#!/usr/bin/env python3
"""
fp_core.py -- shared machinery for the field-projection proofs for BGV mixnets
(mix_proof.py: proof of shuffle;  dec_proof.py: proof of correct partial decryption).

Contents
  * Z_q and F = GF(q^2)                         (q: 78-bit prime, q = 1 mod 2^24)
  * challengers: Fiat-Shamir, random (interactive honest verifier), fixed (replay)
  * multilinear-extension helpers
  * zero-knowledge sumcheck: round messages masked by a committed random polynomial
    (Chiesa-Forbes-Spooner style); committed tables masked off the Boolean cube by
    a * Z(x), Z(x) = prod_i x_i (1 - x_i), so that the one evaluation revealed per
    table is uniformly distributed
  * zero-knowledge encode-then-hash commitment: Reed-Solomon rows with random pads,
    salted Merkle tree over columns, and a Sigma-protocol opening of LINEAR claims
        sum_rows coef_row * <row, lovec>  =  value
    in which every vector sent is masked by a committed random row.

Nothing here is specific to the mixnet; the two protocol files build claims and call
pcs_open_prove / pcs_open_verify.  Reference implementation: clarity over speed.
"""
from __future__ import annotations
import hashlib, math, os, random
from typing import Dict, List, Sequence, Tuple

# ------------------------------------------------------------------------------------------
# Fields
# ------------------------------------------------------------------------------------------
Q = 302231454903657394339841            # ~2^78, prime, Q = 1 mod 2^24
TWO_ADICITY = 24
NR = 3                                   # quadratic non-residue: F = Z_q[t]/(t^2 - NR)
ROOT = pow(NR, (Q - 1) >> TWO_ADICITY, Q)
EB = 10                                  # bytes per Z_q element on the wire
SALT = 16                                # bytes of salt per Merkle leaf
# Proximity regime of the row code (environment variable FP_PROX_DIV, bound into every transcript):
#   3  e = floor((d-1)/3): elementary lemma for arbitrary linear codes (Roth-Zemor, in Ligero), false-witness prob. (e+1)/|F|
#   2  e = floor((d-1)/2): unique-decoding radius, needs the Reed-Solomon proximity gap of BCIKS20, Thm 1.6 (n/|F|)
PROX_DIV = int(os.environ.get("FP_PROX_DIV", "3"))
assert PROX_DIV in (2, 3)
# Inverse code rate (environment variable FP_RATE_INV, bound into every transcript).  Rate 1/2 halves the
# encoding and hashing work; with PROX_DIV = 2 it needs the same number of queries as rate 1/4 with PROX_DIV = 3.
RATE_INV = int(os.environ.get("FP_RATE_INV", "4"))
assert RATE_INV in (2, 4, 8, 16)
assert pow(NR, (Q - 1) // 2, Q) == Q - 1 and pow(ROOT, 1 << (TWO_ADICITY - 1), Q) == Q - 1

Fe = Tuple[int, int]
ZERO: Fe = (0, 0)
ONE: Fe = (1, 0)
TGEN: Fe = (0, 1)

def fint(c: int) -> Fe: return (c % Q, 0)
def fadd(x, y): return ((x[0] + y[0]) % Q, (x[1] + y[1]) % Q)
def fsub(x, y): return ((x[0] - y[0]) % Q, (x[1] - y[1]) % Q)
def fneg(x): return ((-x[0]) % Q, (-x[1]) % Q)
def fmul(x, y):
    a, b = x; c, d = y
    return ((a * c + NR * b * d) % Q, (a * d + b * c) % Q)
def fscale(x, c: int): return (x[0] * c % Q, x[1] * c % Q)
def finv(x):
    a, b = x
    d = pow((a * a - NR * b * b) % Q, Q - 2, Q)
    return (a * d % Q, (-b) * d % Q)
def fsum(xs):
    s0 = s1 = 0
    for a, b in xs: s0 += a; s1 += b
    return (s0 % Q, s1 % Q)
def fdot(xs, ys): return fsum(fmul(a, b) for a, b in zip(xs, ys))
def fdot_base(fs, bs):
    s0 = s1 = 0
    for (a, b), c in zip(fs, bs):
        if c: s0 += a * c; s1 += b * c
    return (s0 % Q, s1 % Q)
def fbatch_inv(xs: List[Fe]) -> List[Fe]:
    pref = [ONE]
    for x in xs: pref.append(fmul(pref[-1], x))
    inv = finv(pref[-1]); out = [ZERO] * len(xs)
    for i in range(len(xs) - 1, -1, -1):
        out[i] = fmul(inv, pref[i]); inv = fmul(inv, xs[i])
    return out
def frand(rnd) -> Fe: return (rnd.randrange(Q), rnd.randrange(Q))

def log2i(n: int) -> int:
    assert n > 0 and n & (n - 1) == 0, n
    return n.bit_length() - 1

def ser_base(x: int) -> bytes: return x.to_bytes(EB, "big")
def ser_f(x: Fe) -> bytes: return x[0].to_bytes(EB, "big") + x[1].to_bytes(EB, "big")
def ser_fs(xs) -> bytes: return b"".join(ser_f(x) for x in xs)
def H(b: bytes) -> bytes: return hashlib.sha256(b).digest()

# ------------------------------------------------------------------------------------------
# Challengers.  Every challenge has a name; prover and verifier ask for the same names in
# the same order.  'F': n field elements;  'I': n distinct indices below `bound` (a power of 2).
# ------------------------------------------------------------------------------------------
class Reject(Exception): pass

class FSChallenger:
    """Fiat-Shamir: challenges are SHA-256 outputs of everything absorbed so far."""
    def __init__(self, domain: bytes):
        self.state = H(b"FP-BGV-v2|" + domain); self._buf = b""; self._ctr = 0
    def absorb(self, label: bytes, data: bytes):
        self.state = H(self.state + b"|A|" + label + b"|" + H(data)); self._buf = b""; self._ctr = 0
    def _bytes(self, k: int) -> bytes:
        while len(self._buf) < k:
            self._buf += H(self.state + b"|S|" + self._ctr.to_bytes(8, "big")); self._ctr += 1
        out, self._buf = self._buf[:k], self._buf[k:]
        return out
    def _base(self) -> int:                               # rejection sampling: unbiased
        while True:
            v = int.from_bytes(self._bytes(EB), "big") & ((1 << 79) - 1)
            if v < Q: return v
    def get(self, name: str, kind: str = "F", n: int = 1, bound: int = 0):
        self.state = H(self.state + b"|C|" + name.encode()); self._buf = b""; self._ctr = 0
        if kind == "F": return [(self._base(), self._base()) for _ in range(n)]
        out, seen = [], set()
        while len(out) < n:
            v = int.from_bytes(self._bytes(4), "big") & (bound - 1)
            if v not in seen: seen.add(v); out.append(v)
        return out

class RandomChallenger:
    """Interactive honest verifier: fresh uniform challenges, recorded by name."""
    def __init__(self, rnd=None): self.rnd = rnd or random.SystemRandom(); self.log: Dict[str, list] = {}
    def absorb(self, label, data): pass
    def get(self, name, kind="F", n=1, bound=0):
        v = [frand(self.rnd) for _ in range(n)] if kind == "F" else self.rnd.sample(range(bound), n)
        self.log[name] = v
        return v

class FixedChallenger:
    """Replays given challenges (used by the prover to re-derive claims, and by the simulator tests)."""
    def __init__(self, chal: Dict[str, list]): self.chal = chal
    def absorb(self, label, data): pass
    def get(self, name, kind="F", n=1, bound=0):
        v = self.chal[name]
        if len(v) != n: raise Reject(f"challenge {name}: expected {n}, have {len(v)}")
        return v

class Recorder:
    """Wraps a challenger and remembers what it answered."""
    def __init__(self, inner): self.inner = inner; self.log: Dict[str, list] = {}
    def absorb(self, label, data): self.inner.absorb(label, data)
    def get(self, name, kind="F", n=1, bound=0):
        v = self.inner.get(name, kind, n, bound); self.log[name] = v
        return v

# ------------------------------------------------------------------------------------------
# Multilinear extensions (variable 0 = least significant index bit)
# ------------------------------------------------------------------------------------------
def eq_table(r: Sequence[Fe]) -> List[Fe]:
    tbl = [ONE]
    for rk in r:
        om = fsub(ONE, rk)
        tbl = [fmul(x, om) for x in tbl] + [fmul(x, rk) for x in tbl]
    return tbl

def eq_eval(r, s) -> Fe:
    acc = ONE
    for a, b in zip(r, s):
        acc = fmul(acc, fadd(fmul(a, b), fmul(fsub(ONE, a), fsub(ONE, b))))
    return acc

def fold(table: List[Fe], r: Fe) -> List[Fe]:
    r0, r1 = r; out = []
    for i in range(0, len(table), 2):
        a0, a1 = table[i]; b0, b1 = table[i + 1]
        d0 = b0 - a0; d1 = b1 - a1
        out.append(((a0 + r0 * d0 + NR * r1 * d1) % Q, (a1 + r0 * d1 + r1 * d0) % Q))
    return out

def mle(table, r) -> Fe:
    assert len(table) == 1 << len(r)
    t = list(table)
    for rk in r: t = fold(t, rk)
    return t[0]

def zval(r) -> Fe:
    """Z(r) = prod_i r_i (1 - r_i): vanishes on the Boolean cube."""
    acc = ONE
    for x in r: acc = fmul(acc, fmul(x, fsub(ONE, x)))
    return acc

_LAG: Dict[int, List[int]] = {}
def interp(vals: List[Fe], r: Fe) -> Fe:
    """Lagrange interpolation through x = 0..d, evaluated at r."""
    d = len(vals) - 1
    if d not in _LAG:
        _LAG[d] = [pow(math.prod((i - j) for j in range(d + 1) if j != i) % Q, Q - 2, Q) for i in range(d + 1)]
    diffs = [fsub(r, fint(j)) for j in range(d + 1)]
    acc = ZERO
    for i, v in enumerate(vals):
        num = ONE
        for j in range(d + 1):
            if j != i: num = fmul(num, diffs[j])
        acc = fadd(acc, fmul(v, fscale(num, _LAG[d][i])))
    return acc

# ------------------------------------------------------------------------------------------
# Zero-knowledge sumcheck
# ------------------------------------------------------------------------------------------
class SCMask:
    """Random g(x) = a0 + sum_j sum_{t=1..degs[j]} c[j][t-1] x_j^t  (committed by the prover)."""
    def __init__(self, degs: List[int], rnd):
        self.degs = degs; self.a0 = frand(rnd)
        self.c = [[frand(rnd) for _ in range(d)] for d in degs]
    def entries(self) -> List[Fe]: return [self.a0] + [x for row in self.c for x in row]
    def total(self) -> Fe:                                 # sum over the Boolean cube
        m = len(self.degs)
        s = fsum(x for row in self.c for x in row)
        return fadd(fscale(self.a0, pow(2, m, Q)), fscale(s, pow(2, m - 1, Q)))
    def _uni(self, j: int, x: Fe) -> Fe:
        acc, p = ZERO, ONE
        for cf in self.c[j]:
            p = fmul(p, x); acc = fadd(acc, fmul(cf, p))
        return acc
    def round_evals(self, j: int, pref: List[Fe]) -> List[Fe]:
        m = len(self.degs); rem = m - j - 1
        base = fadd(self.a0, fsum(self._uni(i, pref[i]) for i in range(j)))
        tail = fsum(x for i in range(j + 1, m) for x in self.c[i])
        out = []
        for cpt in range(self.degs[j] + 1):
            v = fscale(fadd(base, self._uni(j, fint(cpt))), pow(2, rem, Q))
            if rem >= 1: v = fadd(v, fscale(tail, pow(2, rem - 1, Q)))
            out.append(v)
        return out
    @staticmethod
    def functional(degs: List[int], r: List[Fe]) -> List[Fe]:
        """Coefficients, aligned with entries(), of the linear map  entries -> g(r)."""
        out = [ONE]
        for j, d in enumerate(degs):
            p = ONE
            for _ in range(d):
                p = fmul(p, r[j]); out.append(p)
        return out

def sc_degs(m: int, deg: int, deg_last: int) -> List[int]: return [deg] * (m - 1) + [deg_last]

def sc_prove(ch, name: str, tables: List[List[Fe]], tmask, terms, claim: Fe, m: int,
             deg: int, deg_last: int, g: SCMask, rho_g: Fe):
    """Sumcheck for  sum_x sum_terms coef * prod_factors T(x) = claim, with
         * each table T extended off the cube as T~(x) + tmask[T] * Z(x)   (tmask entry None = no mask),
         * round polynomials masked by rho_g * g.
       A factor is a table index, or (index, shift) meaning T(x) - shift.
       Sends, per round, the evaluations at 0, 2, 3, .., d (the value at 1 is implied by the running claim).
       Returns (messages, point, masked final value of every table, final running claim)."""
    assert all(len(t) == 1 << m for t in tables) and m >= 1
    tables = [list(t) for t in tables]
    point: List[Fe] = []; msgs = []; finals = None
    claim = fadd(claim, fmul(rho_g, g.total()))
    for j in range(m):
        last = (j == m - 1); d = deg_last if last else deg
        acc0 = [0] * (d + 1); acc1 = [0] * (d + 1)
        if not last:
            half = len(tables[0]) >> 1
            for i in range(half):
                ev = []
                for t in tables:
                    a0, a1 = t[2 * i]; b0, b1 = t[2 * i + 1]
                    d0 = b0 - a0; d1 = b1 - a1
                    row = [(a0, a1)]
                    for _ in range(d):
                        a0 += d0; a1 += d1
                        row.append((a0 % Q, a1 % Q))
                    ev.append(row)
                for c in range(d + 1):
                    for coef, facs in terms:
                        p = coef
                        for fa in facs:
                            if isinstance(fa, tuple): v = ev[fa[0]][c]; p = fmul(p, ((v[0] - fa[1]) % Q, v[1]))
                            else: p = fmul(p, ev[fa][c])
                        acc0[c] += p[0]; acc1[c] += p[1]
        else:                                               # two entries left: the off-cube masks show up here
            zprev = zval(point)
            def uni(idx, x: Fe) -> Fe:
                t0, t1 = tables[idx]
                v = fadd(t0, fmul(x, fsub(t1, t0)))
                if tmask[idx] is not None:
                    v = fadd(v, fmul(fmul(tmask[idx], zprev), fmul(x, fsub(ONE, x))))
                return v
            for c in range(d + 1):
                x = fint(c); cache = {}
                for coef, facs in terms:
                    p = coef
                    for fa in facs:
                        idx, sh = (fa if isinstance(fa, tuple) else (fa, 0))
                        if idx not in cache: cache[idx] = uni(idx, x)
                        v = cache[idx]; p = fmul(p, ((v[0] - sh) % Q, v[1]))
                    acc0[c] += p[0]; acc1[c] += p[1]
        gv = g.round_evals(j, point)
        vals = [fadd((acc0[c] % Q, acc1[c] % Q), fmul(rho_g, gv[c])) for c in range(d + 1)]
        send = [vals[0]] + vals[2:]
        msgs.append(send); ch.absorb(f"{name}.m{j}".encode(), ser_fs(send))
        r = ch.get(f"{name}.r{j}")[0]; point.append(r)
        claim = interp([vals[0], fsub(claim, vals[0])] + vals[2:], r)     # as the verifier will compute it
        if not last: tables = [fold(t, r) for t in tables]
        else: finals = [uni(idx, r) for idx in range(len(tables))]
    return msgs, point, finals, claim

def sc_verify(ch, name: str, msgs, claim: Fe, m: int, deg: int, deg_last: int):
    """Returns (point, final running claim).  The caller checks the final claim."""
    if not isinstance(msgs, list) or len(msgs) != m: raise Reject(f"{name}: wrong number of rounds")
    point = []
    for j in range(m):
        d = deg_last if j == m - 1 else deg
        ev = msgs[j]
        if not isinstance(ev, list) or len(ev) != d: raise Reject(f"{name}: round {j} has the wrong length")
        ch.absorb(f"{name}.m{j}".encode(), ser_fs(ev))
        r = ch.get(f"{name}.r{j}")[0]; point.append(r)
        claim = interp([ev[0], fsub(claim, ev[0])] + ev[1:], r)
    return point, claim

# ------------------------------------------------------------------------------------------
# Reed-Solomon / Merkle
# ------------------------------------------------------------------------------------------
def ntt(a: List[int], w: int) -> List[int]:
    n = len(a); a = a[:]
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit: j ^= bit; bit >>= 1
        j |= bit
        if i < j: a[i], a[j] = a[j], a[i]
    length = 2
    while length <= n:
        wl = pow(w, n // length, Q); half = length >> 1
        for i in range(0, n, length):
            x = 1
            for k in range(i, i + half):
                u = a[k]; v = a[k + half] * x % Q
                a[k] = (u + v) % Q; a[k + half] = (u - v) % Q
                x = x * wl % Q
        length <<= 1
    return a

def merkle_build(leaves: List[bytes]) -> List[List[bytes]]:
    layers = [leaves]
    while len(layers[-1]) > 1:
        p = layers[-1]
        layers.append([H(p[i] + p[i + 1]) for i in range(0, len(p), 2)])
    return layers
def merkle_path(layers, j: int) -> List[bytes]:
    path = []
    for lay in layers[:-1]:
        path.append(lay[j ^ 1]); j >>= 1
    return path
def merkle_root_from(leaf: bytes, j: int, path: List[bytes]) -> bytes:
    h = leaf
    for sib in path:
        h = H(h + sib) if j & 1 == 0 else H(sib + h)
        j >>= 1
    return h
def leaf_hash(salt: bytes, entries: Sequence[int]) -> bytes:
    return H(salt + b"".join(ser_base(x) for x in entries))

def code_params(C: int, rate_inv: int, qbits: int):
    """Row code for C data symbols:  message length k = C + nq  (nq random pads, one per column
       query, so that opened columns are uniform), length n = rate_inv*C (doubled while k > 2n/rate_inv).
       nq column queries give 2^-qbits for the interleaved proximity test at distance
       e = floor((d-1)/PROX_DIV), d = n-k+1  (per-query miss probability 1 - e/n)."""
    n = rate_inv * C; nq = 1
    while True:
        k = C + nq
        while (rate_inv // 2) * k > n or n - k < PROX_DIV: n *= 2
        e = (n - k) // PROX_DIV
        need = math.ceil(qbits / -math.log2(1 - e / n))
        if need <= nq: return k, n, nq
        nq = need

class MatParams:
    """Public description of one committed matrix: row code and number of rows per batch."""
    def __init__(self, name: str, C: int, rate_inv: int, qbits: int, batch_rows: List[int], prox_mask):
        self.name, self.C = name, C
        self.k, self.n, self.nq = code_params(C, rate_inv, qbits)
        assert self.n <= 1 << TWO_ADICITY
        self.w = pow(ROOT, (1 << TWO_ADICITY) // self.n, Q)
        self.batch_rows = batch_rows                      # rows committed in each batch, in order
        self.R = sum(batch_rows)
        self.prox_mask = prox_mask                        # (row, row): committed random F-row masking the proximity vector
    def encode_ext(self, u: List[Fe]):
        pad = [0] * (self.n - len(u))
        return ntt([x[0] for x in u] + pad, self.w), ntt([x[1] for x in u] + pad, self.w)

class Matrix:
    """Prover side of a committed matrix."""
    def __init__(self, mp: MatParams, rnd):
        self.mp, self.rnd = mp, rnd
        self.msgs: List[List[int]] = []; self.enc: List[List[int]] = []; self.batches = []
    def commit(self, rows: List[List[int]]) -> bytes:
        mp = self.mp; b = len(self.batches)
        assert len(rows) == mp.batch_rows[b], (mp.name, b, len(rows), mp.batch_rows[b])
        start = len(self.msgs)
        for r in rows:
            assert len(r) <= mp.C
            msg = [x % Q for x in r] + [0] * (mp.C - len(r)) + [self.rnd.randrange(Q) for _ in range(mp.nq)]
            self.msgs.append(msg); self.enc.append(ntt(msg + [0] * (mp.n - mp.k), mp.w))
        salts = [self.rnd.randbytes(SALT) for _ in range(mp.n)]
        cols = range(start, start + len(rows))
        tree = merkle_build([leaf_hash(salts[j], [self.enc[i][j] for i in cols]) for j in range(mp.n)])
        self.batches.append((start, len(rows), salts, tree))
        return tree[-1][0]
    def frow(self, pair) -> List[Fe]:
        return list(zip(self.msgs[pair[0]], self.msgs[pair[1]]))
    def comb(self, coef: Dict[int, Fe]) -> List[Fe]:
        k = self.mp.k; o0 = [0] * k; o1 = [0] * k
        for ridx, (c0, c1) in coef.items():
            for x, v in enumerate(self.msgs[ridx]):
                if v: o0[x] += c0 * v; o1[x] += c1 * v
        return [(a % Q, b % Q) for a, b in zip(o0, o1)]

def rand_frow(C: int, rnd) -> List[List[int]]:
    """A uniformly random F-valued row, stored as two Z_q rows."""
    return [[rnd.randrange(Q) for _ in range(C)], [rnd.randrange(Q) for _ in range(C)]]

# ------------------------------------------------------------------------------------------
# Opening of linear claims.
#   slot:  {'mat': name, 'kind': 'tensor'|'func', 'lovec': [Fe]*C (tensor only), 'mask': (row,row)}
#          tensor: many rows share one lo-vector;  func: one row, the lo-vector is assembled from the terms
#   claim: (value, [(slot id, row, coef, lv)])   lv = None for tensor slots; for func slots a list or
#          a {position: Fe} dict giving the functional on that row
#   Claimed relation:  sum_terms coef * <row, lovec or lv>  =  value.
# ------------------------------------------------------------------------------------------
def _slots_compile(mps: Dict[str, MatParams], slots, claims, kap):
    rowcoef = {sid: {} for sid in slots}
    L = {sid: (list(s["lovec"]) if s["kind"] == "tensor" else [ZERO] * mps[s["mat"]].C) for sid, s in slots.items()}
    V = ZERO
    for (value, terms), kc in zip(claims, kap):
        V = fadd(V, fmul(kc, value))
        for (sid, row, coef, lv) in terms:
            kcoef = fmul(kc, coef)
            if slots[sid]["kind"] == "tensor":
                rowcoef[sid][row] = fadd(rowcoef[sid].get(row, ZERO), kcoef)
            else:
                rowcoef[sid][row] = ONE
                assert len(rowcoef[sid]) == 1, "a func slot lives on a single row"
                Ls = L[sid]
                for pos, c in (lv.items() if isinstance(lv, dict) else enumerate(lv)):
                    Ls[pos] = fadd(Ls[pos], fmul(kcoef, c))
    for sid, s in slots.items(): assert len(L[sid]) == mps[s["mat"]].C
    return rowcoef, L, V

def pcs_open_prove(ch, mats: Dict[str, Matrix], slots, claims, proof):
    mps = {name: M.mp for name, M in mats.items()}
    kap = ch.get("pcs.kappa", "F", len(claims))
    rowcoef, L, _V = _slots_compile(mps, slots, claims, kap)
    us, ms, mu = {}, {}, ZERO
    for sid in sorted(slots):
        M = mats[slots[sid]["mat"]]
        us[sid] = M.comb(rowcoef[sid]); ms[sid] = M.frow(slots[sid]["mask"])
        mu = fadd(mu, fdot(ms[sid][:M.mp.C], L[sid]))
    proof["mu"] = mu; ch.absorb(b"pcs.mu", ser_f(mu))
    c = ch.get("pcs.c")[0]
    proof["vec"] = {sid: [fadd(a, fmul(c, b)) for a, b in zip(ms[sid], us[sid])] for sid in sorted(slots)}
    proof["prox"] = {}
    for name in sorted(mats):
        M = mats[name]; gam = ch.get(f"pcs.gamma.{name}", "F", M.mp.R)
        comb = M.comb({i: gam[i] for i in range(M.mp.R) if i not in M.mp.prox_mask})
        proof["prox"][name] = [fadd(a, b) for a, b in zip(M.frow(M.mp.prox_mask), comb)]
    ch.absorb(b"pcs.vec", b"".join(ser_fs(proof["vec"][s]) for s in sorted(slots))
              + b"".join(ser_fs(proof["prox"][n]) for n in sorted(mats)))
    proof["cols"] = {}
    for name in sorted(mats):
        M = mats[name]; J = ch.get(f"pcs.J.{name}", "I", M.mp.nq, M.mp.n)
        proof["cols"][name] = [[{"e": [M.enc[i][j] for i in range(start, start + cnt)], "salt": salts[j],
                                 "path": merkle_path(tree, j)} for (start, cnt, salts, tree) in M.batches] for j in J]

def pcs_open_verify(ch, mps: Dict[str, MatParams], roots: Dict[str, List[bytes]], slots, claims, proof) -> None:
    """Raises Reject unless every claim is accepted."""
    kap = ch.get("pcs.kappa", "F", len(claims))
    rowcoef, L, V = _slots_compile(mps, slots, claims, kap)
    mu = chk_f(proof.get("mu")); ch.absorb(b"pcs.mu", ser_f(mu))
    c = ch.get("pcs.c")[0]
    vec, prox = proof.get("vec"), proof.get("prox")
    if not isinstance(vec, dict) or set(vec) != set(slots) or not isinstance(prox, dict) or set(prox) != set(mps):
        raise Reject("opening: wrong set of vectors")
    for sid in slots: chk_fvec(vec[sid], mps[slots[sid]["mat"]].k)
    gam = {}
    for name in sorted(mps):
        chk_fvec(prox[name], mps[name].k); gam[name] = ch.get(f"pcs.gamma.{name}", "F", mps[name].R)
    ch.absorb(b"pcs.vec", b"".join(ser_fs(vec[s]) for s in sorted(slots)) + b"".join(ser_fs(prox[n]) for n in sorted(mps)))
    # the single Sigma-protocol equation over all slots
    lhs = fsum(fdot(vec[sid][:mps[slots[sid]["mat"]].C], L[sid]) for sid in slots)
    if lhs != fadd(mu, fmul(c, V)): raise Reject("opening: claimed values")
    cols = proof.get("cols")
    if not isinstance(cols, dict) or set(cols) != set(mps): raise Reject("opening: columns")
    for name in sorted(mps):
        mp = mps[name]; J = ch.get(f"pcs.J.{name}", "I", mp.nq, mp.n)
        enc_prox = mp.encode_ext(prox[name])
        enc_vec = {sid: mp.encode_ext(vec[sid]) for sid in slots if slots[sid]["mat"] == name}
        if not isinstance(cols[name], list) or len(cols[name]) != mp.nq: raise Reject("opening: number of columns")
        for j, per_batch in zip(J, cols[name]):
            if not isinstance(per_batch, list) or len(per_batch) != len(mp.batch_rows): raise Reject("opening: batches")
            col: List[int] = []
            for b, item in enumerate(per_batch):
                e, salt, path = item.get("e"), item.get("salt"), item.get("path")
                if (not isinstance(e, list) or len(e) != mp.batch_rows[b]
                        or any(not isinstance(x, int) or not 0 <= x < Q for x in e)
                        or not isinstance(salt, bytes) or len(salt) != SALT
                        or not isinstance(path, list) or len(path) != log2i(mp.n)
                        or any(not isinstance(hh, bytes) or len(hh) != 32 for hh in path)):
                    raise Reject("opening: malformed column")
                if merkle_root_from(leaf_hash(salt, e), j, path) != roots[name][b]: raise Reject("opening: Merkle path")
                col += e
            pm = mp.prox_mask
            s0 = col[pm[0]]; s1 = col[pm[1]]
            for i, (g0, g1) in enumerate(gam[name]):
                if i not in pm: s0 += g0 * col[i]; s1 += g1 * col[i]
            if (s0 % Q, s1 % Q) != (enc_prox[0][j], enc_prox[1][j]): raise Reject("opening: proximity vector")
            for sid, enc in enc_vec.items():
                ma, mb = slots[sid]["mask"]; s0 = s1 = 0
                for ridx, (c0, c1) in rowcoef[sid].items():
                    s0 += c0 * col[ridx]; s1 += c1 * col[ridx]
                comb = fmul(c, (s0 % Q, s1 % Q))
                if ((col[ma] + comb[0]) % Q, (col[mb] + comb[1]) % Q) != (enc[0][j], enc[1][j]):
                    raise Reject("opening: combination vector")

def pcs_open_simulate(chal, mps: Dict[str, MatParams], data_rows: Dict[str, List[int]], slots, claims, coins, rnd):
    """Honest-verifier simulator for the opening.  `chal` holds all challenges; `coins` may fix the
       free values  vec, prox, cols[name][q][row] for data rows, salts  (missing ones are sampled).
       Returns (proof fragment, roots).  Uses no witness: only the claims' public values."""
    kap = chal["pcs.kappa"]; c = chal["pcs.c"][0]
    rowcoef, L, V = _slots_compile(mps, slots, claims, kap)
    out = {"vec": {}, "prox": {}, "cols": {}}
    for sid in sorted(slots):
        k = mps[slots[sid]["mat"]].k
        out["vec"][sid] = coins.get("vec", {}).get(sid) or [frand(rnd) for _ in range(k)]
    lhs = fsum(fdot(out["vec"][sid][:mps[slots[sid]["mat"]].C], L[sid]) for sid in slots)
    out["mu"] = fsub(lhs, fmul(c, V))
    roots = {}
    for name in sorted(mps):
        mp = mps[name]; J = chal[f"pcs.J.{name}"]; gam = chal[f"pcs.gamma.{name}"]
        out["prox"][name] = coins.get("prox", {}).get(name) or [frand(rnd) for _ in range(mp.k)]
        enc_prox = mp.encode_ext(out["prox"][name])
        enc_vec = {sid: mp.encode_ext(out["vec"][sid]) for sid in slots if slots[sid]["mat"] == name}
        full = [[rnd.randrange(Q) for _ in range(mp.R)] for _ in range(mp.n)]       # columns; unopened ones stay random
        for qi, j in enumerate(J):
            col = full[j]
            given = coins.get("cols", {}).get(name)
            for i in data_rows[name]:
                if given is not None: col[i] = given[qi][i]
            for sid, enc in enc_vec.items():                                         # solve the slot mask rows
                ma, mb = slots[sid]["mask"]; s0 = s1 = 0
                for ridx, (c0, c1) in rowcoef[sid].items():
                    s0 += c0 * col[ridx]; s1 += c1 * col[ridx]
                comb = fmul(c, (s0 % Q, s1 % Q))
                col[ma] = (enc[0][j] - comb[0]) % Q; col[mb] = (enc[1][j] - comb[1]) % Q
            pm = mp.prox_mask; s0 = s1 = 0                                           # then the proximity mask row
            for i, (g0, g1) in enumerate(gam):
                if i not in pm: s0 += g0 * col[i]; s1 += g1 * col[i]
            col[pm[0]] = (enc_prox[0][j] - s0) % Q; col[pm[1]] = (enc_prox[1][j] - s1) % Q
        roots[name] = []; trees = []; start = 0
        for b, cnt in enumerate(mp.batch_rows):
            given_salts = coins.get("salts", {}).get(name)
            salts = [rnd.randbytes(SALT) for _ in range(mp.n)]
            if given_salts is not None:
                for qi, j in enumerate(J): salts[j] = given_salts[qi][b]
            tree = merkle_build([leaf_hash(salts[j], full[j][start:start + cnt]) for j in range(mp.n)])
            trees.append((start, cnt, salts, tree)); roots[name].append(tree[-1][0]); start += cnt
        out["cols"][name] = [[{"e": full[j][st:st + cnt], "salt": salts[j], "path": merkle_path(tree, j)}
                              for (st, cnt, salts, tree) in trees] for j in J]
    return out, roots

def pcs_free_values(mps: Dict[str, "MatParams"], data_rows: Dict[str, List[int]], proof):
    """Free values of the opening: everything pcs_open_simulate samples."""
    cols = {}; salts = {}
    for name in mps:
        cols[name] = []; salts[name] = []
        for per_batch in proof["cols"][name]:
            col = [x for item in per_batch for x in item["e"]]
            cols[name].append({i: col[i] for i in data_rows[name]})
            salts[name].append([item["salt"] for item in per_batch])
    return {"vec": proof["vec"], "prox": proof["prox"], "cols": cols, "salts": salts}

def chk_f(x) -> Fe:
    if not (isinstance(x, tuple) and len(x) == 2 and all(isinstance(v, int) and 0 <= v < Q for v in x)):
        raise Reject("malformed field element")
    return x
def chk_fvec(xs, n: int):
    if not isinstance(xs, list) or len(xs) != n: raise Reject("malformed vector")
    for x in xs: chk_f(x)

# ------------------------------------------------------------------------------------------
# Layout helpers for tables stored in rows of length C
# ------------------------------------------------------------------------------------------
def split_rows(table: List[int], C: int) -> List[List[int]]:
    if len(table) <= C: return [list(table)]
    assert len(table) % C == 0
    return [table[i:i + C] for i in range(0, len(table), C)]
def nrows_for(tab_len: int, C: int) -> int: return 1 if tab_len <= C else tab_len // C
def lo_vec(pt: List[Fe], C: int, tab_len: int) -> List[Fe]:
    """Lo-vector for an MLE evaluation at pt of a table of tab_len entries laid out in rows of C."""
    if tab_len >= C: return eq_table(pt[:log2i(C)])
    return eq_table(pt) + [ZERO] * (C - tab_len)
def hi_coefs(pt: List[Fe], C: int, tab_len: int) -> List[Fe]:
    return eq_table(pt[log2i(C):]) if tab_len > C else [ONE]

def proof_size(obj) -> int:
    """Bytes on the wire: 10 per Z_q element, 20 per F element, hashes and salts as they are."""
    if isinstance(obj, tuple) and len(obj) == 2 and all(isinstance(v, int) for v in obj): return 2 * EB
    if isinstance(obj, bool): return 0
    if isinstance(obj, int): return EB
    if isinstance(obj, bytes): return len(obj)
    if isinstance(obj, dict): return sum(proof_size(v) for v in obj.values())
    if isinstance(obj, (list, tuple)): return sum(proof_size(v) for v in obj)
    raise TypeError(type(obj))
