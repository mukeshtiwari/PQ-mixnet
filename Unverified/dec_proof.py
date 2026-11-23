#!/usr/bin/env python3
"""
dec_proof.py -- zero-knowledge, non-interactive proof of correct partial decryption for
BGV with additively shared keys (the distributed-decryption step of a mixnet such as
CCS 2023), sublinear in the number of ciphertexts.  Same machinery as mix_proof.py.

Key shares are anchored by public key shares, so no trusted dealer or committed key
shares are needed:   b_j = a s_j + p e_j   with ternary s_j, e_j,   pk = (a, sum_j b_j).

Statement (one decryption server):  a, b in R_q;  first ciphertext components u_i and
    partial decryptions t_i, i < tau.
Witness:  ternary s, e and noise E_i with every coefficient in [-B/2, B/2), B = base^k:
    (K)  b = a s + p e                (the share really is the registered key share)
    (D)  t_i = s u_i + p E_i          (the share was applied, with bounded flooding noise)

The range proof is EXACT (digit decomposition E = sum_d base^d delta_d - B/2 and the zero-
check prod_{v<base} (delta_d - v) = 0 over a field), so there is no soundness slack: the
bound the verifier learns is the bound the honest prover uses.

Linear relations cost no sumcheck at all here: with theta, theta' random,
    sum_{i,x} eq(theta,i) eq(theta',x) [ t_i - s u_i - p E_i ]_x = 0
is one linear claim on the committed rows whose value the verifier computes itself.
"""
from __future__ import annotations
import hashlib, random, time, math
from fp_core import *
from mix_proof import rmul, radd, rsub, rscale, tern, P_PLAIN, unit, gfun, tamper_targets, tampered

class DecStatement:
    def __init__(self, a, b, us, ts): self.a, self.b, self.us, self.ts = a, b, us, ts
    def digest(self) -> bytes:
        h = hashlib.sha256()
        for poly in [self.a, self.b] + list(self.us) + list(self.ts): h.update(b"".join(ser_base(v) for v in poly))
        return h.digest()
class DecWitness:
    def __init__(self, s, e, E): self.s, self.e, self.E = s, e, E

class DecParams:
    def __init__(self, N, tau, base, kdig, C1=None, C2=None, rate_inv=RATE_INV, qbits=128):
        self.N, self.tau, self.base, self.kdig = N, tau, base, kdig
        self.logN, self.ell = log2i(N), log2i(tau); self.m = self.logN + self.ell
        self.off = base ** kdig // 2                                   # E in [-off, off)
        self.dG = sc_degs(self.m, base + 1, 2 * base + 1); self.dT = sc_degs(self.logN, 4, 7)
        self.offG = kdig + 2; self.offT = self.offG + 1 + sum(self.dG)
        self.n_mask = self.offT + 1 + sum(self.dT)
        c2min = 1 << (max(N, 2 * self.n_mask) - 1).bit_length()
        C2 = C2 or c2min; assert C2 >= c2min
        C1 = C1 or dec_best_C1(N, tau, base, kdig, C2, rate_inv, qbits)
        self.C1, self.C2 = C1, C2
        self.tag = f"dec|N={N}|tau={tau}|base={base}|kdig={kdig}|C1={C1}|C2={C2}|rate={rate_inv}|qbits={qbits}|prox={PROX_DIV}".encode()
        rw = self.rw = nrows_for(tau * N, C1)
        self.big = MatParams("big", C1, rate_inv, qbits, [kdig * rw + 6], (kdig * rw + 4, kdig * rw + 5))
        self.maskS1, self.maskS2 = (kdig * rw, kdig * rw + 1), (kdig * rw + 2, kdig * rw + 3)
        # small matrix: s, e, mask table, then random F-rows masking the slots of those three rows and the proximity vector
        self.small = MatParams("small", C2, rate_inv, qbits, [11], (9, 10))
        self.row_s, self.row_e, self.maskrow = 0, 1, 2
        self.maskSs, self.maskSe, self.maskSm = (3, 4), (5, 6), (7, 8)
        self.mps = {"big": self.big, "small": self.small}
        self.data_rows = {"big": list(range(kdig * rw)), "small": [0, 1, 2]}

def dec_size_model(N, tau, base, kdig, C1, C2, rate_inv=RATE_INV, qbits=128):
    logN, ell = log2i(N), log2i(tau); m = logN + ell
    f_elems = 2 + ((base + 1) * (m - 1) + 2 * base + 1) + kdig + (4 * (logN - 1) + 7) + 2 + 1
    k1, n1, q1 = code_params(C1, rate_inv, qbits); k2, n2, q2 = code_params(C2, rate_inv, qbits)
    R1 = kdig * nrows_for(tau * N, C1) + 6
    field = f_elems * 2 * EB + 2 * 32
    opening = 3 * k1 * 2 * EB + 4 * k2 * 2 * EB + q1 * (R1 * EB + SALT + 32 * log2i(n1)) + q2 * (11 * EB + SALT + 32 * log2i(n2))
    return field, opening

def dec_best_C1(N, tau, base, kdig, C2, rate_inv=RATE_INV, qbits=128):
    cands = [1 << l for l in range(1, log2i(tau * N) + 1) if code_params(1 << l, rate_inv, qbits)[1] <= 1 << TWO_ADICITY]
    return min(cands, key=lambda C1: sum(dec_size_model(N, tau, base, kdig, C1, C2, rate_inv, qbits)))

def tshift(vec, e):
    """w[x'] = sum_x e[x] * coeff_x( vec * X^{x'} )  in Z_q[X]/(X^N+1); vec may have Z_q or F entries."""
    N = len(e); out = []
    isf = isinstance(vec[0], tuple)
    for xp in range(N):
        s0 = s1 = 0
        for x in range(N):
            v = vec[x - xp] if x >= xp else vec[N + x - xp]
            sgn = 1 if x >= xp else -1
            if isf:
                pr = fmul(e[x], v); s0 += sgn * pr[0]; s1 += sgn * pr[1]
            else:
                s0 += sgn * e[x][0] * v; s1 += sgn * e[x][1] * v
        out.append((s0 % Q, s1 % Q))
    return out

def dec_derive(par: DecParams, st: DecStatement, proof, ch):
    N, tau, ell, logN, m, base, kd = par.N, par.tau, par.ell, par.logN, par.m, par.base, par.kdig
    for key in ("root_big", "root_small"):
        if not isinstance(proof.get(key), bytes) or len(proof[key]) != 32: raise Reject("malformed root")
    for key, n in (("G", 2), ("evalsG", kd), ("evalsT", 2)): chk_fvec(proof.get(key), n)
    for key, degs in (("scG", par.dG), ("scT", par.dT)):
        msgs = proof.get(key)
        if not isinstance(msgs, list) or len(msgs) != len(degs): raise Reject("malformed sumcheck")
        for ev, d in zip(msgs, degs): chk_fvec(ev, d)
    ch.absorb(b"params", par.tag); ch.absorb(b"stmt", st.digest())
    ch.absorb(b"round1", proof["root_big"] + proof["root_small"] + ser_fs(proof["G"]))
    th = ch.get("theta", "F", ell); th1 = ch.get("theta1", "F", logN); th2 = ch.get("theta2", "F", logN)
    eqt, eq1, eq2 = eq_table(th), eq_table(th1), eq_table(th2)
    # public side of (D) and (K)
    Tcomb = [fsum(fscale(eqt[i], st.ts[i][x]) for i in range(tau)) for x in range(N)]
    Ucomb = [fsum(fscale(eqt[i], st.us[i][x]) for i in range(tau)) for x in range(N)]
    valD = fadd(fdot(eq1, Tcomb), fint(P_PLAIN * par.off))
    w_s = tshift(Ucomb, eq1); w_a = tshift(st.a, eq2)
    valK = fdot_base(eq2, st.b)
    # digit range check
    tz = ch.get("tz", "F", m); kG = ch.get("kG", "F", kd); rhoG = ch.get("rhoG")[0]
    rz, clG = sc_verify(ch, "G", proof["scG"], fmul(rhoG, proof["G"][0]), m, base + 1, 2 * base + 1)
    dz = proof["evalsG"]; ch.absorb(b"evalsG", ser_fs(dz))
    acc = ZERO
    for d in range(kd):
        pr = ONE
        for v in range(base): pr = fmul(pr, fsub(dz[d], fint(v)))
        acc = fadd(acc, fmul(kG[d], pr))
    if rhoG == ZERO: raise Reject("degenerate challenge")
    gvalG = fmul(fsub(clG, fmul(eq_eval(tz, rz), acc)), finv(rhoG))
    # ternary key share
    tt = ch.get("tt", "F", logN); kT = ch.get("kT", "F", 2); rhoT = ch.get("rhoT")[0]
    rt, clT = sc_verify(ch, "T", proof["scT"], fmul(rhoT, proof["G"][1]), logN, 4, 7)
    sz, ez = proof["evalsT"]; ch.absorb(b"evalsT", ser_fs(proof["evalsT"]))
    cube = lambda w: fsub(fmul(fmul(w, w), w), w)
    if rhoT == ZERO: raise Reject("degenerate challenge")
    gvalT = fmul(fsub(clT, fmul(eq_eval(tt, rt), fadd(fmul(kT[0], cube(sz)), fmul(kT[1], cube(ez))))), finv(rhoT))
    # claims
    C1, rw = par.C1, par.rw
    ptD = th1 + th
    slots = {"S1": {"mat": "big", "kind": "tensor", "lovec": lo_vec(ptD, C1, tau * N), "mask": par.maskS1},
             "S2": {"mat": "big", "kind": "tensor", "lovec": lo_vec(rz, C1, tau * N), "mask": par.maskS2},
             "Ss": {"mat": "small", "kind": "func", "mask": par.maskSs},
             "Se": {"mat": "small", "kind": "func", "mask": par.maskSe},
             "Sm": {"mat": "small", "kind": "func", "mask": par.maskSm}}
    hiD, hiz = hi_coefs(ptD, C1, tau * N), hi_coefs(rz, C1, tau * N)
    tab = lambda sid, start, hi, coef: [(sid, start + i, fmul(coef, hi[i]), None) for i in range(len(hi))]
    mr = par.maskrow; Zrz, Zrt = zval(rz), zval(rt); eqrt = eq_table(rt)
    tD = [("Ss", par.row_s, ONE, w_s)]
    for d in range(kd): tD += tab("S1", d * rw, hiD, fint(P_PLAIN * pow(base, d, Q)))
    claims = [(valD, tD),
              (valK, [("Ss", par.row_s, ONE, w_a), ("Se", par.row_e, fint(P_PLAIN), eq2)])]
    for d in range(kd): claims.append((dz[d], tab("S2", d * rw, hiz, ONE) + [("Sm", mr, Zrz, unit(d))]))
    claims.append((sz, [("Ss", par.row_s, ONE, eqrt), ("Sm", mr, Zrt, unit(kd))]))
    claims.append((ez, [("Se", par.row_e, ONE, eqrt), ("Sm", mr, Zrt, unit(kd + 1))]))
    claims.append((gvalG, [("Sm", mr, ONE, gfun(par.offG, SCMask.functional(par.dG, rz)))]))
    claims.append((gvalT, [("Sm", mr, ONE, gfun(par.offT, SCMask.functional(par.dT, rt)))]))
    return slots, claims

def dec_verify(par: DecParams, st: DecStatement, proof, ch=None):
    ch = ch or FSChallenger(b"dec")
    try:
        slots, claims = dec_derive(par, st, proof, ch)
        pcs_open_verify(ch, par.mps, {"big": [proof["root_big"]], "small": [proof["root_small"]]}, slots, claims, proof)
        return True, None
    except Reject as e:
        return False, str(e)

def dec_prove(par: DecParams, st: DecStatement, wit: DecWitness, ch=None, rnd=None, digits=None):
    rnd = rnd or random.SystemRandom()
    ch = Recorder(ch or FSChallenger(b"dec"))
    N, tau, ell, logN, m, base, kd, C1, C2 = par.N, par.tau, par.ell, par.logN, par.m, par.base, par.kdig, par.C1, par.C2
    if digits is None:                                                 # honest digit decomposition of E + off
        digits = [[0] * (tau * N) for _ in range(kd)]
        for i in range(tau):
            for x in range(N):
                v = wit.E[i][x] + par.off
                assert 0 <= v < base ** kd, "noise out of range"
                for d in range(kd): digits[d][x + N * i] = v % base; v //= base
    proof = {}
    big, small = Matrix(par.big, rnd), Matrix(par.small, rnd)
    proof["root_big"] = big.commit([r for T in digits for r in split_rows([x % Q for x in T], C1)]
                                   + [x for _ in range(3) for x in rand_frow(C1, rnd)])
    a_d = [frand(rnd) for _ in range(kd)]; a_s, a_e = frand(rnd), frand(rnd)
    gG, gT = SCMask(par.dG, rnd), SCMask(par.dT, rnd)
    mask_entries = a_d + [a_s, a_e] + gG.entries() + gT.entries(); assert len(mask_entries) == par.n_mask
    s_row = [x % Q for x in wit.s]; e_row = [x % Q for x in wit.e]
    proof["root_small"] = small.commit([s_row, e_row, [v for en in mask_entries for v in en]]
                                       + [x for _ in range(4) for x in rand_frow(C2, rnd)])
    proof["G"] = [gG.total(), gT.total()]
    ch.absorb(b"params", par.tag); ch.absorb(b"stmt", st.digest())
    ch.absorb(b"round1", proof["root_big"] + proof["root_small"] + ser_fs(proof["G"]))
    ch.get("theta", "F", ell); ch.get("theta1", "F", logN); ch.get("theta2", "F", logN)
    tz = ch.get("tz", "F", m); kG = ch.get("kG", "F", kd); rhoG = ch.get("rhoG")[0]
    DF = [[fint(x) for x in T] for T in digits]
    terms = [(kG[d], (0,) + tuple((1 + d, v) for v in range(base))) for d in range(kd)]
    proof["scG"], rz, fin, _ = sc_prove(ch, "G", [eq_table(tz)] + DF, [None] + a_d, terms, ZERO, m, base + 1, 2 * base + 1, gG, rhoG)
    proof["evalsG"] = fin[1:]; ch.absorb(b"evalsG", ser_fs(proof["evalsG"]))
    tt = ch.get("tt", "F", logN); kT = ch.get("kT", "F", 2); rhoT = ch.get("rhoT")[0]
    terms = [(kT[0], (0, 1, 1, 1)), (fneg(kT[0]), (0, 1)), (kT[1], (0, 2, 2, 2)), (fneg(kT[1]), (0, 2))]
    proof["scT"], rt, fin, _ = sc_prove(ch, "T", [eq_table(tt), [fint(x) for x in s_row], [fint(x) for x in e_row]],
                                        [None, a_s, a_e], terms, ZERO, logN, 4, 7, gT, rhoT)
    proof["evalsT"] = fin[1:3]; ch.absorb(b"evalsT", ser_fs(proof["evalsT"]))
    slots, claims = dec_derive(par, st, proof, FixedChallenger(ch.log))
    pcs_open_prove(ch, {"big": big, "small": small}, slots, claims, proof)
    return proof

def dec_draw_challenges(par, st, rnd):
    rc = RandomChallenger(rnd)
    dummy = {"root_big": bytes(32), "root_small": bytes(32), "G": [ZERO] * 2, "evalsG": [ZERO] * par.kdig, "evalsT": [ZERO] * 2,
             "scG": [[ZERO] * d for d in par.dG], "scT": [[ZERO] * d for d in par.dT]}
    _s, claims = dec_derive(par, st, dummy, rc)
    rc.get("pcs.kappa", "F", len(claims)); rc.get("pcs.c")
    for name in sorted(par.mps): rc.get(f"pcs.gamma.{name}", "F", par.mps[name].R)
    for name in sorted(par.mps): rc.get(f"pcs.J.{name}", "I", par.mps[name].nq, par.mps[name].n)
    return rc.log

def dec_simulate(par, st, chal, rnd, coins=None):
    coins = coins or {}
    fr = lambda n: [frand(rnd) for _ in range(n)]
    proof = {"root_big": bytes(32), "root_small": bytes(32), "G": coins.get("G") or fr(2),
             "evalsG": coins.get("evalsG") or fr(par.kdig), "evalsT": coins.get("evalsT") or fr(2),
             "scG": coins.get("scG") or [fr(d) for d in par.dG], "scT": coins.get("scT") or [fr(d) for d in par.dT]}
    slots, claims = dec_derive(par, st, proof, FixedChallenger(chal))
    frag, roots = pcs_open_simulate(chal, par.mps, par.data_rows, slots, claims, coins.get("pcs", {}), rnd)
    proof.update(frag); proof["root_big"] = roots["big"][0]; proof["root_small"] = roots["small"][0]
    return proof

# ------------------------------------------------------------------------------------------
# Byte serialisation. Fields in transcript order; every length follows from the parameters, so there
# are no length prefixes. Z_q elements are 10 bytes big-endian (< q), F elements two of them.
#   root_big | root_small | G (2 F) | scG messages | evalsG (kdig F) | scT messages | evalsT (2 F) | mu
#   | vec S1, S2 (k1 F each), Se, Sm, Ss (k2 F each) | prox big (k1 F) | prox small (k2 F)
#   | nq1 opened big columns: R1 entries, salt, log2 n1 path hashes | nq2 small columns: 11 entries, salt, path
# ------------------------------------------------------------------------------------------
DEC_SLOTS = ("S1", "S2", "Se", "Sm", "Ss")                            # sorted, as absorbed in pcs.vec

def dec_serialize(par: DecParams, proof) -> bytes:
    out = [proof["root_big"], proof["root_small"], ser_fs(proof["G"])]
    out += [ser_fs(ev) for ev in proof["scG"]] + [ser_fs(proof["evalsG"])]
    out += [ser_fs(ev) for ev in proof["scT"]] + [ser_fs(proof["evalsT"]), ser_f(proof["mu"])]
    out += [ser_fs(proof["vec"][sid]) for sid in DEC_SLOTS] + [ser_fs(proof["prox"][n]) for n in ("big", "small")]
    for name in ("big", "small"):
        for per_batch in proof["cols"][name]:
            for item in per_batch:
                out += [b"".join(ser_base(x) for x in item["e"]), item["salt"]] + item["path"]
    return b"".join(out)

def dec_deserialize(par: DecParams, data: bytes):
    pos = 0
    def take(n):
        nonlocal pos
        if pos + n > len(data): raise Reject("proof too short")
        pos += n; return data[pos - n:pos]
    def base():
        v = int.from_bytes(take(EB), "big")
        if v >= Q: raise Reject("malformed field element")
        return v
    f = lambda: (base(), base())
    fs = lambda n: [f() for _ in range(n)]
    p = {"root_big": take(32), "root_small": take(32), "G": fs(2)}
    p["scG"] = [fs(d) for d in par.dG]; p["evalsG"] = fs(par.kdig)
    p["scT"] = [fs(d) for d in par.dT]; p["evalsT"] = fs(2); p["mu"] = f()
    k1, k2 = par.big.k, par.small.k
    p["vec"] = {sid: fs(k1 if sid in ("S1", "S2") else k2) for sid in DEC_SLOTS}
    p["prox"] = {"big": fs(k1), "small": fs(k2)}
    p["cols"] = {}
    for name in ("big", "small"):
        mp = par.mps[name]
        p["cols"][name] = [[{"e": [base() for _ in range(cnt)], "salt": take(SALT), "path": [take(32) for _ in range(log2i(mp.n))]}
                            for cnt in mp.batch_rows] for _ in range(mp.nq)]
    if pos != len(data): raise Reject("trailing bytes")
    return p

def dec_stmt_serialize(st: DecStatement) -> bytes:
    N, tau = len(st.a), len(st.us)
    polys = [st.a, st.b] + list(st.us) + list(st.ts)
    return N.to_bytes(4, "big") + tau.to_bytes(4, "big") + b"".join(ser_base(v) for poly in polys for v in poly)

def dec_stmt_deserialize(data: bytes) -> DecStatement:
    if len(data) < 8: raise Reject("statement too short")
    N, tau = int.from_bytes(data[:4], "big"), int.from_bytes(data[4:8], "big")
    if len(data) != 8 + (2 + 2 * tau) * N * EB: raise Reject("statement: wrong length")
    vals = [int.from_bytes(data[8 + EB * i:8 + EB * (i + 1)], "big") for i in range((2 + 2 * tau) * N)]
    if any(v >= Q for v in vals): raise Reject("statement: entry not reduced")
    polys = [vals[N * i:N * (i + 1)] for i in range(2 + 2 * tau)]
    return DecStatement(polys[0], polys[1], polys[2:2 + tau], polys[2 + tau:])

def dec_verify_bytes(par: DecParams, st_bytes: bytes, proof_bytes: bytes):
    try:
        st = dec_stmt_deserialize(st_bytes)
        if (len(st.a), len(st.us)) != (par.N, par.tau): return False, "statement does not match N, tau"
        return dec_verify(par, st, dec_deserialize(par, proof_bytes))
    except Reject as e:
        return False, str(e)

# ------------------------------------------------------------------------------------------
def keyshare(a, rng):
    N = len(a); s, e = tern(rng, N), tern(rng, N)
    return s, e, radd(rmul(a, s), rscale(e, P_PLAIN))

def partial_decrypt(par, s, us, rng):
    E = [[rng.randrange(-par.off, par.off) for _ in range(par.N)] for _ in us]
    ts = [radd(rmul(s, u), [(P_PLAIN * x) % Q for x in Ei]) for u, Ei in zip(us, E)]
    return E, ts

if __name__ == "__main__":
    N, TAU, BASE, KD, NSERV = 8, 16, 2, 8, 2
    par = DecParams(N, TAU, BASE, KD, C1=64, qbits=24)
    rng = random.Random(3)
    a = [rng.randrange(Q) for _ in range(N)]
    shares = [keyshare(a, rng) for _ in range(NSERV)]
    b = [0] * N
    for (_s, _e, bj) in shares: b = radd(b, bj)
    msgs = [[rng.randrange(P_PLAIN) for _ in range(N)] for _ in range(TAU)]
    cts = []
    for mm in msgs:
        r, e1, e2 = tern(rng, N), tern(rng, N), tern(rng, N)
        cts.append((radd(rmul(a, r), rscale(e1, P_PLAIN)), radd(radd(rmul(b, r), rscale(e2, P_PLAIN)), mm)))
    us = [c[0] for c in cts]
    print(f"N = {N}, tau = {TAU}, {NSERV} decryption servers, noise in [-{par.off}, {par.off}) as {KD} base-{BASE} digits; "
          f"big rows {par.big.R} x {par.big.k}, small rows {par.small.R} x {par.small.k}")

    print("1. honest distributed decryption: every server proves its shares, the combiner checks and decrypts")
    all_ts = []; keep = None
    for j, (s, e, bj) in enumerate(shares):
        E, ts = partial_decrypt(par, s, us, rng)
        st = DecStatement(a, bj, us, ts)
        t0 = time.time(); pf = dec_prove(par, st, DecWitness(s, e, E)); t1 = time.time()
        ok, why = dec_verify(par, st, pf); t2 = time.time(); assert ok, why
        assert sum(dec_size_model(N, TAU, BASE, KD, par.C1, par.C2, RATE_INV, 24)) == proof_size(pf)
        all_ts.append(ts)
        if j == 0: keep = (st, DecWitness(s, e, E), pf)
        print(f"   server {j}: accepted; prove {t1-t0:.1f}s, verify {t2-t1:.1f}s; proof {proof_size(pf)/1024:.1f} KiB; size model exact")
    out = []
    for i in range(TAU):
        d = cts[i][1]
        for ts in all_ts: d = rsub(d, ts[i])
        out.append([((x if x <= Q // 2 else x - Q) % P_PLAIN) for x in d])
    assert out == msgs
    print("   combined shares decrypt every ciphertext correctly")

    st, wit, pf = keep; s, e, bj = shares[0]
    print("2. cheating decryption servers")
    ts2 = [t[:] for t in st.ts]; ts2[0][0] = (ts2[0][0] + 1) % Q                      # flips a plaintext bit
    st2 = DecStatement(a, bj, us, ts2)
    ok, why = dec_verify(par, st2, dec_prove(par, st2, wit)); print(f"   share changed by +1 (plaintext flipped): {why}"); assert not ok
    # noise outside the range, digits made to satisfy the linear relation: top digit = base
    E3 = [row[:] for row in wit.E]; E3[2][1] = par.off + 5
    ts3 = [radd(rmul(s, u), [(P_PLAIN * x) % Q for x in Ei]) for u, Ei in zip(us, E3)]
    dig3 = [[0] * (TAU * N) for _ in range(KD)]
    for i in range(TAU):
        for x in range(N):
            v = E3[i][x] + par.off
            top = v // BASE ** (KD - 1); v -= top * BASE ** (KD - 1)
            for d in range(KD - 1): dig3[d][x + N * i] = v % BASE; v //= BASE
            dig3[KD - 1][x + N * i] = top
    st3 = DecStatement(a, bj, us, ts3)
    ok, why = dec_verify(par, st3, dec_prove(par, st3, DecWitness(s, e, E3), digits=dig3))
    print(f"   noise out of range, linear relations satisfied: {why}"); assert not ok
    s4, e4, _b4 = keyshare(a, rng)                                                   # a different key
    E4, ts4 = partial_decrypt(par, s4, us, rng); st4 = DecStatement(a, bj, us, ts4)
    ok, why = dec_verify(par, st4, dec_prove(par, st4, DecWitness(s4, e4, E4))); print(f"   shares made with another key: {why}"); assert not ok
    s5 = [rng.randrange(Q) for _ in range(N)]                                         # non-short 'key' explaining b
    e5 = rscale(rsub(bj, rmul(a, s5)), pow(P_PLAIN, Q - 2, Q))
    assert radd(rmul(a, s5), rscale(e5, P_PLAIN)) == bj
    E5, ts5 = partial_decrypt(par, s5, us, rng); st5 = DecStatement(a, bj, us, ts5)
    ok, why = dec_verify(par, st5, dec_prove(par, st5, DecWitness(s5, e5, E5)))
    print(f"   non-short key satisfying b = a s + p e exactly: {why}"); assert not ok
    ok, why = dec_verify(par, st2, pf); assert not ok

    print("3. tampering with a valid proof")
    leaves = list(tamper_targets(pf)); rr = random.Random(5); by_key = {}
    for p in leaves: by_key.setdefault(p[0], []).append(p)
    picks = [rr.choice(v) for v in by_key.values()] + [rr.choice(leaves) for _ in range(50 - len(by_key))]
    for p in picks:
        ok, why = dec_verify(par, st, tampered(pf, p)); assert not ok, p
    print(f"   {len(picks)} tampered proofs, all rejected")

    print("4. honest-verifier simulator")
    chal = dec_draw_challenges(par, st, random.SystemRandom())
    ok, why = dec_verify(par, st, dec_simulate(par, st, chal, random.SystemRandom()), FixedChallenger(chal)); assert ok, why
    real = dec_prove(par, st, wit, ch=FixedChallenger(chal))
    ok, why = dec_verify(par, st, real, FixedChallenger(chal)); assert ok, why
    coins = {k: real[k] for k in ("G", "evalsG", "evalsT", "scG", "scT")}
    coins["pcs"] = pcs_free_values(par.mps, par.data_rows, real)
    rep = dec_simulate(par, st, chal, random.SystemRandom(), coins=coins)
    same = all(rep[k] == real[k] for k in ("G", "scG", "scT", "evalsG", "evalsT", "mu", "vec", "prox")) and all(
        x["e"] == y["e"] for name in par.mps for qa, qb in zip(rep["cols"][name], real["cols"][name]) for x, y in zip(qa, qb))
    assert same
    print("   simulated transcript (no witness) accepted; simulator reproduces a real transcript from its free values")

    print("5. base-4 digits and 128-bit query parameters")
    par4 = DecParams(16, 32, 4, 5)
    a16 = [rng.randrange(Q) for _ in range(16)]; s16, e16, b16 = keyshare(a16, rng)
    us16 = [[rng.randrange(Q) for _ in range(16)] for _ in range(32)]
    E16, ts16 = partial_decrypt(par4, s16, us16, rng); st16 = DecStatement(a16, b16, us16, ts16)
    t0 = time.time(); pf16 = dec_prove(par4, st16, DecWitness(s16, e16, E16)); t1 = time.time()
    ok, why = dec_verify(par4, st16, pf16); assert ok, why
    assert sum(dec_size_model(16, 32, 4, 5, par4.C1, par4.C2)) == proof_size(pf16)
    print(f"   accepted; proof {proof_size(pf16)/1024:.0f} KiB, model exact, prove {t1-t0:.1f}s")

    print("6. byte format")
    for (pp, stt, pff) in ((par, st, pf), (par4, st16, pf16)):
        blob = dec_serialize(pp, pff); sblob = dec_stmt_serialize(stt)
        assert len(blob) == proof_size(pff) == sum(dec_size_model(pp.N, pp.tau, pp.base, pp.kdig, pp.C1, pp.C2, RATE_INV,
                                                                  24 if pp is par else 128))
        assert dec_serialize(pp, dec_deserialize(pp, blob)) == blob and dec_stmt_deserialize(sblob).digest() == stt.digest()
        ok, why = dec_verify_bytes(pp, sblob, blob); assert ok, why
        rb = random.Random(len(blob))
        for _ in range(20):
            b2 = bytearray(blob); b2[rb.randrange(len(b2))] ^= 1 << rb.randrange(8)
            assert not dec_verify_bytes(pp, sblob, bytes(b2))[0]
        assert not dec_verify_bytes(pp, sblob, blob[:-1])[0] and not dec_verify_bytes(pp, sblob, blob + b"\0")[0]
        s2 = bytearray(sblob); s2[-1] ^= 1
        assert not dec_verify_bytes(pp, bytes(s2), blob)[0]
    over = bytearray(dec_serialize(par, pf)); over[64:64 + EB] = (Q).to_bytes(EB, "big")       # an entry equal to q
    assert not dec_verify_bytes(par, dec_stmt_serialize(st), bytes(over))[0]
    print(f"   round trip exact, length = size model; 40 bit flips, truncation, extension, a changed statement and an unreduced entry rejected")

    print("\nall checks passed\n")
    print("Extrapolation (N = 4096, 128-bit query parameters); CCS 2023 needs noise up to 2^54, i.e. a range of 2^55:")
    print(f"   {'ballots':>8} {'digits':>12} {'sumcheck part':>14} {'opening':>10} {'per ballot':>11}   vs CCS 2023 decryption proof (117 KB/ballot)")
    for lt in (13, 20):
        for base, kd in ((2, 55), (4, 28)):
            t_ = 1 << lt; p_ = DecParams(4096, t_, base, kd)
            f_b, o_b = dec_size_model(4096, t_, base, kd, p_.C1, p_.C2)
            print(f"   {'2^'+str(lt):>8} {str(kd)+' base-'+str(base):>12} {f_b/1024:11.1f} KiB {o_b/2**20:7.1f} MiB {(f_b+o_b)/t_:8.0f} B   "
                  f"{117*1024*t_/(f_b+o_b):6.0f}x smaller")
