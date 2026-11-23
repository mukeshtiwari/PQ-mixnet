#!/usr/bin/env python3
"""
mix_proof.py -- zero-knowledge, non-interactive proof of shuffle for BGV re-randomisation
mixnets (the relation of Aranha-Baum-Gjosteen-Silde, CCS 2023), sublinear in the number
of ciphertexts.  Reference implementation in pure Python on top of fp_core.py.

Statement (one mix server):  pk = (a, b) in R_q^2, R_q = Z_q[X]/(X^N+1), q = 1 mod 2N;
    inputs c_i = (u_i, v_i), outputs chat_j, i, j < tau.
Witness:  sigma in S_tau and ternary r_i, e1_i, e2_i with
    chat_j = c_{sigma(j)} + (a r + p e1, b r + p e2)_{sigma(j)}.

Protocol (all algebra over F = GF(q^2); R_q's ring structure is never used):
  1. commit  W_r, W_e1, W_e2 (tau x N, ternary)  and  sigma (tau)                       [round 1]
  2. challenges rho in F^{2N}, alpha, beta;   z_i = <rho, coeff(c_i)> + <rho M_pk, w_i>,
     zhat_j = <rho, coeff(chat_j)>,  h_i = z_i + beta*i - alpha,  hhat_j = zhat_j + beta*sigma_j - alpha
  3. commit  u = 1/h, uhat = 1/hhat  and all masks                                       [round 2]
  4. sumcheck A (log-derivative permutation argument):
        sum_x  eq(tc,x) [k1 u h + k2 uhat hhat] + k3 (u - uhat)  =  k1 + k2
     i.e. u = 1/h, uhat = 1/hhat on the cube and  sum_i 1/h_i = sum_j 1/hhat_j,  which over a
     field forces {(z_i, i)} = {(zhat_j, sigma_j)} as multisets.  Nothing about sigma's range
     has to be proven, and no product is ever revealed.
  5. sumcheck B: reduces the virtual polynomial h at the point of A to the committed W.
  6. sumcheck C: exact shortness  w^3 - w = 0.
  7. one zero-knowledge opening of nine linear claims on the committed rows.

Zero-knowledge: see fp_core.py.  mix_simulate() is the honest-verifier simulator; the tests
check that it is accepted and that it reproduces real transcripts from their free values.
"""
from __future__ import annotations
import hashlib, random, sys, time, math
from fp_core import *

P_PLAIN = 2

# ------------------------------------------------------------------------------------------
# Toy BGV over R_q = Z_q[X]/(X^N + 1)
# ------------------------------------------------------------------------------------------
def rmul(a, b):
    N = len(a); res = [0] * N
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                k = i + j
                if k < N: res[k] += x * y
                else: res[k - N] -= x * y
    return [v % Q for v in res]
def radd(a, b): return [(x + y) % Q for x, y in zip(a, b)]
def rsub(a, b): return [(x - y) % Q for x, y in zip(a, b)]
def rscale(a, c): return [x * c % Q for x in a]
def tern(rng, N): return [rng.choice((-1, 0, 1)) % Q for _ in range(N)]
def slot_roots(N):
    z = pow(ROOT, (1 << TWO_ADICITY) // (2 * N), Q)
    return [pow(z, 2 * k + 1, Q) for k in range(N)]
def to_slots(x, roots): return [sum(c * pow(r, j, Q) for j, c in enumerate(x)) % Q for r in roots]
def from_slots(s, roots):
    N = len(s); ninv = pow(N, Q - 2, Q)
    return [ninv * sum(sk * pow(r, -j, Q) for sk, r in zip(s, roots)) % Q for j in range(N)]

class BGV:
    def __init__(self, N, rng):
        self.N = N
        self.a = [rng.randrange(Q) for _ in range(N)]
        self.s = tern(rng, N); self.e = tern(rng, N)
        self.b = radd(rmul(self.a, self.s), rscale(self.e, P_PLAIN))
    def enc(self, m, rng):
        r, e1, e2 = tern(rng, self.N), tern(rng, self.N), tern(rng, self.N)
        return (radd(rmul(self.a, r), rscale(e1, P_PLAIN)), radd(radd(rmul(self.b, r), rscale(e2, P_PLAIN)), m))
    def rerand_term(self, r, e1, e2):
        return (radd(rmul(self.a, r), rscale(e1, P_PLAIN)), radd(rmul(self.b, r), rscale(e2, P_PLAIN)))
    def dec(self, c):
        d = rsub(c[1], rmul(self.s, c[0]))
        return tuple(((x if x <= Q // 2 else x - Q) % P_PLAIN) for x in d)

class Instance:
    def __init__(self, a, b, cin, cout): self.a, self.b, self.cin, self.cout = a, b, cin, cout
    def digest(self) -> bytes:
        h = hashlib.sha256()
        for poly in [self.a, self.b] + [x for c in self.cin for x in c] + [x for c in self.cout for x in c]:
            h.update(b"".join(ser_base(v) for v in poly))
        return h.digest()
class Witness:
    def __init__(self, sigma, r, e1, e2): self.sigma, self.r, self.e1, self.e2 = sigma, r, e1, e2

# ------------------------------------------------------------------------------------------
# Parameters and layout
# ------------------------------------------------------------------------------------------
class MixParams:
    def __init__(self, N, tau, C1=None, C2=None, rate_inv=RATE_INV, qbits=128):
        self.N, self.tau, self.rate_inv, self.qbits = N, tau, rate_inv, qbits
        self.logN, self.ell = log2i(N), log2i(tau); self.m = self.logN + self.ell
        assert self.logN >= 1 and self.ell >= 1
        self.dA, self.dB, self.dC = sc_degs(self.ell, 3, 5), sc_degs(self.logN, 2, 2), sc_degs(self.m, 4, 7)
        # mask table (F entries): a_u, a_uhat, a_sigma, a_h, a_w0..2, then the three sumcheck masks
        self.offA = 7; self.offB = self.offA + 1 + sum(self.dA); self.offC = self.offB + 1 + sum(self.dB)
        self.n_mask = self.offC + 1 + sum(self.dC)
        if C1 is None or C2 is None:
            b1, b2 = best_C(N, tau, rate_inv, qbits)
            C1, C2 = C1 or b1, C2 or b2
        assert 2 * self.n_mask <= C2, "small matrix rows must hold the mask table"
        self.C1, self.C2 = C1, C2
        self.tag = f"mix|N={N}|tau={tau}|C1={C1}|C2={C2}|rate={rate_inv}|qbits={qbits}|prox={PROX_DIV}".encode()
        rw = self.rw = nrows_for(tau * N, C1); rs = self.rs = nrows_for(tau, C2)
        # big matrix: W_r, W_e1, W_e2, then three random F-rows (masks of slots S1, S2 and of the proximity vector)
        self.big = MatParams("big", C1, rate_inv, qbits, [3 * rw + 6], (3 * rw + 4, 3 * rw + 5))
        self.maskS1, self.maskS2 = (3 * rw, 3 * rw + 1), (3 * rw + 2, 3 * rw + 3)
        # small matrix, batch 1: sigma, masks of S3, S4, proximity;  batch 2: u (2 tables), uhat (2), mask table
        c1 = rs + 6
        self.small = MatParams("small", C2, rate_inv, qbits, [c1, 4 * rs + 1], (rs + 4, rs + 5))
        self.maskS3, self.maskS4 = (rs, rs + 1), (rs + 2, rs + 3)
        self.row_u = [c1, c1 + rs, c1 + 2 * rs, c1 + 3 * rs]; self.maskrow = c1 + 4 * rs
        self.mps = {"big": self.big, "small": self.small}
        self.data_rows = {"big": list(range(3 * rw)),
                          "small": list(range(rs)) + list(range(c1, c1 + 4 * rs + 1))}

def mix_size_model(N, tau, C1, C2, rate_inv=RATE_INV, qbits=128):
    """Exact proof size in bytes as a function of the parameters (checked against real proofs in the tests)."""
    logN, ell = log2i(N), log2i(tau); m = logN + ell
    f_elems = 3 + (3 * (ell - 1) + 5) + 4 + 2 * logN + (4 * (m - 1) + 7) + 3 + 1
    k1, n1, q1 = code_params(C1, rate_inv, qbits); k2, n2, q2 = code_params(C2, rate_inv, qbits)
    R1 = 3 * nrows_for(tau * N, C1) + 6; R2 = 5 * nrows_for(tau, C2) + 7
    field = f_elems * 2 * EB + 3 * 32
    vecs = 3 * k1 * 2 * EB + 3 * k2 * 2 * EB
    cols = q1 * (R1 * EB + SALT + 32 * log2i(n1)) + q2 * (R2 * EB + 2 * (SALT + 32 * log2i(n2)))
    return field, vecs + cols

def best_C(N, tau, rate_inv=RATE_INV, qbits=128):
    n_mask = 7 + 3 + 3 * (log2i(tau) - 1) + 5 + 2 * log2i(N) + 4 * (log2i(N) + log2i(tau) - 1) + 7
    c2min = 1 << (2 * n_mask - 1).bit_length()
    best = None
    for l1 in range(1, log2i(tau * N) + 1):
        for l2 in range(log2i(c2min), max(log2i(c2min), log2i(tau)) + 3):
            if max(code_params(1 << l1, rate_inv, qbits)[1], code_params(1 << l2, rate_inv, qbits)[1]) > 1 << TWO_ADICITY: continue
            s = sum(mix_size_model(N, tau, 1 << l1, 1 << l2, rate_inv, qbits))
            if best is None or s < best[0]: best = (s, 1 << l1, 1 << l2)
    return best[1], best[2]

def unit(e: int) -> dict: return {2 * e: ONE, 2 * e + 1: TGEN}
def gfun(off: int, coefs) -> dict:
    out = {}
    for i, c in enumerate(coefs): out[2 * (off + i)] = c; out[2 * (off + i) + 1] = fmul(c, TGEN)
    return out

def public_projection(inst: Instance, rho_u, rho_v):
    """Everything the verifier computes from the statement: projections and rho' = rho . M_pk."""
    N = len(inst.a)
    proj = lambda c: fadd(fdot_base(rho_u, c[0]), fdot_base(rho_v, c[1]))
    zpub = [proj(c) for c in inst.cin]; zhat = [proj(c) for c in inst.cout]
    def shift(a, y): return [(a[x - y] if x >= y else -a[N + x - y]) % Q for x in range(N)]
    rp = [[fadd(fdot_base(rho_u, shift(inst.a, y)), fdot_base(rho_v, shift(inst.b, y))) for y in range(N)],
          [fscale(x, P_PLAIN) for x in rho_u], [fscale(x, P_PLAIN) for x in rho_v]]
    return zpub, zhat, rp

# ------------------------------------------------------------------------------------------
# Verifier logic shared by verifier, prover (to restate its claims) and simulator
# ------------------------------------------------------------------------------------------
def mix_derive(par: MixParams, inst: Instance, proof, ch):
    """Replays the public-coin part: returns (slots, claims) for the final opening.  Raises Reject."""
    N, tau, ell, logN, m = par.N, par.tau, par.ell, par.logN, par.m
    for key in ("root_big", "root_s1", "root_s2"):
        if not isinstance(proof.get(key), bytes) or len(proof[key]) != 32: raise Reject("malformed root")
    for key, n in (("G", 3), ("evalsA", 4), ("evalsC", 3)): chk_fvec(proof.get(key), n)
    for key, degs in (("A", par.dA), ("B", par.dB), ("C", par.dC)):
        msgs = proof.get(key)
        if not isinstance(msgs, list) or len(msgs) != len(degs): raise Reject("malformed sumcheck")
        for ev, d in zip(msgs, degs): chk_fvec(ev, d)
    ch.absorb(b"params", par.tag); ch.absorb(b"stmt", inst.digest()); ch.absorb(b"round1", proof["root_big"] + proof["root_s1"])
    rho_u = ch.get("rho_u", "F", N); rho_v = ch.get("rho_v", "F", N); alpha, beta = ch.get("ab", "F", 2)
    zpub, zhat, rp = public_projection(inst, rho_u, rho_v)
    GA, GB, GC = proof["G"]
    ch.absorb(b"round2", proof["root_s2"] + ser_fs(proof["G"]))
    # --- sumcheck A
    tc = ch.get("tc", "F", ell); k1, k2, k3 = ch.get("kA", "F", 3); rhoA = ch.get("rhoA")[0]
    r, clA = sc_verify(ch, "A", proof["A"], fadd(fadd(k1, k2), fmul(rhoA, GA)), ell, 3, 5)
    U, Uh, s_val, Hd = proof["evalsA"]; ch.absorb(b"evalsA", ser_fs(proof["evalsA"]))
    Hh = fsub(fadd(mle(zhat, r), fmul(beta, s_val)), alpha)
    fA = fadd(fmul(eq_eval(tc, r), fadd(fmul(k1, fmul(U, Hd)), fmul(k2, fmul(Uh, Hh)))), fmul(k3, fsub(U, Uh)))
    if rhoA == ZERO: raise Reject("degenerate challenge")
    gvalA = fmul(fsub(clA, fA), finv(rhoA))
    # --- sumcheck B
    rhoB = ch.get("rhoB")[0]
    idr = fsum(fscale(r[bq], 1 << bq) for bq in range(ell))
    Sp = fadd(fsub(fsub(Hd, mle(zpub, r)), fmul(beta, idr)), alpha)
    ry, clB = sc_verify(ch, "B", proof["B"], fadd(Sp, fmul(rhoB, GB)), logN, 2, 2)
    # --- sumcheck C
    tz = ch.get("tz", "F", m); kC = ch.get("kC", "F", 3); rhoC = ch.get("rhoC")[0]
    rz, clC = sc_verify(ch, "C", proof["C"], fmul(rhoC, GC), m, 4, 7)
    wz = proof["evalsC"]; ch.absorb(b"evalsC", ser_fs(wz))
    fC = fmul(eq_eval(tz, rz), fsum(fmul(kC[k], fsub(fmul(fmul(wz[k], wz[k]), wz[k]), wz[k])) for k in range(3)))
    if rhoC == ZERO: raise Reject("degenerate challenge")
    gvalC = fmul(fsub(clC, fC), finv(rhoC))
    # --- the nine linear claims
    C1, C2, rw, rs = par.C1, par.C2, par.rw, par.rs
    Zr, Zrz = zval(r), zval(rz); ptB = ry + r
    slots = {"S1": {"mat": "big", "kind": "tensor", "lovec": lo_vec(ptB, C1, tau * N), "mask": par.maskS1},
             "S2": {"mat": "big", "kind": "tensor", "lovec": lo_vec(rz, C1, tau * N), "mask": par.maskS2},
             "S3": {"mat": "small", "kind": "tensor", "lovec": lo_vec(r, C2, tau), "mask": par.maskS3},
             "S4": {"mat": "small", "kind": "func", "mask": par.maskS4}}
    hiB, hiz, hir = hi_coefs(ptB, C1, tau * N), hi_coefs(rz, C1, tau * N), hi_coefs(r, C2, tau)
    mr = par.maskrow
    tab = lambda sid, start, hi, coef: [(sid, start + i, fmul(coef, hi[i]), None) for i in range(len(hi))]
    ru = par.row_u
    claims = [(U, tab("S3", ru[0], hir, ONE) + tab("S3", ru[1], hir, TGEN) + [("S4", mr, Zr, unit(0))]),
              (Uh, tab("S3", ru[2], hir, ONE) + tab("S3", ru[3], hir, TGEN) + [("S4", mr, Zr, unit(1))]),
              (s_val, tab("S3", 0, hir, ONE) + [("S4", mr, Zr, unit(2))])]
    tB = []
    for k in range(3): tB += tab("S1", k * rw, hiB, mle(rp[k], ry))
    tB += [("S4", mr, fscale(Zr, pow(N, Q - 2, Q)), unit(3)),
           ("S4", mr, rhoB, gfun(par.offB, SCMask.functional(par.dB, ry)))]
    claims.append((clB, tB))
    for k in range(3): claims.append((wz[k], tab("S2", k * rw, hiz, ONE) + [("S4", mr, Zrz, unit(4 + k))]))
    claims.append((gvalA, [("S4", mr, ONE, gfun(par.offA, SCMask.functional(par.dA, r)))]))
    claims.append((gvalC, [("S4", mr, ONE, gfun(par.offC, SCMask.functional(par.dC, rz)))]))
    return slots, claims

def mix_verify(par: MixParams, inst: Instance, proof, ch=None):
    """Returns (True, None) or (False, reason)."""
    ch = ch or FSChallenger(b"mix")
    try:
        slots, claims = mix_derive(par, inst, proof, ch)
        pcs_open_verify(ch, par.mps, {"big": [proof["root_big"]], "small": [proof["root_s1"], proof["root_s2"]]},
                        slots, claims, proof)
        return True, None
    except Reject as e:
        return False, str(e)

# ------------------------------------------------------------------------------------------
# Prover
# ------------------------------------------------------------------------------------------
def mix_prove(par: MixParams, inst: Instance, wit: Witness, ch=None, rnd=None):
    rnd = rnd or random.SystemRandom()
    ch = Recorder(ch or FSChallenger(b"mix"))
    N, tau, ell, logN, m, C1, C2 = par.N, par.tau, par.ell, par.logN, par.m, par.C1, par.C2
    proof = {}
    Wk = [[row[y] % Q for row in tbl for y in range(N)] for tbl in (wit.r, wit.e1, wit.e2)]     # index y + N*i
    sig = [s % Q for s in wit.sigma]
    big, small = Matrix(par.big, rnd), Matrix(par.small, rnd)
    proof["root_big"] = big.commit([r for T in Wk for r in split_rows(T, C1)] + [x for _ in range(3) for x in rand_frow(C1, rnd)])
    proof["root_s1"] = small.commit(split_rows(sig, C2) + [x for _ in range(3) for x in rand_frow(C2, rnd)])
    ch.absorb(b"params", par.tag); ch.absorb(b"stmt", inst.digest()); ch.absorb(b"round1", proof["root_big"] + proof["root_s1"])
    rho_u = ch.get("rho_u", "F", N); rho_v = ch.get("rho_v", "F", N); alpha, beta = ch.get("ab", "F", 2)
    zpub, zhat, rp = public_projection(inst, rho_u, rho_v)
    h, hh = [], []
    for i in range(tau):
        z = zpub[i]
        for k in range(3): z = fadd(z, fdot_base(rp[k], Wk[k][N * i:N * (i + 1)]))
        h.append(fsub(fadd(z, fscale(beta, i)), alpha))
        hh.append(fsub(fadd(zhat[i], fscale(beta, sig[i])), alpha))
    if ZERO in h or ZERO in hh: raise ArithmeticError("a denominator vanished (probability ~ 2 tau / |F|): re-run")
    u, uh = fbatch_inv(h), fbatch_inv(hh)
    a_u, a_uh, a_sig, a_h, a_w0, a_w1, a_w2 = [frand(rnd) for _ in range(7)]
    gA, gB, gC = SCMask(par.dA, rnd), SCMask(par.dB, rnd), SCMask(par.dC, rnd)
    mask_entries = [a_u, a_uh, a_sig, a_h, a_w0, a_w1, a_w2] + gA.entries() + gB.entries() + gC.entries()
    assert len(mask_entries) == par.n_mask
    mask_row = [v for e in mask_entries for v in e]
    proof["root_s2"] = small.commit(split_rows([x[0] for x in u], C2) + split_rows([x[1] for x in u], C2)
                                    + split_rows([x[0] for x in uh], C2) + split_rows([x[1] for x in uh], C2) + [mask_row])
    proof["G"] = [gA.total(), gB.total(), gC.total()]
    ch.absorb(b"round2", proof["root_s2"] + ser_fs(proof["G"]))
    # --- sumcheck A
    tc = ch.get("tc", "F", ell); k1, k2, k3 = ch.get("kA", "F", 3); rhoA = ch.get("rhoA")[0]
    proof["A"], r, fin, _ = sc_prove(ch, "A", [eq_table(tc), u, h, uh, hh], [None, a_u, a_h, a_uh, fmul(beta, a_sig)],
                                     [(k1, (0, 1, 2)), (k2, (0, 3, 4)), (k3, (1,)), (fneg(k3), (3,))],
                                     fadd(k1, k2), ell, 3, 5, gA, rhoA)
    Zr = zval(r)
    s_val = fadd(mle([fint(x) for x in sig], r), fmul(a_sig, Zr))
    proof["evalsA"] = [fin[1], fin[3], s_val, fin[2]]                    # u(r), uhat(r), sigma(r), h(r), all masked
    ch.absorb(b"evalsA", ser_fs(proof["evalsA"]))
    # --- sumcheck B
    rhoB = ch.get("rhoB")[0]
    eqr = eq_table(r)
    Wp = [[fsum(fscale(eqr[i], Wk[k][y + N * i]) for i in range(tau)) for y in range(N)] for k in range(3)]
    const = fscale(fmul(a_h, Zr), pow(N, Q - 2, Q))
    idr = fsum(fscale(r[bq], 1 << bq) for bq in range(ell))
    Sp = fadd(fsub(fsub(fin[2], mle(zpub, r)), fmul(beta, idr)), alpha)
    proof["B"], ry, _, _ = sc_prove(ch, "B", rp + Wp + [[const] * N], [None] * 7,
                                    [(ONE, (0, 3)), (ONE, (1, 4)), (ONE, (2, 5)), (ONE, (6,))], Sp, logN, 2, 2, gB, rhoB)
    # --- sumcheck C
    tz = ch.get("tz", "F", m); kC = ch.get("kC", "F", 3); rhoC = ch.get("rhoC")[0]
    WF = [[fint(x) for x in T] for T in Wk]
    terms = [(kC[k], (0, 1 + k, 1 + k, 1 + k)) for k in range(3)] + [(fneg(kC[k]), (0, 1 + k)) for k in range(3)]
    proof["C"], rz, fin, _ = sc_prove(ch, "C", [eq_table(tz)] + WF, [None, a_w0, a_w1, a_w2], terms, ZERO, m, 4, 7, gC, rhoC)
    proof["evalsC"] = fin[1:4]; ch.absorb(b"evalsC", ser_fs(proof["evalsC"]))
    # --- restate the claims exactly as the verifier will, then open them
    slots, claims = mix_derive(par, inst, proof, FixedChallenger(ch.log))
    pcs_open_prove(ch, {"big": big, "small": small}, slots, claims, proof)
    return proof

# ------------------------------------------------------------------------------------------
# Honest-verifier simulator (no witness)
# ------------------------------------------------------------------------------------------
def mix_draw_challenges(par: MixParams, inst: Instance, rnd):
    """All verifier challenges of one interactive execution, sampled up front."""
    rc = RandomChallenger(rnd)
    dummy = {"root_big": bytes(32), "root_s1": bytes(32), "root_s2": bytes(32), "G": [ZERO] * 3,
             "evalsA": [ZERO] * 4, "evalsC": [ZERO] * 3,
             "A": [[ZERO] * d for d in par.dA], "B": [[ZERO] * d for d in par.dB], "C": [[ZERO] * d for d in par.dC]}
    _slots, claims = mix_derive(par, inst, dummy, rc)
    rc.get("pcs.kappa", "F", len(claims)); rc.get("pcs.c")
    for name in sorted(par.mps): rc.get(f"pcs.gamma.{name}", "F", par.mps[name].R)
    for name in sorted(par.mps): rc.get(f"pcs.J.{name}", "I", par.mps[name].nq, par.mps[name].n)
    return rc.log

def mix_simulate(par: MixParams, inst: Instance, chal, rnd, coins=None):
    """Produces an accepting transcript for the given challenges from uniformly random 'free values'.
       coins (optional) fixes those free values; it never contains anything derived from a witness here."""
    coins = coins or {}
    fr = lambda n: [frand(rnd) for _ in range(n)]
    proof = {"root_big": bytes(32), "root_s1": bytes(32), "root_s2": bytes(32)}
    proof["G"] = coins.get("G") or fr(3)
    proof["evalsA"] = coins.get("evalsA") or fr(4)
    proof["evalsC"] = coins.get("evalsC") or fr(3)
    for key, degs in (("A", par.dA), ("B", par.dB), ("C", par.dC)):
        proof[key] = coins.get(key) or [fr(d) for d in degs]
    slots, claims = mix_derive(par, inst, proof, FixedChallenger(chal))
    frag, roots = pcs_open_simulate(chal, par.mps, par.data_rows, slots, claims, coins.get("pcs", {}), rnd)
    proof.update(frag)
    proof["root_big"] = roots["big"][0]; proof["root_s1"], proof["root_s2"] = roots["small"]
    return proof

def free_values(par: MixParams, proof):
    """The free values of a transcript: everything the simulator samples."""
    return {"G": proof["G"], "evalsA": proof["evalsA"], "evalsC": proof["evalsC"],
            "A": proof["A"], "B": proof["B"], "C": proof["C"],
            "pcs": pcs_free_values(par.mps, par.data_rows, proof)}

# ------------------------------------------------------------------------------------------
# Byte serialisation (the format the native implementation reads and writes)
# ------------------------------------------------------------------------------------------
def mix_serialize(par: MixParams, proof) -> bytes:
    out = [proof["root_big"], proof["root_s1"], proof["root_s2"], ser_fs(proof["G"])]
    out += [ser_fs(ev) for ev in proof["A"]] + [ser_fs(proof["evalsA"])]
    out += [ser_fs(ev) for ev in proof["B"]] + [ser_fs(ev) for ev in proof["C"]] + [ser_fs(proof["evalsC"]), ser_f(proof["mu"])]
    out += [ser_fs(proof["vec"][s]) for s in ("S1", "S2", "S3", "S4")] + [ser_fs(proof["prox"][n]) for n in ("big", "small")]
    for name in ("big", "small"):
        for per_batch in proof["cols"][name]:
            for item in per_batch:
                out += [b"".join(ser_base(x) for x in item["e"]), item["salt"]] + item["path"]
    return b"".join(out)

def mix_deserialize(par: MixParams, data: bytes):
    pos = 0
    def take(n):
        nonlocal pos
        if pos + n > len(data): raise Reject("proof too short")
        pos += n; return data[pos - n:pos]
    base = lambda: int.from_bytes(take(EB), "big")
    f = lambda: (base(), base())
    fs = lambda n: [f() for _ in range(n)]
    p = {"root_big": take(32), "root_s1": take(32), "root_s2": take(32), "G": fs(3)}
    p["A"] = [fs(d) for d in par.dA]; p["evalsA"] = fs(4)
    p["B"] = [fs(d) for d in par.dB]; p["C"] = [fs(d) for d in par.dC]; p["evalsC"] = fs(3); p["mu"] = f()
    p["vec"] = {"S1": fs(par.big.k), "S2": fs(par.big.k), "S3": fs(par.small.k), "S4": fs(par.small.k)}
    p["prox"] = {"big": fs(par.big.k), "small": fs(par.small.k)}
    p["cols"] = {}
    for name in ("big", "small"):
        mp = par.mps[name]
        p["cols"][name] = [[{"e": [base() for _ in range(cnt)], "salt": take(SALT), "path": [take(32) for _ in range(log2i(mp.n))]}
                            for cnt in mp.batch_rows] for _ in range(mp.nq)]
    if pos != len(data): raise Reject("trailing bytes")
    return p

def inst_serialize(inst: Instance) -> bytes:
    N, tau = len(inst.a), len(inst.cin)
    polys = [inst.a, inst.b] + [x for c in inst.cin for x in c] + [x for c in inst.cout for x in c]
    return N.to_bytes(4, "big") + tau.to_bytes(4, "big") + b"".join(ser_base(v) for poly in polys for v in poly)

def inst_deserialize(data: bytes) -> Instance:
    N, tau = int.from_bytes(data[:4], "big"), int.from_bytes(data[4:8], "big")
    assert len(data) == 8 + (2 + 4 * tau) * N * EB
    pos = 8
    def poly():
        nonlocal pos
        out = [int.from_bytes(data[pos + EB * i:pos + EB * (i + 1)], "big") for i in range(N)]; pos += EB * N
        return out
    a, b = poly(), poly()
    cin = [(poly(), poly()) for _ in range(tau)]; cout = [(poly(), poly()) for _ in range(tau)]
    return Instance(a, b, cin, cout)

# ------------------------------------------------------------------------------------------
# Instances
# ------------------------------------------------------------------------------------------
def make_instance(tau, N, seed=1):
    rng = random.Random(seed)
    bgv = BGV(N, rng)
    msgs = [[rng.randrange(P_PLAIN) for _ in range(N)] for _ in range(tau)]
    cin = [bgv.enc(mm, rng) for mm in msgs]
    sigma = list(range(tau)); rng.shuffle(sigma)
    wit = Witness(sigma, [tern(rng, N) for _ in range(tau)], [tern(rng, N) for _ in range(tau)], [tern(rng, N) for _ in range(tau)])
    return bgv, msgs, Instance(bgv.a, bgv.b, cin, outputs(bgv, cin, wit)), wit

def outputs(bgv, cin, wit):
    out = []
    for j in range(len(cin)):
        i = wit.sigma[j]; t = bgv.rerand_term(wit.r[i], wit.e1[i], wit.e2[i])
        out.append((radd(cin[i][0], t[0]), radd(cin[i][1], t[1])))
    return out

def ring_product_check(inst, rerand, rng):
    """The Neff product check of CCS 2023's Pi_SHUF, evaluated in R_q."""
    N = len(inst.a)
    hch = [rng.randrange(Q) for _ in range(N)]; rho = [rng.randrange(Q) for _ in range(N)]
    lhs = [1] + [0] * (N - 1); rhs = [1] + [0] * (N - 1)
    for mm in rerand: lhs = rmul(lhs, rsub(radd(mm[0], rmul(hch, mm[1])), rho))
    for mm in inst.cout: rhs = rmul(rhs, rsub(radd(mm[0], rmul(hch, mm[1])), rho))
    return lhs == rhs

def crt_slot_attack(inst, slot=0):
    """Swap one CRT slot between outputs 0 and 1 (Bootle-Lyubashevsky-Merino-Gallardo)."""
    roots = slot_roots(len(inst.a))
    bad = [tuple(list(x) for x in c) for c in inst.cout]; n0, n1 = [], []
    for comp in range(2):
        s0, s1 = to_slots(bad[0][comp], roots), to_slots(bad[1][comp], roots)
        s0[slot], s1[slot] = s1[slot], s0[slot]
        n0.append(from_slots(s0, roots)); n1.append(from_slots(s1, roots))
    bad[0], bad[1] = tuple(n0), tuple(n1)
    return Instance(inst.a, inst.b, inst.cin, bad)

# ------------------------------------------------------------------------------------------
# Tests
# ------------------------------------------------------------------------------------------
def tamper_targets(obj, path=()):
    """All leaves of a proof (field elements, Z_q elements, byte strings) with their paths."""
    if isinstance(obj, tuple) and len(obj) == 2 and all(isinstance(v, int) for v in obj): yield path
    elif isinstance(obj, (int, bytes)): yield path
    elif isinstance(obj, dict):
        for k in obj: yield from tamper_targets(obj[k], path + (k,))
    elif isinstance(obj, list):
        for i, v in enumerate(obj): yield from tamper_targets(v, path + (i,))

def tampered(proof, path):
    import copy
    p = copy.deepcopy(proof); o = p
    for key in path[:-1]: o = o[key]
    v = o[path[-1]]
    if isinstance(v, tuple): o[path[-1]] = ((v[0] + 1) % Q, v[1])
    elif isinstance(v, int): o[path[-1]] = (v + 1) % Q
    else: o[path[-1]] = bytes([v[0] ^ 1]) + v[1:]
    return p

if __name__ == "__main__":
    TAU, N = 16, 8
    par = MixParams(N, TAU, C1=64, C2=256, qbits=24)                 # small query count: fast tests
    print(f"q ~ 2^{Q.bit_length()-1}, F = GF(q^2);  tau = {TAU}, N = {N};  big rows {par.big.R} x {par.big.k} (n={par.big.n}, "
          f"{par.big.nq} queries), small rows {par.small.R} x {par.small.k} (n={par.small.n}, {par.small.nq} queries)")
    bgv, msgs, inst, wit = make_instance(TAU, N)
    plain = sorted(tuple(mm) for mm in msgs)
    dec_ms = lambda cs: sorted(bgv.dec(c) for c in cs)

    print("1. honest shuffle, Fiat-Shamir")
    t0 = time.time(); proof = mix_prove(par, inst, wit); t1 = time.time()
    ok, why = mix_verify(par, inst, proof); t2 = time.time()
    assert ok, why
    assert dec_ms(inst.cout) == plain
    assert sum(mix_size_model(N, TAU, par.C1, par.C2, RATE_INV, 24)) == proof_size(proof)
    print(f"   accepted; prove {t1-t0:.1f}s, verify {t2-t1:.1f}s; proof {proof_size(proof)/1024:.1f} KiB; size model exact")

    print("2. CRT-slot attack on the outputs")
    bad = crt_slot_attack(inst)
    rerand = [tuple(radd(inst.cin[i][c], bgv.rerand_term(wit.r[i], wit.e1[i], wit.e2[i])[c]) for c in range(2)) for i in range(TAU)]
    rng = random.Random(7)
    assert ring_product_check(inst, rerand, rng) and all(ring_product_check(bad, rerand, rng) for _ in range(3))
    assert dec_ms(bad.cout) != plain
    ok, why = mix_verify(par, bad, mix_prove(par, bad, wit))
    print(f"   passes the product check over R_q; decrypts to a different multiset; verifier: {why}"); assert not ok

    print("3. cheating provers (each runs the honest prover on an inconsistent statement or witness)")
    w3 = Witness(wit.sigma, [row[:] for row in wit.r], wit.e1, wit.e2); w3.r[5][0] = 2
    i3 = Instance(inst.a, inst.b, inst.cin, outputs(bgv, inst.cin, w3))
    w4 = Witness(wit.sigma, wit.r, wit.e1, [row[:] for row in wit.e2]); w4.e2[9][0] = (w4.e2[9][0] + pow(P_PLAIN, Q - 2, Q)) % Q
    i4 = Instance(inst.a, inst.b, inst.cin, outputs(bgv, inst.cin, w4))
    w5 = Witness(wit.sigma[:], wit.r, wit.e1, wit.e2); w5.sigma[3] = w5.sigma[9]
    i5 = Instance(inst.a, inst.b, inst.cin, outputs(bgv, inst.cin, w5))
    o6 = inst.cout[:]; o6[1], o6[2] = o6[2], o6[1]; i6 = Instance(inst.a, inst.b, inst.cin, o6)
    for label, ii, ww in (("coefficient 2 in a re-randomiser", i3, w3), ("vote flip via e2 += 1/p", i4, w4),
                          ("sigma not a permutation", i5, w5), ("two outputs swapped", i6, wit)):
        ok, why = mix_verify(par, ii, mix_prove(par, ii, ww))
        print(f"   {label}: {why}"); assert not ok
    assert dec_ms(i4.cout) != plain
    ok, why = mix_verify(par, i6, proof); assert not ok                    # a valid proof for another statement

    print("4. tampering with a valid proof: every leaf class, 60 random leaves")
    leaves = list(tamper_targets(proof)); rr = random.Random(11)
    by_key = {}
    for p in leaves: by_key.setdefault(p[0], []).append(p)
    picks = [rr.choice(v) for v in by_key.values()] + [rr.choice(leaves) for _ in range(60 - len(by_key))]
    for p in picks:
        ok, why = mix_verify(par, inst, tampered(proof, p)); assert not ok, p
    print(f"   {len(picks)} tampered proofs, all rejected ({len(leaves)} leaves in the proof)")

    print("5. interactive mode and the honest-verifier simulator")
    rc = RandomChallenger(); p_int = mix_prove(par, inst, wit, ch=rc)
    ok, why = mix_verify(par, inst, p_int, FixedChallenger(rc.log)); assert ok, why
    chal = mix_draw_challenges(par, inst, random.SystemRandom())
    sim = mix_simulate(par, inst, chal, random.SystemRandom())
    ok, why = mix_verify(par, inst, sim, FixedChallenger(chal)); assert ok, why
    print("   simulated transcript (no witness) accepted")
    real = mix_prove(par, inst, wit, ch=FixedChallenger(chal))
    ok, why = mix_verify(par, inst, real, FixedChallenger(chal)); assert ok, why
    rep = mix_simulate(par, inst, chal, random.SystemRandom(), coins=free_values(par, real))
    same = all(rep[k] == real[k] for k in ("G", "A", "B", "C", "evalsA", "evalsC", "mu", "vec", "prox"))
    same_cols = all(a["e"] == b["e"] and a["salt"] == b["salt"]
                    for name in par.mps for qa, qb in zip(rep["cols"][name], real["cols"][name]) for a, b in zip(qa, qb))
    print(f"   simulator fed the free values of a real transcript reproduces it (except Merkle roots/paths): {same and same_cols}")
    assert same and same_cols

    print("6. distribution of the free values of real transcripts (fixed challenges, 2 different witnesses, 300 runs each)")
    # two witnesses for the SAME statement: inputs 0 and 1 are equal ciphertexts, and the witnesses swap their roles
    par6 = MixParams(4, 4, C1=16, C2=128, qbits=6)
    bgv6, _m6, inst6, wit6 = make_instance(4, 4, seed=9)
    c6 = inst6.cin[:]; c6[1] = c6[0]
    w6a = Witness(wit6.sigma[:], wit6.r, wit6.e1, wit6.e2); i6a = Instance(inst6.a, inst6.b, c6, outputs(bgv6, c6, w6a))
    w6b = Witness(w6a.sigma[:], [x[:] for x in w6a.r], [x[:] for x in w6a.e1], [x[:] for x in w6a.e2])
    j0, j1 = w6a.sigma.index(0), w6a.sigma.index(1); w6b.sigma[j0], w6b.sigma[j1] = 1, 0
    for tbl in (w6b.r, w6b.e1, w6b.e2): tbl[0], tbl[1] = tbl[1], tbl[0]
    assert outputs(bgv6, c6, w6b) == i6a.cout
    chal6 = mix_draw_challenges(par6, i6a, random.SystemRandom())
    def probe(p):                                            # a few free values from every part of the transcript
        fv = free_values(par6, p)
        xs = [fv["G"][0], fv["evalsA"][0], fv["evalsA"][3], fv["evalsC"][1], fv["A"][0][0], fv["A"][-1][2], fv["B"][0][1],
              fv["C"][0][0], fv["C"][-1][5], p["mu"], fv["pcs"]["vec"]["S1"][0], fv["pcs"]["vec"]["S3"][1],
              fv["pcs"]["vec"]["S4"][3], fv["pcs"]["prox"]["big"][0], fv["pcs"]["prox"]["small"][2]]
        cols = [fv["pcs"]["cols"]["big"][0][0], fv["pcs"]["cols"]["small"][0][0], fv["pcs"]["cols"]["small"][1][par6.maskrow]]
        return [x[0] % 8 for x in xs] + [x[1] % 8 for x in xs] + [c % 8 for c in cols]
    RUNS = 300; worst = 0.0
    for wname, ww in (("witness A", w6a), ("witness B", w6b)):
        counts = None
        for _ in range(RUNS):
            pr = probe(mix_prove(par6, i6a, ww, ch=FixedChallenger(chal6)))
            if counts is None: counts = [[0] * 8 for _ in pr]
            for k, v in enumerate(pr): counts[k][v] += 1
        chi = [sum((c - RUNS / 8) ** 2 / (RUNS / 8) for c in row) for row in counts]
        worst = max(worst, max(chi))
        print(f"   {wname}: {len(chi)} probes, chi-square (7 d.o.f.) mean {sum(chi)/len(chi):.1f}, max {max(chi):.1f}")
    assert worst < 35, "a probe is far from uniform"                 # 7 d.o.f.: P[chi2 > 35] ~ 1e-5 per probe

    print("7. 128-bit query parameters, larger instance")
    for (t_, n_) in ((64, 32),):
        p7 = MixParams(n_, t_)
        _b, _m, inst7, wit7 = make_instance(t_, n_, seed=5)
        t0 = time.time(); pr7 = mix_prove(p7, inst7, wit7); t1 = time.time()
        ok, why = mix_verify(p7, inst7, pr7); t2 = time.time(); assert ok, why
        f_b, o_b = mix_size_model(n_, t_, p7.C1, p7.C2)
        assert f_b + o_b == proof_size(pr7)
        print(f"   tau={t_} N={n_}: C1={p7.C1}, C2={p7.C2}, queries {p7.big.nq}/{p7.small.nq}; proof {proof_size(pr7)/1024:.0f} KiB "
              f"(sumcheck part {f_b/1024:.1f} KiB); prove {t1-t0:.1f}s, verify {t2-t1:.1f}s; model exact")
        ok, why = mix_verify(p7, crt_slot_attack(inst7), pr7); assert not ok

    print("8. tables of the small matrix spanning several rows (tau > C2), and the byte format")
    p8 = MixParams(4, 1024, C1=512, C2=256, qbits=24)
    b8, m8, inst8, wit8 = make_instance(1024, 4, seed=8)
    t0 = time.time(); pr8 = mix_prove(p8, inst8, wit8); t1 = time.time()
    ok, why = mix_verify(p8, inst8, pr8); assert ok, why
    assert sum(mix_size_model(4, 1024, 512, 256, RATE_INV, 24)) == proof_size(pr8)
    blob = mix_serialize(p8, pr8); assert len(blob) == proof_size(pr8)
    ok, why = mix_verify(p8, inst8, mix_deserialize(p8, blob)); assert ok, why
    assert inst_deserialize(inst_serialize(inst8)).digest() == inst8.digest()
    ok, why = mix_verify(p8, crt_slot_attack(inst8), pr8); assert not ok
    w8 = Witness(wit8.sigma[:], wit8.r, wit8.e1, wit8.e2); w8.sigma[700] = w8.sigma[5]
    i8 = Instance(inst8.a, inst8.b, inst8.cin, outputs(b8, inst8.cin, w8))
    ok, why = mix_verify(p8, i8, mix_prove(p8, i8, w8)); assert not ok
    print(f"   tau=1024 N=4: small tables use {p8.rs} rows each; accepted; serialised proof = {len(blob)} bytes = model; prove {t1-t0:.1f}s")

    print("\nall checks passed\n")
    print("Extrapolation with the validated size model (N = 4096, q ~ 2^78, 128-bit query parameters):")
    print(f"   {'ballots':>8} {'C1':>6} {'C2':>6} {'sumcheck part':>14} {'opening':>10} {'per ballot':>11}   vs CCS 2023 proof (290 KB/ballot)")
    for lt in (10, 13, 16, 20):
        t_ = 1 << lt; c1, c2 = best_C(4096, t_)
        f_b, o_b = mix_size_model(4096, t_, c1, c2)
        print(f"   {'2^'+str(lt):>8} {'2^'+str(log2i(c1)):>6} {'2^'+str(log2i(c2)):>6} {f_b/1024:11.1f} KiB {o_b/2**20:7.1f} MiB "
              f"{(f_b+o_b)/t_:8.0f} B   {290*1024*t_/(f_b+o_b):7.0f}x smaller")
