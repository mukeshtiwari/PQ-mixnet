#!/usr/bin/env python3
"""
cross_field.py -- the field arithmetic extracted from Rocq (src/Examples/ExecField.v, proven
equal to the field GF(q^2) of the theorems) against fp_core.py.

    dune build && python3 Unverified/cross_field.py

Compares add, sub, neg, mul, inv, int, equality, eq_eval, zval, eq_table, lo_vec, hi_coefs, interp, the rounds of
sc_verify (given challenges), SHA-256, leaf hashes, Merkle roots from paths and the Fiat-Shamir
challenger (absorb, field challenges, index challenges), and the nine claims of mix_derive on real
proofs (the extracted xclaims9 against MixParams/mix_derive), and the opening checks on real proofs, honest
and tampered (the extracted xaccO against pcs_open_verify), and the sumcheck layer of mix_derive (the extracted xderive against the
claimed values of mix_derive, honest and with altered messages), and the decryption verifier
(the extracted xdec_verify against dec_verify, honest and tampered) on random inputs and on the edge values 0, 1, 2, q-2, q-1.  Exit code 0 if every answer agrees.
"""
import os, random, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fp_core import *

BIN = os.path.join(HERE, "..", "_build", "default", "src", "Executable", "Fpcheck", "main.exe")

def open_request(par, proof, slots, claims, log, mp_names=("big", "small")):
    """The opening checks of pcs_open_verify (without Merkle paths), as a request for fpcheck."""
    f2 = lambda x: f"{x[0]} {x[1]}"
    fl = lambda xs: " ".join([str(len(xs))] + [f2(x) for x in xs])
    il = lambda xs: " ".join([str(len(xs))] + [str(x) for x in xs])
    big, small = par.mps["big"], par.mps["small"]; SO = big.R
    off = {"big": 0, "small": SO}
    sv = {"big": sorted(int(s[1]) for s in slots if slots[s]["mat"] == "big"),
          "small": sorted(int(s[1]) for s in slots if slots[s]["mat"] == "small")}
    out = ["open", str(big.k), str(small.k), f2((big.w, 0)), f2((small.w, 0)), str(SO), il(sv["big"]), il(sv["small"])]
    for v in sv["big"] + sv["small"]:
        sl = slots[f"S{v}"]; o = off[sl["mat"]]
        kind = 1 if sl["kind"] == "func" else 0
        frow = 0
        if kind:
            rows = {row for (_, terms) in claims for (sid, row, _, _) in terms if sid == f"S{v}"}
            frow = o + rows.pop()
        lt = sl["lovec"] if not kind else []
        ma, mb = sl["mask"]
        out += [str(kind), str(frow), fl(lt), "2", str(o + ma), f2(ONE), str(o + mb), f2(TGEN)]
    rws = {n: [off[n] + i for i in range(par.mps[n].R) if i not in par.mps[n].prox_mask] for n in mp_names}
    out += [il(rws["big"]), il(rws["small"])]
    for n in mp_names: out += [str(off[n] + par.mps[n].prox_mask[0]), str(off[n] + par.mps[n].prox_mask[1])]
    out.append(str(len(claims)))
    for _, terms in claims:
        out.append(str(len(terms)))
        for (sid, row, coef, lv) in terms:
            dense = [] if lv is None else ([lv.get(i, ZERO) for i in range(max(lv) + 1)] if isinstance(lv, dict) else list(lv))
            out += [sid[1], str(row + off[slots[sid]["mat"]]), f2(coef), fl(dense)]
    out += [fl([v for v, _ in claims]), fl(log["pcs.kappa"]), f2(log["pcs.c"][0])]
    for n in mp_names:
        g = log[f"pcs.gamma.{n}"]; out.append(fl([g[i] for i in range(par.mps[n].R) if i not in par.mps[n].prox_mask]))
    out += [il(log["pcs.J.big"]), il(log["pcs.J.small"]), f2(proof["mu"])]
    for v in sv["big"] + sv["small"]: out.append(fl(proof["vec"][f"S{v}"]))
    out += [fl(proof["prox"]["big"]), fl(proof["prox"]["small"])]
    for n in mp_names:
        for per_batch in proof["cols"][n]:
            out.append(il([x for item in per_batch for x in item["e"]]))
    return " ".join(out)

def derive_request(par, inst, proof, log):
    f2 = lambda x: f"{x[0]} {x[1]}"
    fl = lambda xs: " ".join([str(len(xs))] + [f2(x) for x in xs])
    base = lambda poly: [(x, 0) for x in poly]
    ctxs = lambda cs: " ".join([str(len(cs))] + [fl(base(c0)) + " " + fl(base(c1)) for c0, c1 in cs])
    al, be = log["ab"]
    kA = log["kA"] + log["rhoA"]; kC = log["kC"] + log["rhoC"]
    rA = [log[f"A.r{j}"][0] for j in range(par.ell)]; ry = [log[f"B.r{j}"][0] for j in range(par.logN)]
    rz = [log[f"C.r{j}"][0] for j in range(par.m)]
    msgs = lambda ms: " ".join([str(len(ms))] + [fl(ev) for ev in ms])
    out = ["derive", str(par.logN), str(par.ell), fl(base(inst.a)), fl(base(inst.b)), f2((MP_P_PLAIN, 0)),
           ctxs(inst.cin), ctxs(inst.cout), fl(log["rho_u"]), fl(log["rho_v"]), f2(al), f2(be),
           fl(log["tc"]), fl(kA), fl(rA), f2(log["rhoB"][0]), fl(ry), fl(log["tz"]), fl(kC), fl(rz),
           " ".join(f2(g) for g in proof["G"]), msgs(proof["A"]), " ".join(f2(x) for x in proof["evalsA"]),
           msgs(proof["B"]), msgs(proof["C"]), " ".join(f2(x) for x in proof["evalsC"])]
    return " ".join(out)

def decverify_request(par, st, proof):
    import dec_proof as DP
    f2 = lambda x: f"{x[0]} {x[1]}"
    fl = lambda xs: " ".join([str(len(xs))] + [f2(x) for x in xs])
    il = lambda xs: " ".join([str(len(xs))] + [str(x) for x in xs])
    ms = lambda mm: " ".join([str(len(mm))] + [fl(ev) for ev in mm])
    big, small = par.big, par.small
    out = ["decverify", str(par.logN), str(par.ell), str(log2i(par.C1)), str(par.kdig), str(par.base),
           str(big.k), str(big.n), str(big.nq), str(small.k), str(small.n), str(small.nq), str(big.w), str(small.w),
           par.tag.hex(), str(DP.P_PLAIN), str(par.off),
           il(st.a), il(st.b), " ".join([str(len(st.us))] + [il(u) for u in st.us]),
           " ".join([str(len(st.ts))] + [il(t) for t in st.ts]),
           proof["root_big"].hex(), proof["root_small"].hex(), fl(proof["G"]), ms(proof["scG"]), fl(proof["evalsG"]),
           ms(proof["scT"]), fl(proof["evalsT"]), f2(proof["mu"])]
    for sid in ("S1", "S2", "Ss", "Se", "Sm"): out.append(fl(proof["vec"][sid]))
    out += [fl(proof["prox"]["big"]), fl(proof["prox"]["small"])]
    for name in ("big", "small"):
        qs = proof["cols"][name]; out.append(str(len(qs)))
        for per_batch in qs:
            out.append(str(len(per_batch)))
            for item in per_batch:
                out += [il(item["e"]), item["salt"].hex(), " ".join([str(len(item["path"]))] + [h.hex() for h in item["path"]])]
    return " ".join(out)

def main():
    if not os.path.exists(BIN):
        print("src/Executable/Fpcheck/main.exe not built: run `dune build` at the repository root first"); return 2
    rnd = random.Random(20261111)
    edge = [0, 1, 2, Q - 1, Q - 2]
    def el():
        return (rnd.choice(edge), rnd.choice(edge)) if rnd.random() < 0.2 else frand(rnd)
    reqs, want = [], []
    def add(req, ans): reqs.append(req); want.append(ans)
    f2 = lambda x: f"{x[0]} {x[1]}"
    for _ in range(2000):
        a, b = el(), el()
        add(f"add {f2(a)} {f2(b)}", f2(fadd(a, b)))
        add(f"sub {f2(a)} {f2(b)}", f2(fsub(a, b)))
        add(f"mul {f2(a)} {f2(b)}", f2(fmul(a, b)))
        add(f"neg {f2(a)}", f2(fneg(a)))
        add(f"inv {f2(a)}", f2(finv(a)))
        add(f"eqb {f2(a)} {f2(b)}", "1" if a == b else "0")
        add(f"eqb {f2(a)} {f2(a)}", "1")
        c = rnd.randrange(-Q * Q, Q * Q)
        add(f"int {c}", f2(fint(c)))
    for _ in range(300):
        n = rnd.randrange(0, 12)
        r = [el() for _ in range(n)]; s = [el() for _ in range(n)]
        add(f"eqeval {n} " + " ".join(f2(x) for x in r + s), f2(eq_eval(r, s)))
        add(f"zval {n} " + " ".join(f2(x) for x in r), f2(zval(r)))
    for _ in range(300):
        n = rnd.randrange(0, 9)
        r = [el() for _ in range(n)]
        add(f"eqtable {n} " + " ".join(f2(x) for x in r), " ".join(f2(x) for x in eq_table(r)))
    for _ in range(300):
        n = rnd.randrange(1, 10)
        v = [el() for _ in range(n)]; x = el()
        add(f"interp {n} " + " ".join(f2(y) for y in v + [x]), f2(interp(v, x)))
    for _ in range(300):
        n = rnd.randrange(0, 8); lo = rnd.randrange(0, 8)
        x = [el() for _ in range(n)]
        xs = " ".join(f2(y) for y in x)
        add(f"lovec {lo} {n} {xs}", " ".join(f2(y) for y in lo_vec(x, 1 << lo, 1 << n)))
        add(f"hicoefs {lo} {n} {xs}", " ".join(f2(y) for y in hi_coefs(x, 1 << lo, 1 << n)))
    for t in range(300):
        m = rnd.randrange(1, 8); deg = rnd.randrange(1, 5); deg_last = rnd.randrange(1, 9)
        claim = el(); msgs = [[el() for _ in range(deg_last if j == m - 1 else deg)] for j in range(m)]
        chal = {f"X.r{j}": [el()] for j in range(m)}
        _, final = sc_verify(FixedChallenger(chal), "X", msgs, claim, m, deg, deg_last)
        parts = [f"scv {m} {f2(claim)}"]
        for j in range(m):
            parts.append(f"{len(msgs[j])} " + " ".join(f2(e) for e in msgs[j]) + f" {f2(chal[f'X.r{j}'][0])}")
        add(" ".join(parts), f2(final))
    hx = lambda b: b.hex() if b else "-"
    for _ in range(300):
        b = rnd.randbytes(rnd.choice([0, 1, 55, 56, 63, 64, 65, 119, 120, 128, rnd.randrange(0, 600)]))
        add(f"sha {hx(b)}", H(b).hex())
        add(f"shaspec {hx(b)}", H(b).hex())
    for _ in range(200):
        salt = rnd.randbytes(SALT); es = [rnd.randrange(Q) for _ in range(rnd.randrange(0, 12))]
        add(f"leaf {salt.hex()} {len(es)} " + " ".join(map(str, es)), leaf_hash(salt, es).hex())
        k = rnd.randrange(0, 10); j = rnd.randrange(1 << k); leaf = rnd.randbytes(32)
        path = [rnd.randbytes(32) for _ in range(k)]
        add(f"root {leaf.hex()} {j} {k} " + " ".join(p.hex() for p in path), merkle_root_from(leaf, j, path).hex())
    for _ in range(100):
        dom = rnd.choice([b"mix", b"dec", rnd.randbytes(rnd.randrange(0, 20))]); ch = FSChallenger(dom)
        ops, vals = [], []
        for _ in range(rnd.randrange(1, 12)):
            t = rnd.randrange(3)
            if t == 0:
                lab, data = rnd.randbytes(rnd.randrange(1, 12)), rnd.randbytes(rnd.randrange(0, 300))
                ops.append(f"A {hx(lab)} {hx(data)}"); ch.absorb(lab, data)
            elif t == 1:
                name = rnd.choice(["theta", "pcs.kappa", "G.r3", "rhoG"]); n = rnd.randrange(0, 6)
                ops.append(f"F {name.encode().hex()} {n}")
                for a, b in ch.get(name, "F", n): vals += [str(a), str(b)]
            else:
                name = rnd.choice(["pcs.J.big", "pcs.J.small"]); bound = 1 << rnd.randrange(4, 12)
                n = rnd.randrange(0, min(bound // 2, 40))
                ops.append(f"I {name.encode().hex()} {n} {bound}")
                vals += [str(v) for v in ch.get(name, "I", n, bound)]
        add(f"fs {hx(dom)} " + " ".join(ops), " ".join(vals))
    # prover side: Merkle trees and row encoding
    for _ in range(40):
        d = rnd.randrange(0, 7); leaves = [rnd.randbytes(32) for _ in range(1 << d)]; j = rnd.randrange(1 << d)
        layers = merkle_build(leaves)
        add(f"mtree {d} {j} " + " ".join(l.hex() for l in leaves),
            " ".join([layers[-1][0].hex()] + [p.hex() for p in merkle_path(layers, j)]))
    for _ in range(40):
        n = 1 << rnd.randrange(1, 8); k = rnd.randrange(1, n + 1)
        w = pow(ROOT, (1 << TWO_ADICITY) // n, Q); msg = [rnd.randrange(Q) for _ in range(k)]
        add(f"encrow {w} {n} {k} " + " ".join(map(str, msg)), " ".join(map(str, ntt(msg + [0] * (n - k), w))))
    # the nine claims of mix_derive on real proofs
    import mix_proof as MP
    for (N, tau, C1, C2) in [(4, 4, 8, 128), (8, 16, 64, 256), (16, 2, 32, 128), (2, 64, 16, 128), (8, 8, 128, 128)]:
        par = MP.MixParams(N, tau, C1=C1, C2=C2, qbits=24)
        bgv, msgs_, inst, wit = MP.make_instance(tau, N, seed=N + tau)
        proof = MP.mix_prove(par, inst, wit)
        rec = Recorder(FSChallenger(b"mix"))
        slots, claims = MP.mix_derive(par, inst, proof, rec)
        pcs_open_verify(rec, par.mps, {"big": [proof["root_big"]], "small": [proof["root_s1"], proof["root_s2"]]},
                        slots, claims, proof)
        L = rec.log
        r = [L[f"A.r{j}"][0] for j in range(par.ell)]; ry = [L[f"B.r{j}"][0] for j in range(par.logN)]
        rz = [L[f"C.r{j}"][0] for j in range(par.m)]
        _, _, rp = MP.public_projection(inst, L["rho_u"], L["rho_v"])
        mrp = [mle(rp[k], ry) for k in range(3)]
        invN = finv(fint(N)); SO = 3 * par.rw + 6
        lo1, lo2 = log2i(C1), log2i(C2)
        req = (f"claims {par.logN} {par.ell} {lo1} {lo2} {SO} "
               + " ".join(str(x) for d in (par.dA, par.dB, par.dC) for x in [len(d)] + d) + " "
               + " ".join(f2(x) for x in [invN, L["rhoB"][0]] + mrp + r + ry + rz))
        toks = []
        for _, terms in claims:
            toks.append(f"C {len(terms)}")
            for (sid, row, coef, lv) in terms:
                sl = int(sid[1]); grow = row + (SO if slots[sid]["mat"] == "small" else 0)
                if lv is None: dense = []
                elif isinstance(lv, dict):
                    dense = [lv.get(i, ZERO) for i in range(max(lv) + 1)] if lv else []
                else: dense = list(lv)
                toks.append(" ".join([str(sl), str(grow), f2(coef), str(len(dense))] + [f2(x) for x in dense]))
        add(req, " ".join(toks))
        # the sumcheck layer: honest and with altered messages (the values change; rho = 0 rejects)
        global MP_P_PLAIN; MP_P_PLAIN = MP.P_PLAIN
        import copy
        def py_derive(pr, log):
            try:
                _, cl = MP.mix_derive(par, inst, pr, FixedChallenger(log))
                return " ".join(f2(v) for v, _ in cl)
            except Reject: return "reject"
        dvars = [(proof, L)]
        q1 = copy.deepcopy(proof); q1["A"][0][1] = fadd(q1["A"][0][1], ONE); dvars.append((q1, L))
        q2 = copy.deepcopy(proof); q2["B"][-1][0] = fadd(q2["B"][-1][0], TGEN); dvars.append((q2, L))
        q3 = copy.deepcopy(proof); q3["evalsC"][1] = fadd(q3["evalsC"][1], ONE); dvars.append((q3, L))
        q4 = copy.deepcopy(proof); q4["G"][2] = fadd(q4["G"][2], ONE); dvars.append((q4, L))
        L5 = dict(L); L5["rhoA"] = [ZERO]; dvars.append((proof, L5))
        for pr, lg in dvars:
            add(derive_request(par, inst, pr, lg), py_derive(pr, lg))
        fl = lambda xs: " ".join([str(len(xs))] + [f2(x) for x in xs])
        zpub, zhat, rp = MP.public_projection(inst, L["rho_u"], L["rho_v"])
        add("rhor " + " ".join([fl([(x, 0) for x in inst.a]), fl([(x, 0) for x in inst.b]), fl(L["rho_u"]), fl(L["rho_v"])]),
            " ".join(f2(x) for x in rp[0]))
        add("mle " + fl(zhat) + " " + fl(r), f2(mle(zhat, r)))
        # the opening checks: the honest proof, and tampered messages, claims and columns
        import copy
        def py_open(pr, cl):
            try:
                pcs_open_verify(FixedChallenger(L), par.mps, {"big": [pr["root_big"]], "small": [pr["root_s1"], pr["root_s2"]]},
                                slots, cl, pr)
                return "1"
            except Reject: return "0"
        variants = [(proof, claims)]
        p1 = copy.deepcopy(proof); p1["mu"] = fadd(p1["mu"], ONE); variants.append((p1, claims))
        p2 = copy.deepcopy(proof); v = p2["vec"]["S3"]; v[0] = fadd(v[0], ONE); variants.append((p2, claims))
        p3 = copy.deepcopy(proof); v = p3["prox"]["big"]; v[-1] = fadd(v[-1], TGEN); variants.append((p3, claims))
        p4 = copy.deepcopy(proof); e = p4["cols"]["big"][0][0]["e"]; e[0] = (e[0] + 1) % Q; variants.append((p4, claims))
        p5 = copy.deepcopy(proof); e = p5["cols"]["small"][1][1]["e"]; e[-1] = (e[-1] + 1) % Q; variants.append((p5, claims))
        c6 = list(claims); c6[3] = (fadd(c6[3][0], ONE), c6[3][1]); variants.append((proof, c6))
        for pr, cl in variants:
            add(open_request(par, pr, slots, cl, L), py_open(pr, cl))
    # the decryption verifier on real proofs, honest and tampered
    import copy, dec_proof as DP
    for (N, tau, base, kd, C1) in [(8, 16, 2, 8, 64), (4, 4, 4, 3, 16), (16, 2, 3, 4, 32)]:
        par = DP.DecParams(N, tau, base, kd, C1=C1, qbits=24)
        rng = random.Random(N * tau + kd)
        a = [rng.randrange(Q) for _ in range(N)]
        s_, e_, bj = DP.keyshare(a, rng)
        us = [[rng.randrange(Q) for _ in range(N)] for _ in range(tau)]
        E, ts = DP.partial_decrypt(par, s_, us, rng)
        st = DP.DecStatement(a, bj, us, ts)
        pf = DP.dec_prove(par, st, DP.DecWitness(s_, e_, E))
        def pyv(p, stt=st): return "1" if DP.dec_verify(par, stt, p)[0] else "0"
        variants = [(pf, st)]
        p1 = copy.deepcopy(pf); p1["mu"] = fadd(p1["mu"], ONE); variants.append((p1, st))
        p2 = copy.deepcopy(pf); p2["scG"][0][0] = fadd(p2["scG"][0][0], ONE); variants.append((p2, st))
        p3 = copy.deepcopy(pf); p3["evalsT"][1] = fadd(p3["evalsT"][1], TGEN); variants.append((p3, st))
        p4 = copy.deepcopy(pf); e = p4["cols"]["small"][0][0]["e"]; e[0] = (e[0] + 1) % Q; variants.append((p4, st))
        p5 = copy.deepcopy(pf); v = p5["vec"]["Ss"]; v[1] = fadd(v[1], ONE); variants.append((p5, st))
        t2 = [list(t) for t in ts]; t2[0][0] = (t2[0][0] + 1) % Q
        variants.append((pf, DP.DecStatement(a, bj, us, t2)))
        for p, stt in variants:
            add(decverify_request(par, stt, p), pyv(p, stt))
    out = subprocess.run([BIN], input="\n".join(reqs) + "\n", capture_output=True, text=True)
    if out.returncode != 0:
        print("fpcheck.exe failed:", out.stderr); return 1
    got = out.stdout.split("\n")[:-1]
    if len(got) != len(want):
        print(f"expected {len(want)} answers, got {len(got)}"); return 1
    bad = [(q, w, g) for q, w, g in zip(reqs, want, got) if w != g]
    for q, w, g in bad[:5]: print("MISMATCH", q[:120], "python:", w, "rocq:", g)
    print(f"cross_field: {len(want) - len(bad)}/{len(want)} answers agree")
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
