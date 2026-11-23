#!/usr/bin/env python3
"""
cross_check.py -- the native implementation (mixnative.cpp) and the Python references
(mix_proof.py, dec_proof.py) must accept each other's proofs and reject each other's tampered
proofs, for the shuffle proof and for the decryption proof.

    g++ -O3 -march=native -std=c++20 -Wno-deprecated-declarations mixnative.cpp -lcrypto -o mixnative
    python3 cross_check.py

With FP_ROCQ=1, also the verifier extracted from Rocq (src/Executable/Fpverify, built by `dune build`
at the repository root) must accept the native and the Python proof and reject bit-flipped proofs and the CRT-slot
attack, for every case (under a second per proof); and the decryption-proof verifier extracted from
Rocq (src/Executable/Fpdecverify) must accept Python decryption proofs read from files (dec_serialize,
dec_stmt_serialize) and reject bit-flipped proofs and a changed statement.
"""
import os, random, subprocess, sys, tempfile
from mix_proof import *

BIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "mixnative")
FPV = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "_build", "default", "src", "Executable", "Fpverify", "main.exe")
FPD = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "_build", "default", "src", "Executable", "Fpdecverify", "main.exe")
ROCQ = os.environ.get("FP_ROCQ") == "1"

def rocq_verify(N, tau, C1, C2, qbits, f_inst, f_proof):
    return subprocess.run([FPV] + [str(a) for a in (N, tau, C1, C2, qbits, f_inst, f_proof)], capture_output=True, text=True).returncode

def run(*args):
    return subprocess.run([BIN] + [str(a) for a in args], capture_output=True, text=True)

def main():
    tmp = tempfile.mkdtemp(prefix="mixcross_")
    cases = [(8, 16, 64, 256, 24), (4, 1024, 512, 256, 24), (32, 64, 256, 256, 128), (16, 2, 32, 128, 24), (2, 64, 16, 128, 24)]
    for (N, tau, C1, C2, qbits) in cases:
        par = MixParams(N, tau, C1=C1, C2=C2, qbits=qbits)
        # --- native prover -> Python verifier
        pre = os.path.join(tmp, f"n{N}_{tau}")
        r = run("prove", N, tau, C1, C2, qbits, 12345 + N + tau, pre)
        assert r.returncode == 0, r.stdout + r.stderr
        inst = inst_deserialize(open(pre + ".inst", "rb").read())
        blob = open(pre + ".proof", "rb").read()
        assert len(blob) == sum(mix_size_model(N, tau, C1, C2, RATE_INV, qbits)), "size differs from the Python model"
        ok, why = mix_verify(par, inst, mix_deserialize(par, blob)); assert ok, why
        rr = random.Random(N * tau); rej = 0
        for _ in range(6):
            b2 = bytearray(blob); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8)
            try: ok2, _ = mix_verify(par, inst, mix_deserialize(par, bytes(b2)))
            except Reject: ok2 = False
            rej += not ok2
        assert rej == 6
        bad = crt_slot_attack(inst); ok3, _ = mix_verify(par, bad, mix_deserialize(par, blob)); assert not ok3
        # --- Python prover -> native verifier
        bgv, msgs, inst2, wit2 = make_instance(tau, N, seed=N + 3 * tau)
        proof2 = mix_prove(par, inst2, wit2)
        f_inst, f_proof = os.path.join(tmp, "p.inst"), os.path.join(tmp, "p.proof")
        blob2 = mix_serialize(par, proof2)
        open(f_inst, "wb").write(inst_serialize(inst2)); open(f_proof, "wb").write(blob2)
        r = run("verify", N, tau, C1, C2, qbits, f_inst, f_proof); assert r.returncode == 0, r.stdout + r.stderr
        rej = 0
        for _ in range(6):
            b2 = bytearray(blob2); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8)
            open(f_proof, "wb").write(bytes(b2)); rej += run("verify", N, tau, C1, C2, qbits, f_inst, f_proof).returncode == 1
        assert rej == 6
        open(f_inst, "wb").write(inst_serialize(crt_slot_attack(inst2))); open(f_proof, "wb").write(blob2)
        assert run("verify", N, tau, C1, C2, qbits, f_inst, f_proof).returncode == 1
        if ROCQ:
            assert os.path.exists(FPV), "FP_ROCQ=1 but _build/default/src/Executable/Fpverify/main.exe is missing: run `dune build` at the repository root"
            assert rocq_verify(N, tau, C1, C2, qbits, pre + ".inst", pre + ".proof") == 0, "Rocq verifier rejects the native proof"
            open(f_inst, "wb").write(inst_serialize(inst2)); open(f_proof, "wb").write(blob2)
            assert rocq_verify(N, tau, C1, C2, qbits, f_inst, f_proof) == 0, "Rocq verifier rejects the Python proof"
            for _ in range(2):
                b2 = bytearray(blob2); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8)
                open(f_proof, "wb").write(bytes(b2)); assert rocq_verify(N, tau, C1, C2, qbits, f_inst, f_proof) == 1
            open(f_proof, "wb").write(blob2); open(f_inst, "wb").write(inst_serialize(crt_slot_attack(inst2)))
            assert rocq_verify(N, tau, C1, C2, qbits, f_inst, f_proof) == 1
            print("   Rocq-extracted verifier: native and Python proofs accepted, 2 bit-flipped proofs and the CRT-slot attack rejected")
        print(f"N={N:3d} tau={tau:5d} C1={C1:4d} C2={C2:4d} qbits={qbits:3d}: native proof accepted by Python and Python proof accepted "
              f"by native ({len(blob)} bytes each way); 12 bit-flipped proofs and 2 CRT-slot attacks rejected")
    dec_cross(tmp)
    if ROCQ:
        rocq_dec_check(tmp)
    print("cross-check passed")

def dec_cross(tmp):
    """Decryption proof: native prover -> Python verifier, Python prover -> native verifier."""
    import dec_proof as dp
    for (N, tau, base, kd, C1, qbits) in ((8, 16, 2, 8, 64, 24), (16, 32, 4, 5, None, 128), (4, 64, 16, 2, None, 24), (32, 8, 8, 3, 32, 128)):
        par = dp.DecParams(N, tau, base, kd, C1=C1, qbits=qbits)
        pre = os.path.join(tmp, f"dec{N}_{tau}")
        r = run("decprove", N, tau, base, kd, par.C1, par.C2, qbits, 777 + N + tau, pre)
        assert r.returncode == 0, r.stdout + r.stderr
        sblob, blob = open(pre + ".stmt", "rb").read(), open(pre + ".proof", "rb").read()
        assert len(blob) == sum(dp.dec_size_model(N, tau, base, kd, par.C1, par.C2, RATE_INV, qbits)), "size differs from the Python model"
        ok, why = dp.dec_verify_bytes(par, sblob, blob); assert ok, why
        rr = random.Random(N * tau + base)
        for _ in range(4):
            b2 = bytearray(blob); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8)
            assert not dp.dec_verify_bytes(par, sblob, bytes(b2))[0]
        rng = random.Random(N + tau + base)
        a = [rng.randrange(Q) for _ in range(N)]; s, e, b = dp.keyshare(a, rng)
        us = [[rng.randrange(Q) for _ in range(N)] for _ in range(tau)]
        E, ts = dp.partial_decrypt(par, s, us, rng); st = dp.DecStatement(a, b, us, ts)
        blob2 = dp.dec_serialize(par, dp.dec_prove(par, st, dp.DecWitness(s, e, E))); sblob2 = dp.dec_stmt_serialize(st)
        f_st, f_pf = os.path.join(tmp, "dp.stmt"), os.path.join(tmp, "dp.proof")
        nv = lambda: run("decverify", N, tau, base, kd, par.C1, par.C2, qbits, f_st, f_pf).returncode
        open(f_st, "wb").write(sblob2); open(f_pf, "wb").write(blob2); assert nv() == 0, "native decryption verifier rejects the Python proof"
        for _ in range(4):
            b2 = bytearray(blob2); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8)
            open(f_pf, "wb").write(bytes(b2)); assert nv() == 1
        open(f_pf, "wb").write(blob2); s2 = bytearray(sblob2); s2[-1] ^= 1; open(f_st, "wb").write(bytes(s2)); assert nv() == 1
        print(f"decryption N={N:3d} tau={tau:3d} base={base:2d} kdig={kd}: native proof accepted by Python and Python proof accepted by "
              f"native ({len(blob)} bytes); 8 bit-flipped proofs and a changed statement rejected")

def rocq_dec_check(tmp):
    import dec_proof as dp
    assert os.path.exists(FPD), "FP_ROCQ=1 but _build/default/src/Executable/Fpdecverify/main.exe is missing: run `dune build` at the repository root"
    for (N, tau, base, kd, C1, qbits) in ((8, 16, 2, 8, 64, 24), (16, 32, 4, 5, None, 128)):
        par = dp.DecParams(N, tau, base, kd, C1=C1, qbits=qbits)
        rng = random.Random(N + tau)
        a = [rng.randrange(Q) for _ in range(N)]; s, e, b = dp.keyshare(a, rng)
        us = [[rng.randrange(Q) for _ in range(N)] for _ in range(tau)]
        E, ts = dp.partial_decrypt(par, s, us, rng); st = dp.DecStatement(a, b, us, ts)
        blob = dp.dec_serialize(par, dp.dec_prove(par, st, dp.DecWitness(s, e, E))); sblob = dp.dec_stmt_serialize(st)
        f_st, f_pf = os.path.join(tmp, "d.stmt"), os.path.join(tmp, "d.proof")
        args = [FPD] + [str(x) for x in (N, tau, base, kd, par.C1, par.C2, qbits, f_st, f_pf)]
        dv = lambda: subprocess.run(args, capture_output=True, text=True).returncode
        open(f_st, "wb").write(sblob); open(f_pf, "wb").write(blob)
        assert dv() == 0, "Rocq decryption verifier rejects the Python proof"
        rr = random.Random(len(blob))
        for _ in range(4):
            b2 = bytearray(blob); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8)
            open(f_pf, "wb").write(bytes(b2)); assert dv() == 1
        open(f_pf, "wb").write(blob[:-1]); assert dv() == 1
        open(f_pf, "wb").write(blob); s2 = bytearray(sblob); s2[-1] ^= 1; open(f_st, "wb").write(bytes(s2)); assert dv() == 1
        pre = os.path.join(tmp, f"rdec{N}_{tau}")
        r = run("decprove", N, tau, base, kd, par.C1, par.C2, qbits, 99 + N, pre); assert r.returncode == 0, r.stdout + r.stderr
        open(f_st, "wb").write(open(pre + ".stmt", "rb").read()); open(f_pf, "wb").write(open(pre + ".proof", "rb").read())
        assert dv() == 0, "Rocq decryption verifier rejects the native proof"
        print(f"   Rocq-extracted decryption verifier, N={N} tau={tau} base={base} kdig={kd}: Python and native proofs accepted "
              f"({len(blob)} bytes); 4 bit-flipped proofs, a truncated proof and a changed statement rejected")

if __name__ == "__main__":
    main()
