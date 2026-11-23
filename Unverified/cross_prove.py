#!/usr/bin/env python3
"""
cross_prove.py -- the shuffle prover extracted from Rocq (src/Examples/ExecProve.v: xmix_prove, driver
src/Executable/Fpprove) against mix_proof.mix_prove.

    dune build && python3 Unverified/cross_prove.py

For each case: mix_prove runs with a recording source of randomness; the same integers and salts are handed
to fpprove, and the two proofs must be identical bytes. Then fpprove runs on fresh OS randomness, and its
proof must be accepted by mix_verify (Python) and by fpverify (Rocq). Exit code 0 if all of this holds.
"""
import os, random, subprocess, sys, tempfile, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fp_core import *
from mix_proof import MixParams, make_instance, mix_prove, mix_verify, mix_serialize, mix_deserialize, inst_serialize

FPP = os.path.join(HERE, "..", "_build", "default", "src", "Executable", "Fpprove", "main.exe")
FPV = os.path.join(HERE, "..", "_build", "default", "src", "Executable", "Fpverify", "main.exe")

class Recording:
    """random.Random with a record of the draws mix_prove makes (randrange(Q), randbytes(SALT))."""
    def __init__(self, seed): self.r = random.Random(seed); self.zs = []; self.ss = []
    def randrange(self, n):
        assert n == Q; v = self.r.randrange(n); self.zs.append(v); return v
    def randbytes(self, k):
        assert k == SALT; v = self.r.randbytes(k); self.ss.append(v); return v

def wit_serialize(wit, N, tau):
    out = b"".join(s.to_bytes(4, "big") for s in wit.sigma)
    for tbl in (wit.r, wit.e1, wit.e2):
        out += b"".join(ser_base(x % Q) for poly in tbl for x in poly)
    return out

def coins_serialize(zs, ss):
    return len(zs).to_bytes(4, "big") + b"".join(ser_base(z) for z in zs) + len(ss).to_bytes(4, "big") + b"".join(ss)

def main():
    tmp = tempfile.mkdtemp(prefix="fpprove_")
    cases = [(8, 16, 64, 256, 24), (4, 1024, 512, 256, 24), (32, 64, 256, 256, 128), (16, 2, 32, 128, 24), (2, 64, 16, 128, 24)]
    for (N, tau, C1, C2, qbits) in cases:
        par = MixParams(N, tau, C1=C1, C2=C2, qbits=qbits)
        _bgv, _msgs, inst, wit = make_instance(tau, N, seed=7 * N + tau)
        fi, fw, fc, fo = (os.path.join(tmp, x) for x in ("i", "w", "c", "o"))
        open(fi, "wb").write(inst_serialize(inst)); open(fw, "wb").write(wit_serialize(wit, N, tau))
        rec = Recording(N * 1000 + tau)
        t0 = time.time(); blob = mix_serialize(par, mix_prove(par, inst, wit, rnd=rec)); tp = time.time() - t0
        open(fc, "wb").write(coins_serialize(rec.zs, rec.ss))
        args = [str(a) for a in (N, tau, C1, C2, qbits, fi, fw, fo)]
        t0 = time.time(); r = subprocess.run([FPP] + args + [fc], capture_output=True, text=True); tr = time.time() - t0
        assert r.returncode == 0, r.stdout + r.stderr
        mine = open(fo, "rb").read()
        if mine != blob:
            first = next((i for i in range(min(len(mine), len(blob))) if mine[i] != blob[i]), None)
            sys.exit(f"N={N} tau={tau}: proofs differ (lengths {len(mine)} / {len(blob)}, first differing byte {first})")
        # fresh coins
        r = subprocess.run([FPP] + args, capture_output=True, text=True); assert r.returncode == 0, r.stdout + r.stderr
        fresh = open(fo, "rb").read()
        ok, why = mix_verify(par, inst, mix_deserialize(par, fresh)); assert ok, why
        rv = subprocess.run([FPV] + [str(a) for a in (N, tau, C1, C2, qbits, fi, fo)], capture_output=True, text=True)
        assert rv.returncode == 0, "fpverify rejects the Rocq proof: " + rv.stdout + rv.stderr
        print(f"N={N:3d} tau={tau:5d} C1={C1:4d} C2={C2:4d} qbits={qbits:3d}: Rocq proof = mix_prove proof "
              f"({len(blob)} bytes; {len(rec.zs)} integers, {len(rec.ss)} salts replayed; Rocq {tr:.1f} s, Python {tp:.1f} s); "
              f"fresh-coin Rocq proof accepted by mix_verify and fpverify")
    print("cross_prove passed")

if __name__ == "__main__":
    main()
