#!/usr/bin/env python3
"""
cross_decprove.py -- the decryption prover extracted from Rocq (src/Examples/ExecDecProve.v: xdec_prove, driver
src/Executable/Fpdecprove) against dec_proof.dec_prove, and against the extracted decryption verifier.

    dune build && python3 Unverified/cross_decprove.py

For each case: dec_prove runs with a recording source of randomness; the same integers and salts are handed to
fpdecprove, and the two proofs must be identical bytes. Then fpdecprove runs on fresh OS randomness, and its proof
must be accepted by the extracted verifier (fpdecverify), which must reject bit-flipped and truncated proofs and a
changed statement. Exit code 0 if all of this holds.
"""
import os, random, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fp_core import *
import dec_proof as dp
from cross_prove import Recording, coins_serialize
B = os.path.join(HERE, "..", "_build", "default", "src", "Executable")
FPP, FPV = os.path.join(B, "Fpdecprove", "main.exe"), os.path.join(B, "Fpdecverify", "main.exe")
tmp = tempfile.mkdtemp(prefix="fpdecprove_")
def wit_ser(w): return b"".join(ser_base(x % Q) for poly in [w.s, w.e] + list(w.E) for x in poly)
for (N, tau, base, kd, C1, qbits) in ((8, 16, 2, 8, 64, 24), (16, 32, 4, 5, None, 128), (4, 64, 16, 2, None, 24), (32, 8, 8, 3, 32, 128)):
    par = dp.DecParams(N, tau, base, kd, C1=C1, qbits=qbits)
    rng = random.Random(N + tau + base)
    a = [rng.randrange(Q) for _ in range(N)]; s, e, b = dp.keyshare(a, rng)
    us = [[rng.randrange(Q) for _ in range(N)] for _ in range(tau)]
    E, ts = dp.partial_decrypt(par, s, us, rng); st = dp.DecStatement(a, b, us, ts); w = dp.DecWitness(s, e, E)
    fs, fw, fc, fo, fb = (os.path.join(tmp, x) for x in "swcob")
    sb = dp.dec_stmt_serialize(st); open(fs, "wb").write(sb); open(fw, "wb").write(wit_ser(w))
    args = [str(x) for x in (N, tau, base, kd, par.C1, par.C2, qbits)]
    rec = Recording(N * 1000 + tau)
    blob = dp.dec_serialize(par, dp.dec_prove(par, st, w, rnd=rec))
    open(fc, "wb").write(coins_serialize(rec.zs, rec.ss))
    r = subprocess.run([FPP] + args + [fs, fw, fo, fc], capture_output=True, text=True); assert r.returncode == 0, r.stderr
    mine = open(fo, "rb").read()
    if mine != blob:
        first = next((i for i in range(min(len(mine), len(blob))) if mine[i] != blob[i]), None)
        sys.exit(f"N={N} tau={tau} base={base}: proofs differ (lengths {len(mine)}/{len(blob)}, first differing byte {first})")
    # fresh coins, extracted verifier only
    r = subprocess.run([FPP] + args + [fs, fw, fo], capture_output=True, text=True); assert r.returncode == 0, r.stderr
    fresh = open(fo, "rb").read()
    v = lambda st_, pf: subprocess.run([FPV] + args + [st_, pf], capture_output=True).returncode
    assert v(fs, fo) == 0, "extracted verifier rejects the extracted proof"
    rr = random.Random(len(fresh)); rej = 0
    for _ in range(6):
        b2 = bytearray(fresh); b2[rr.randrange(len(b2))] ^= 1 << rr.randrange(8); open(fb, "wb").write(bytes(b2)); rej += v(fs, fb) == 1
    open(fb, "wb").write(fresh[:-1]); rej += v(fs, fb) == 1
    s2 = bytearray(sb); s2[-1] ^= 1; open(fb, "wb").write(bytes(s2)); rej += v(fb, fo) == 1
    assert rej == 8, rej
    print(f"N={N} tau={tau} base={base} kdig={kd}: same bytes as dec_prove for the same coins ({len(blob)} B); "
          f"fresh proof accepted by the extracted verifier; 6 bit flips, truncation, changed statement rejected", flush=True)
print("cross_decprove passed")
