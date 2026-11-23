#!/usr/bin/env python3
"""
size_tables.py -- proof sizes from the exact size models of mix_proof.py and dec_proof.py
(the models are checked byte-for-byte against real proofs in the test suites).

    python3 size_tables.py                 # elementary proximity regime, e = floor((d-1)/3)
    FP_PROX_DIV=2 python3 size_tables.py   # unique-decoding regime, e = floor((d-1)/2)  [BCIKS20, Thm 1.6]
"""
import sys
from fp_core import PROX_DIV, RATE_INV, code_params, log2i
from mix_proof import best_C, mix_size_model
import dec_proof as dp

N = 4096
CCS_MIX_PROOF = 290_000          # bytes per ballot per mix server   (CCS 2023, proof part of the 370 KB)
CCS_DEC_PROOF = 117_000          # bytes per ballot per decryption server
CT = 80_000                      # bytes per ciphertext (CCS 2023)

def dec_c2(N, tau, base, kdig):
    logN, ell = log2i(N), log2i(tau); m = logN + ell
    dG = (base + 1) * (m - 1) + 2 * base + 1; dT = 4 * (logN - 1) + 7
    n_mask = kdig + 2 + 1 + dG + 1 + dT
    return max(N, 1 << (2 * n_mask - 1).bit_length())

print(f"proximity regime: e = floor((d-1)/{PROX_DIV});  N = {N}, 128-bit query soundness, rate 1/{RATE_INV}\n")
print("MIX PROOF (per mix server)")
print(f"{'ballots':>8} {'C1':>6} {'C2':>6} {'queries':>9} {'proof':>10} {'B/ballot':>9} {'vs CCS proof':>13} {'proof/statement':>16}")
for lt in (10, 13, 16, 20):
    tau = 1 << lt
    C1, C2 = best_C(N, tau)
    f, o = mix_size_model(N, tau, C1, C2)
    q1, q2 = code_params(C1, RATE_INV, 128)[2], code_params(C2, RATE_INV, 128)[2]
    tot = f + o
    print(f"{'2^%d' % lt:>8} {'2^%d' % log2i(C1):>6} {'2^%d' % log2i(C2):>6} {'%d/%d' % (q1, q2):>9} {tot / 1e6:>8.2f}MB {tot / tau:>9.0f} {CCS_MIX_PROOF * tau / tot:>12.0f}x {100 * tot / (2 * tau * CT):>15.3f}%")
print("\nDECRYPTION PROOF (per decryption server), flooding bound 2^55 (base 2) or 2^56 (base 4)")
print(f"{'ballots':>8} {'digits':>10} {'C1':>6} {'proof':>10} {'B/ballot':>9} {'vs CCS proof':>13}")
for lt in (10, 13, 16, 20):
    tau = 1 << lt
    for base, kdig in ((2, 55), (4, 28)):
        C2 = dec_c2(N, tau, base, kdig)
        C1 = dp.dec_best_C1(N, tau, base, kdig, C2)
        f, o = dp.dec_size_model(N, tau, base, kdig, C1, C2)
        tot = f + o
        print(f"{'2^%d' % lt:>8} {'%d base-%d' % (kdig, base):>10} {'2^%d' % log2i(C1):>6} {tot / 1e6:>8.2f}MB {tot / tau:>9.0f} {CCS_DEC_PROOF * tau / tot:>12.0f}x")
