#!/usr/bin/env python3
"""
variant_sizes.py -- ESTIMATE of two changes to the opening of the big matrix.  Neither is implemented.

  V = 3   as built: two slot vectors (points of sumcheck B and of sumcheck C) + one proximity vector
  V = 2   'merged': the linearisation (sumcheck B) is folded into the shortness sumcheck, so the big
          matrix is opened at one point only: one slot vector + one proximity vector
  V = 1   'merged, no proximity vector': the slot vector itself is the proximity test, because its row
          coefficients are a random tensor; needs the tensor proximity-gap theorem of Diamond-Posen
          (ePrint 2023/630), which is stated for e < d/3, so PROX_DIV = 3 only

Sizes follow mix_size_model with V vectors and 2(V-1)+2 ... mask rows on the big matrix.
    python3 variant_sizes.py ;  FP_PROX_DIV=2 python3 variant_sizes.py
"""
from fp_core import EB, SALT, PROX_DIV, RATE_INV, TWO_ADICITY, code_params, log2i, nrows_for
N = 4096

def size(tau, C1, C2, V):
    logN, ell = log2i(N), log2i(tau); m = logN + ell
    f_elems = 3 + (3 * (ell - 1) + 5) + 4 + (2 * logN if V == 3 else 0) + (4 * (m - 1) + 7) + 3 + 1
    k1, n1, q1 = code_params(C1, RATE_INV, 128); k2, n2, q2 = code_params(C2, RATE_INV, 128)
    R1 = 3 * nrows_for(tau * N, C1) + 2 * V; R2 = 5 * nrows_for(tau, C2) + 7
    return (f_elems * 2 * EB + 96 + V * k1 * 2 * EB + 3 * k2 * 2 * EB
            + q1 * (R1 * EB + SALT + 32 * log2i(n1)) + q2 * (R2 * EB + 2 * (SALT + 32 * log2i(n2))))

def best(tau, V):
    out = None; logN, ell = log2i(N), log2i(tau); m = logN + ell
    n_mask = 7 + (3 * (ell - 1) + 6) + (2 * logN + 1 if V == 3 else 0) + (4 * (m - 1) + 8)
    for l1 in range(6, 30):
        if (1 << l1) > N * tau or code_params(1 << l1, RATE_INV, 128)[1] > 1 << TWO_ADICITY: break
        for l2 in range(7, 22):
            if (1 << l2) > max(tau, 128) or code_params(1 << l2, RATE_INV, 128)[1] > 1 << TWO_ADICITY: break
            if (1 << l2) < 2 * n_mask: continue                      # the mask table must fit in one row
            s = size(tau, 1 << l1, 1 << l2, V)
            if out is None or s < out: out = s
    return out

if __name__ == "__main__":
    print(f"ESTIMATE (V = 2 and V = 1 are not implemented).  N = {N}, e = floor((d-1)/{PROX_DIV}), rate 1/{RATE_INV}")
    print(f"{'ballots':>8} {'V=3 (built)':>14} {'V=2 merged':>14} {'V=1 merged, no prox. vector':>30}")
    for lt in (10, 13, 16, 20):
        tau = 1 << lt; s3, s2 = best(tau, 3), best(tau, 2)
        s1 = f"{best(tau, 1) / 1e6:.2f} MB" if PROX_DIV == 3 else "n/a (needs e < d/3)"
        print(f"{'2^%d' % lt:>8} {s3 / 1e6:>11.2f} MB {s2 / 1e6:>11.2f} MB {s1:>30}")
