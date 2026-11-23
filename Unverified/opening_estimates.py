#!/usr/bin/env python3
"""
opening_estimates.py -- ESTIMATE (nothing here is implemented) of the proof size if the vectors
of the opening were not sent in the clear but proven with a FRI/BaseFold-style folding argument.

Design assumed:  rows as now (data || pads, message space K = 2C), code length n = K / rho;
  the batched combination of the rows is the first (virtual) FRI oracle, so every query opens
  two columns of the committed matrix (positions j and j + n/2, stored in one Merkle leaf);
  later layers are committed every `a` folds (leaf = coset of 2^a F-elements); folding stops
  at a message of 64 symbols, sent in the clear; no Merkle-path pruning.
Query count for 128 bits:  nq = ceil(128 / -log2(1 - delta)),
  'UD'      delta = (1 - rho)/2               unique-decoding radius [BCIKS20, Thm 1.2/1.6]
  'Johnson' delta = 1 - sqrt(rho)(1 + 1/20)   list-decoding regime of [BCIKS20] (larger error terms)
"""
import math
EB, SALT, HASH, FE = 10, 16, 32, 20
N = 4096
def log2i(x): return x.bit_length() - 1

def fold_part(R, C, rho_inv, regime, a=3):
    K = 2 * C; n = rho_inv * K
    if n > 1 << 24: return None
    rho = 1 / rho_inv
    delta = (1 - rho) / 2 if regime == "UD" else 1 - math.sqrt(rho) * 1.05
    nq = math.ceil(128 / -math.log2(1 - delta))
    per_q = 2 * R * EB + SALT + HASH * (log2i(n) - 1)                  # two columns in one leaf
    size, msg = n // 2, K // 2                                         # after the first fold
    layers = 0
    while msg > 64:
        per_q += FE * (1 << a) + HASH * max(0, log2i(size) - a); layers += 1
        size >>= a; msg >>= a
    fixed = HASH * (layers + 1) + FE * 64 + FE * 2 * (log2i(K) + 3)     # roots, final message, sumcheck
    return nq * per_q + fixed, nq

def best(tau, rho_inv, regime):
    out = None
    for l1 in range(8, 24):
        C1 = 1 << l1
        if C1 > N * tau: break
        b = fold_part(3 * max(1, N * tau // C1) + 6, C1, rho_inv, regime)
        if b is None: continue
        for l2 in range(8, 24):
            C2 = 1 << l2
            if C2 > max(tau, 256): break
            s = fold_part(5 * max(1, tau // C2) + 7, C2, rho_inv, regime)
            if s is None: continue
            tot = b[0] + s[0] + 5000
            if out is None or tot < out[0]: out = (tot, l1, l2, b[1])
    return out

if __name__ == "__main__":
    print("ESTIMATE, not implemented.  N = 4096, 128-bit query soundness.")
    print(f"{'ballots':>8} {'rate':>5} {'regime':>8} {'queries':>8} {'C1':>5} {'C2':>5} {'proof':>10} {'B/ballot':>9}")
    for lt in (10, 13, 16, 20):
        for rho_inv in (2, 4):
            for regime in ("UD", "Johnson"):
                tot, l1, l2, nq = best(1 << lt, rho_inv, regime)
                print(f"{'2^%d' % lt:>8} {'1/%d' % rho_inv:>5} {regime:>8} {nq:>8} {'2^%d' % l1:>5} {'2^%d' % l2:>5} {tot / 1e6:>8.2f}MB {tot / (1 << lt):>9.0f}")
