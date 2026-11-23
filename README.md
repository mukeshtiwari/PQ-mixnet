# fp-mixnet: field-projection mixnet proofs for BGV

## What this repository does

A mixnet takes a list of encrypted ballots, shuffles and re-encrypts them, and finally decrypts them,
so that no one can link an output ballot to its voter. Each mix server must prove that it did its job
honestly. This repository contains two such proofs for the BGV lattice encryption scheme, in the
setting of Aranha, Baum, Gjosteen and Silde (CCS 2023):

- a **proof of shuffle**: the output ciphertexts are a permutation of the input ciphertexts,
  re-randomised with small noise;
- a **proof of correct partial decryption**: a decryption server applied its registered key share,
  with flooding noise inside a stated bound.

Both proofs are zero-knowledge, non-interactive and hash-based: they are sound in the (quantum)
random-oracle model and need no lattice assumption themselves. The idea, written up in
`paper/main.tex` and `docs/SPEC.md`, is to project the Z_q-linear mixnet relation into an extension
field GF(q^2) and prove it with sumchecks and a Reed-Solomon commitment.

The repository has three parts:

1. **A Rocq formalisation** (`src/`). It proves knowledge soundness of both proofs (Theorems 5.2 and
   7.1 of the paper), zero knowledge of the shuffle proof (Theorem 5.3), and that the executable
   verifiers and prover written in Rocq meet those statements. The audit checks that 236 main
   theorems use no axioms. `THEOREMS.md` lists every theorem and says exactly what it does and does not
   cover.
2. **Executables extracted from Rocq** (`src/Extraction`, `src/Executable`). They are a shuffle-proof
   verifier, a decryption-proof verifier and a shuffle-proof prover. They read and write the same
   files as the unverified implementations.
3. **Unverified implementations** (`Unverified/`). A Python reference (prover, verifier, simulator,
   tests) and a fast C++ prover and verifier for the shuffle proof, byte-compatible with each other
   and with the extracted Rocq code.

Not for production use: see `Handoff.md` section 6, tasks H1 to H5.

## Layout

The layout follows SigmaProtocol: generic code, instances, extraction, executables, and the
unverified code kept apart.

| Path | What it is |
| --- | --- |
| `src/Algebra`, `src/Utility`, `src/Probability` | general libraries (copied from SigmaProtocol) |
| `src/Crypto` | the generic theory, over any field: sumcheck, masks, Reed-Solomon opening, the row layouts, soundness and zero knowledge |
| `src/Examples` | instances at GF(q^2): the concrete field, the executable verifiers and prover (`Exec*.v`), zero knowledge for the shuffle proof's layout |
| `src/Extraction` | one directory per extracted OCaml library, each with its `Extraction.v` (`Fpexeclib`: verifiers; `Fpprovelib`: provers), and `Hshalib`, the binding to HACL*'s SHA-256 |
| `src/Executable` | the OCaml drivers, one directory each with `main.ml`: `Fpverify`, `Fpdecverify`, `Fpprove`, `Fpdecprove`, `Fpcheck` |
| `audit/`, `audit.sh` | the axiom audit |
| `THEOREMS.md`, `src/README.md` | theorem index; Rocq layout and conventions |
| `Unverified/fp_core.py` | field GF(q^2), transcript, masked sumcheck, commitment, zero-knowledge opening, simulator |
| `Unverified/mix_proof.py` | shuffle proof: prover, verifier, simulator, byte format, tests |
| `Unverified/dec_proof.py` | decryption proof: prover, verifier, simulator, byte format, tests |
| `Unverified/mixnative.cpp` | native provers and verifiers for the shuffle proof and the decryption proof |
| `Unverified/cross_check.py` | Python and C++ must accept each other's proofs; with `FP_ROCQ=1`, also the extracted verifiers |
| `Unverified/cross_field.py`, `Unverified/cross_prove.py` | the extracted Rocq code against the Python reference |
| `Unverified/size_tables.py`, `Unverified/expected.json` | proof sizes from the exact size models; recorded sizes checked by `run_all.sh` |
| `Unverified/opening_estimates.py`, `Unverified/variant_sizes.py` | ESTIMATES of other openings; not implemented |
| `Unverified/toy_example.py`, `docs/TOY_EXAMPLE.md` | worked example: 2 ballots, N = 4, q = 7681, every message traced |
| `docs/SPEC.md` | protocols, theorems, proofs, hashing layout and wire formats |
| `Handoff.md` | state of the project, open tasks, verified and unverified claims |
| `paper/` | `main.tex` (draft paper), `tutorial.tex` (step-by-step tutorial) |
| `results/` | test logs (`baseline-*`: from the machine this was developed on) |

## Requirements

- For the Rocq part: Rocq 9.2 and dune 3.23, with the opam packages `rocq-prover` (or `rocq-core` and
  `rocq-stdlib`), `coq-ext-lib`, `rocq-coqprime`, `rocq-bignums`, `zarith` and `hacl-star`.
- For the unverified part: Python 3.9 or newer (standard library only) and a C++20 compiler with
  `__int128`. The OpenSSL headers are optional; without them the C++ code uses a slower built-in SHA-256.

## Building and testing

All commands run from the repository root.

    dune build             # the Rocq development, the extracted libraries and the four executables
    ./audit.sh             # check that the main theorems use no axioms (prints AUDIT OK)

    ./run_all.sh smoke     # builds mixnative, native self-tests, size check (about 1 minute)
    ./run_all.sh           # + full Python test suites and the Python/C++ cross-check, both regimes
    ./run_all.sh bench     # + native benchmarks at 256, 1024, 4096 ballots

    FP_ROCQ=1 python3 Unverified/cross_check.py   # the extracted verifiers against Python and C++ proofs
    python3 Unverified/cross_field.py             # extracted pieces against the Python reference
    python3 Unverified/cross_prove.py             # the extracted prover against mix_prove, byte for byte

`./run_all.sh` builds `Unverified/mixnative`. Run it once before the examples below, which use that
binary to make test files.

## Running the OCaml executables

After `dune build`, the executables are at `_build/default/src/Executable/<Name>/main.exe`. In the
examples below:

    X=_build/default/src/Executable

### Common parameters

Every command takes the public parameters as arguments. They are not stored in the files, so they must
be the ones the proof was made with:

- `N`: ring dimension (number of polynomial coefficients); `tau`: number of ciphertexts. Both are
  powers of two.
- `C1`, `C2`: row lengths of the big and the small committed matrix (powers of two).
- `qbits`: security level of the query phase (24 for quick tests, 128 for real use).
- For the decryption proof: `base` and `kdig`. The flooding noise is written as `kdig` digits in
  base `base`.

Two environment variables change the protocol and are bound into the transcript. Prover and verifier
must use the same values:

- `FP_PROX_DIV`: proximity regime, 3 (default) or 2;
- `FP_RATE_INV`: inverse code rate, 4 (default) or 2.

Exit codes: 0 means accepted (or success), 1 means rejected, 2 means a usage error. The verifiers also
print `accept` or `reject`.

### Fpverify: verify a shuffle proof

    $X/Fpverify/main.exe N tau C1 C2 qbits INSTANCE PROOF

`INSTANCE` holds the public key and the input and output ciphertexts (`mix_proof.py: inst_serialize`).
`PROOF` is in the format of `mix_serialize`. This is the same interface as `mixnative verify`.

Example: make a proof with the native prover, then check it with the verifier extracted from Rocq:

    Unverified/mixnative prove 8 16 64 256 24 7 /tmp/shuffle     # writes /tmp/shuffle.inst, /tmp/shuffle.proof
    $X/Fpverify/main.exe 8 16 64 256 24 /tmp/shuffle.inst /tmp/shuffle.proof
    accept

The arguments of `mixnative prove` are `N tau C1 C2 qbits seed prefix`. A changed byte in either file
gives `reject`.

### Fpprove: make a shuffle proof

    $X/Fpprove/main.exe [--text] N tau C1 C2 qbits INSTANCE WITNESS OUT [COINS]

This writes the proof to `OUT` in the format of `mix_serialize`. With `--text` it also writes
`OUT.txt`, the same proof as numbers: one labelled section per part (mask sums, sumcheck round
messages, evaluations, mu, slot and proximity vectors, opened columns), with Z_q entries in decimal,
a GF(q^2) element a + b·t as `a b`, and hashes and salts in hex. The text comes from decoding `OUT`
with the verifier's extracted parser, so it shows exactly what a verifier reads. It is for reading
only: the verifiers take the binary file. `WITNESS` holds the secret
permutation and re-randomisers in this driver's format (described at the top of
`src/Executable/Fpprove/main.ml`). Without `COINS`, the random coins are read from `/dev/urandom`.
With `COINS`, the run replays given coins, which is how `cross_prove.py` compares it with the Python
prover byte for byte.

Example: Python makes a random instance and its witness. The Rocq prover proves it, and both
verifiers accept:

    python3 -c "
    import sys; sys.path.insert(0, 'Unverified')
    from mix_proof import make_instance, inst_serialize
    from cross_prove import wit_serialize
    _bgv, _msgs, inst, wit = make_instance(16, 8, seed=1)        # tau = 16 ciphertexts, N = 8
    open('/tmp/my.inst', 'wb').write(inst_serialize(inst))
    open('/tmp/my.wit', 'wb').write(wit_serialize(wit, 8, 16))"
    $X/Fpprove/main.exe --text 8 16 64 256 24 /tmp/my.inst /tmp/my.wit /tmp/my.proof
    $X/Fpverify/main.exe 8 16 64 256 24 /tmp/my.inst /tmp/my.proof
    accept
    head -8 /tmp/my.proof.txt                                   # the proof as numbers
    Unverified/mixnative verify 8 16 64 256 24 /tmp/my.inst /tmp/my.proof

The prover is proven complete in `src/Examples/ExecComplete.v`: for a valid witness and any coins,
its proof is accepted.

### Fpdecprove: make a decryption proof

    $X/Fpdecprove/main.exe N tau base kdig C1 C2 qbits STATEMENT WITNESS OUT [COINS]

The decryption prover extracted from Rocq (`src/Examples/ExecDecProve.v: xdec_prove`). `STATEMENT` is
the file read by `Fpdecverify`; `WITNESS` holds s, e and the flooding noise E_1..E_tau, every
coefficient as 10 bytes mod q (described at the top of `src/Executable/Fpdecprove/main.ml`); `COINS`
as for `Fpprove`. `Unverified/cross_decprove.py` checks that it writes the same bytes as `dec_prove`
for the same coins, and that `Fpdecverify` accepts its proofs and rejects tampered ones. Its
completeness and zero knowledge are not yet proven.

### Fpdecverify: verify a decryption proof

    $X/Fpdecverify/main.exe N tau base kdig C1 C2 qbits STATEMENT PROOF

`STATEMENT` holds the public key share and the ciphertexts with their partial decryptions
(`dec_proof.py: dec_stmt_serialize`). `PROOF` is in the format of `dec_serialize`. Both formats are
in `docs/SPEC.md`, section 4. A proof from the native prover:

    Unverified/mixnative decprove 8 16 2 8 64 0 24 7 /tmp/ndec     # N tau base kdig C1 C2 qbits seed prefix
    $X/Fpdecverify/main.exe 8 16 2 8 64 128 24 /tmp/ndec.stmt /tmp/ndec.proof
    accept

(`C2 = 0` lets the prover choose the default, 128 here; it prints the values it used.) The same
with a proof made in Python:

    python3 -c "
    import sys, random; sys.path.insert(0, 'Unverified')
    import dec_proof as dp
    from fp_core import Q
    par = dp.DecParams(8, 16, 2, 8, C1=64, qbits=24)              # N, tau, base, kdig
    rng = random.Random(1)
    a = [rng.randrange(Q) for _ in range(8)]
    s, e, b = dp.keyshare(a, rng)                                 # key share b = a s + p e
    us = [[rng.randrange(Q) for _ in range(8)] for _ in range(16)]
    E, ts = dp.partial_decrypt(par, s, us, rng)                   # t_i = s u_i + p E_i
    st = dp.DecStatement(a, b, us, ts)
    open('/tmp/dec.stmt', 'wb').write(dp.dec_stmt_serialize(st))
    open('/tmp/dec.proof', 'wb').write(dp.dec_serialize(par, dp.dec_prove(par, st, dp.DecWitness(s, e, E))))
    print('C1 =', par.C1, ' C2 =', par.C2)"
    C1 = 64  C2 = 128
    $X/Fpdecverify/main.exe 8 16 2 8 64 128 24 /tmp/dec.stmt /tmp/dec.proof
    accept

`DecParams` chooses `C2` when it is not given, so pass the value it prints. A wrong `C2` changes the
transcript, and the proof is rejected.

### Fpcheck: test driver for the extracted pieces

    $X/Fpcheck/main.exe

This reads one request per line on standard input and prints one answer per line. It exposes the
extracted field arithmetic, SHA-256, Merkle trees, the transcript, the claims, the sumcheck layer and
the opening checks. `Unverified/cross_field.py` uses it to compare each piece with the Python
reference. The list of requests is at the top of `src/Executable/Fpcheck/main.ml`. For example,
multiplication in GF(q^2) = Z_q[t]/(t^2 - 3) and SHA-256:

    printf 'mul 3 4 5 6\nsha 616263\n' | $X/Fpcheck/main.exe
    87 38
    ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

### What is verified and what is not

The algebra of the verifiers and the prover is proven in Rocq. Some pieces are only tested:

- the parsers, the Fiat-Shamir transcript and the Merkle checks of the extracted code;
- the OCaml drivers in `src/Executable`;
- HACL*'s SHA-256, which the extracted code uses in place of the Rocq definition (the two are compared
  in `cross_field.py`).

Everything in `Unverified/` is tested, not proven. Details are in `THEOREMS.md` and in `Handoff.md`,
section 8.

## The unverified C++ prover and verifier

In `Unverified/` (`./run_all.sh` does this for you):

    c++ -O3 -march=native -std=c++20 -Wno-deprecated-declarations mixnative.cpp -lcrypto -o mixnative
    c++ -O3 -std=c++20 -DFP_PORTABLE_SHA256 mixnative.cpp -o mixnative     # without OpenSSL, slower
    ./mixnative prove 4096 1024 32768 1024 128 11     # N tau C1 C2 qbits seed [prefix|-] [store]
    ./mixnative verify N tau C1 C2 qbits INSTANCE PROOF
    ./mixnative decprove 4096 1024 4 28 0 0 128 11    # N tau base kdig C1 C2 qbits seed [prefix|-]  (0: default C1, C2)
    ./mixnative decverify N tau base kdig C1 C2 qbits STATEMENT PROOF

`FP_PROX_DIV=2` selects the unique-decoding proximity regime (fewer queries; relies on the
Reed-Solomon proximity-gap theorem). The default, 3, relies only on an elementary lemma.
`FP_RATE_INV=2` selects code rate 1/2 instead of 1/4. It halves the encoding and hashing work, and
with `FP_PROX_DIV=2` it gives the default proof size at about 1.6 times the prover speed.
