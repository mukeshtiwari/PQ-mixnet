# fp-mixnet in Rocq

Formalisation of `paper/main.tex`, following `docs/ROCQ_PLAN.md`. Rocq 9.2, Stdlib, ExtLib and CoqPrime
(only `ConcreteField.v` uses CoqPrime: the positive-number certificate checker
`PocklingtonCertificat`, which needs no axioms; the `Pock` variant on primitive integers does).
`THEOREMS.md` maps each paper claim to its Rocq name and says what is and is not proven.

    dune build        # build everything
    ./audit.sh        # build, then check that the audited theorems use no axioms
    python3 Unverified/cross_field.py   # extracted pieces against fp_core.py / mix_proof.py (needs the opam packages zarith and hacl-star)
    _build/default/src/Executable/Fpverify/main.exe N tau C1 C2 qbits INSTANCE PROOF
                      # the extracted shuffle-proof verifier; same interface and files as `mixnative verify`
    _build/default/src/Executable/Fpdecverify/main.exe N tau base kdig C1 C2 qbits STATEMENT PROOF
                      # the extracted decryption-proof verifier; files of dec_stmt_serialize, dec_serialize
    FP_ROCQ=1 python3 Unverified/cross_check.py   # the extracted verifiers against Python and C++
    _build/default/src/Executable/Fpprove/main.exe N tau C1 C2 qbits INSTANCE WITNESS OUT [COINS]
                      # the extracted shuffle prover (ExecProve.v; complete: ExecComplete.v); witness format in its main.ml
    python3 Unverified/cross_prove.py   # Fpprove against mix_prove, byte for byte with the same coins

All commands run from the repository root.

## Layout

The layout follows SigmaProtocol: generic code, instances, extraction, executables.

| Directory | Content |
| --- | --- |
| `src/Algebra/`, `src/Utility/`, `src/Probability/`, `src/Crypto/PolyRoots.v` | copied unchanged from `SigmaProtocol` (commit 0c10dd3, 11 November 2026; that working tree had uncommitted changes outside these files) |
| `src/Crypto/` (theory `Crypto`) | the generic development, over any field: sumcheck, masks, Reed-Solomon opening, the layouts, soundness (Theorems 5.2, 7.1) and zero knowledge (`ZkTranscript`, `ZkJoin`, ...) |
| `src/Examples/` (theory `Examples`) | instances at GF(q^2): the concrete field (`ConcreteField`, `ConcreteInstance`), the executable verifiers and prover (`Exec*.v`), zero knowledge for the layout of `mix_derive` (`ZkLayer`, `ZkOpenMix`, `ZkMixJoin`) and its refinement to the extracted prover (`ExecZkSC`, `ExecZkTables`, `ExecZkMsgs`, `ExecZkOpen`, `ExecZkMain`, `ExecZkCoins`) |
| `src/Extraction/` | one directory per extracted OCaml library, each with its `Extraction.v`: `Fpexeclib` (verifiers, field arithmetic, test entry points), `Fpprovelib` (the shuffle prover); `Hshalib` is the OCaml binding of HACL*'s SHA-256 that both use (not verified) |
| `src/Executable/` | the OCaml drivers, one directory each with `main.ml` (not verified): `Fpverify`, `Fpdecverify`, `Fpprove`, `Fpcheck` (line-based test driver for `Unverified/cross_field.py`) |
| `audit/Audit.v` | `Print Assumptions` for the main theorems (`./audit.sh` at the root) |

A file in `src/Crypto` never imports one in `src/Examples`.

## Conventions

- A field is the class `Hierarchy.field` over Leibniz equality, with decidable equality.
- "Probability at most k/|F|" is a count: for a duplicate-free list `lf` of all field elements and a
  boolean event, `length (filter bad ...) <= k * length lf ^ (n-1)`.
- Proofs about executable code that draws Fiat-Shamir challenges keep the drawing operations abstract (`sc_chalsG`,
  `xmix_trG`, `xmix_prove_partsG` take them as arguments). With the concrete `get_F`, a case split on a draw can make
  the kernel evaluate SHA-256 on symbolic data when it checks the proof (seen: `Qed` not finishing in 20 minutes).
- No `Axiom`, no `Admitted`. Results that the paper cites (the line lemma) are hypotheses of a
  `Section` and appear as premises of the theorems that use them.
- Inside a section, `*`, `+`, `-` are the field operations. Write nat arithmetic inside `(...)%nat`.
- Do not call `lia` with a hypothesis in context that has a power with a 78-bit exponent: it does
  not return. Clear it, or give the side conditions by `vm_compute`.
- Do not `rewrite <- e` when `e : _ = zero`: it also rewrites the implicit `zero` inside `dot`,
  `eval` and `fsum`. Use `transitivity`.
