(* The two soundness theorems at the concrete field GF(q^2) of the
   implementation (ConcreteField.v).

   mix_theorem_5_2_Fq2 and dec_theorem_7_1_Fq2 are mix_theorem_5_2 and
   dec_theorem_7_1 with the field, its decidable equality, its field
   axioms and the list of all its elements filled in. For the shuffle
   proof the two conditions on the characteristic (1, .., tau and N are
   non-zero in the field) are discharged from tau < q and N < q.

   What remains a hypothesis is what is a hypothesis in the general
   theorems: the instance and layout parameters, the Reed-Solomon
   parameters, and one proximity statement per code. *)

From Stdlib Require Import Utf8 ZArith List Lia.
From Algebra Require Import Hierarchy.
From Crypto Require Import LogDer. From Examples Require Import ConcreteField. From Crypto Require Import MixFinal DecFinal.
Import ListNotations.

Lemma char_tau : forall ell : nat, (Z.of_nat (2 ^ ell) < Q)%Z ->
  forall k : nat, 0 < k <= 2 ^ ell -> @nF Fq2 fzero fone fadd k <> fzero.
Proof. intros ell h k hk. apply Fq2_char. lia. Qed.

Lemma char_N : forall n1 : nat, (Z.of_nat (2 ^ n1) < Q)%Z -> @nF Fq2 fzero fone fadd (2 ^ n1) <> fzero.
Proof.
  intros n1 h. apply Fq2_char. pose proof (Nat.pow_nonzero 2 n1 ltac:(lia)). lia.
Qed.

Definition mix_theorem_5_2_Fq2
  (a b : list Fq2) (pp : Fq2) (n1 ell : nat) (Hell : 1 <= ell)
  (Htau : (Z.of_nat (2 ^ ell) < Q)%Z) (HNq : (Z.of_nat (2 ^ n1) < Q)%Z) :=
  @mix_theorem_5_2 Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field
    lf2 lf2_NoDup lf2_all a b pp n1 ell Hell (char_tau ell Htau) (char_N n1 HNq).

Definition dec_theorem_7_1_Fq2 :=
  @dec_theorem_7_1 Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field
    lf2 lf2_NoDup lf2_all.

(* the number of field elements *)
Lemma lf2_length : length lf2 = (Z.to_nat Q * Z.to_nat Q)%nat.
Proof.
  transitivity (length lq * length lq); [exact (length_prod lq lq) |].
  unfold lq. rewrite length_map, length_seq. reflexivity.
Qed.
