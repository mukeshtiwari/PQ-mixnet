(* Prover side of the commitment, stage 1: Merkle trees and row encoding
   (fp_core.py: merkle_build, merkle_path, Matrix.commit, ntt).

   - mroot d l, mpath d l j: the root of the tree over 2^d leaves and the
     authentication path of leaf j (siblings from the bottom up, as
     fp_core.merkle_path).
   - root_from_path: the verifier's check (ExecHash.root_from) succeeds on
     every path the tree produces. This is the Merkle part of completeness.
   - xenc_row om n msg: the codeword of a row of integers mod q at the
     points om^j, j < n (Horner; fp_core.py uses an NTT for the same
     values). enc_row_entry: lifted to the field, an entry is xrs_enc, the
     evaluation the verifier uses. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith.
From Crypto Require Import LogDer Negacyclic ReedSolomon. From Examples Require Import ConcreteField ExecField ExecHash ExecOpen ExecVerify.
Import ListNotations.
Local Open Scope list_scope.

(* ---------------------------------------------------------------------- *)
(* Merkle trees *)

Fixpoint up (l : list (list Z)) : list (list Z) :=
  match l with
  | a :: b :: r => sha256 (a ++ b) :: up r
  | _ => []
  end.

Fixpoint mroot (d : nat) (l : list (list Z)) : list Z :=
  match d with
  | O => nth 0 l []
  | S d' => mroot d' (up l)
  end.

Definition sib (j : nat) : nat := if Nat.even j then S j else pred j.

Fixpoint mpath (d : nat) (l : list (list Z)) (j : nat) : list (list Z) :=
  match d with
  | O => []
  | S d' => nth (sib j) l [] :: mpath d' (up l) (Nat.div2 j)
  end.

Lemma up_length : forall l k, List.length l = (2 * k)%nat -> List.length (up l) = k.
Proof.
  fix ih 1. intros l k h. destruct l as [| a [| b r]]; cbn in h |- *; try lia.
  destruct k as [| k]; [lia |]. f_equal. apply ih. lia.
Qed.

Lemma up_nth : forall l k j, List.length l = (2 * k)%nat -> (j < k)%nat ->
  nth j (up l) [] = sha256 (nth (2 * j) l [] ++ nth (2 * j + 1) l []).
Proof.
  fix ih 1. intros l k j h hj. destruct l as [| a [| b r]]; cbn in h; try lia.
  destruct j as [| j]; [reflexivity |].
  destruct k as [| k]; [lia |]. cbn [up nth].
  replace (2 * S j)%nat with (S (S (2 * j))) by lia. replace (S (S (2 * j)) + 1)%nat with (S (S (2 * j + 1))) by lia.
  cbn [nth]. apply (ih r k j); lia.
Qed.

Lemma Z_even_nat : forall j : nat, Z.even (Z.of_nat j) = Nat.even j.
Proof.
  induction j as [| j ih]; [reflexivity |].
  rewrite Nat2Z.inj_succ, Z.even_succ, Nat.even_succ, <-Z.negb_even, <-Nat.negb_even, ih. reflexivity.
Qed.

Lemma Z_shiftr_nat : forall j : nat, Z.shiftr (Z.of_nat j) 1 = Z.of_nat (Nat.div2 j).
Proof. intro j. rewrite <-Z.div2_spec, Nat2Z.inj_div2. reflexivity. Qed.

Theorem root_from_path : forall d l j, List.length l = (2 ^ d)%nat -> (j < 2 ^ d)%nat ->
  root_from (nth j l []) (Z.of_nat j) (mpath d l j) = mroot d l.
Proof.
  induction d as [| d ih]; intros l j hl hj.
  + cbn in hj. assert (j = 0%nat) by lia. subst j. reflexivity.
  + cbn [mpath mroot ExecHash.root_from]. rewrite Z_even_nat, Z_shiftr_nat.
    assert (hk : List.length l = (2 * 2 ^ d)%nat) by (rewrite hl; cbn [Nat.pow]; lia).
    assert (hu : List.length (up l) = (2 ^ d)%nat) by (apply up_length; exact hk).
    assert (hj2 : (Nat.div2 j < 2 ^ d)%nat)
      by (rewrite Nat.div2_div; apply Nat.Div0.div_lt_upper_bound; cbn [Nat.pow] in hj; lia).
    rewrite <-(ih (up l) (Nat.div2 j) hu hj2).
    f_equal. rewrite (up_nth l (2 ^ d) (Nat.div2 j) hk hj2). unfold sib.
    destruct (Nat.Even_or_Odd j) as [[k ->] | [k ->]].
    - rewrite Nat.even_mul. cbn [Nat.even orb]. rewrite Nat.div2_double.
      replace (S (2 * k)) with (2 * k + 1)%nat by lia. reflexivity.
    - rewrite Nat.even_add, Nat.even_mul. cbn [Nat.even orb negb Bool.eqb].
      replace (2 * k + 1)%nat with (S (2 * k)) by lia. rewrite Nat.div2_succ_double. cbn [pred].
      replace (S (2 * k)) with (2 * k + 1)%nat by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* encoding a row of integers mod q *)

(* elements of the base field Z_q: second coordinate 0 *)
Definition isbase (x : xf) : Prop := snd x = 0%Z.

Lemma base_add : forall x y, isbase x -> isbase y -> isbase (xadd x y).
Proof. intros [a b] [c d] hx hy. unfold isbase in *. cbn in *. subst. reflexivity. Qed.

Lemma base_mul : forall x y, isbase x -> isbase y -> isbase (xmul x y).
Proof. intros [a b] [c d] hx hy. unfold isbase in *. cbn in *. subst. rewrite !Z.mul_0_r, Z.mul_0_l. reflexivity. Qed.

Lemma base_pw : forall x k, isbase x -> isbase (xpw x k).
Proof.
  intros x k hx. unfold xpw. generalize k at 1. intro fuel. revert k. induction fuel as [| f ih]; intro k; [reflexivity |].
  cbn [xpw_f]. destruct (Nat.eqb k 0); [reflexivity |].
  destruct (Nat.eqb _ 0); repeat apply base_mul; try apply ih; assumption.
Qed.

Lemma base_eval : forall p x, Forall isbase p -> isbase x -> isbase (xeval p x).
Proof.
  intros p x hp hx; induction hp as [| c p hc hp ih]; [reflexivity |].
  cbn [xeval]. apply base_add; [exact hc | apply base_mul; assumption].
Qed.

Lemma base_bx : forall z, isbase (bx z).
Proof. reflexivity. Qed.

(* the codeword of a row, as integers mod q *)
Definition xenc_row (om : Z) (n : nat) (msg : list Z) : list Z :=
  map (fun j => fst (xrs_enc (bx om) (map bx msg) j)) (seq 0 n).

Theorem enc_row_entry : forall om n msg j, (j < n)%nat ->
  bx (nth j (xenc_row om n msg) 0%Z) = xrs_enc (bx om) (map bx msg) j.
Proof.
  intros om n msg j hj. unfold xenc_row.
  rewrite (nth_indep _ 0%Z (fst (xrs_enc (bx om) (map bx msg) 0))) by (rewrite length_map, length_seq; exact hj).
  rewrite (map_nth (fun j => fst (xrs_enc (bx om) (map bx msg) j))), seq_nth by exact hj.
  cbv beta. rewrite Nat.add_0_l.
  assert (hb : isbase (xrs_enc (bx om) (map bx msg) j)).
  { unfold xrs_enc. apply base_eval; [| apply base_pw, base_bx].
    apply Forall_map, Forall_forall. intros; apply base_bx. }
  set (v := xrs_enc (bx om) (map bx msg) j) in *. clearbody v.
  destruct v as [u w]. unfold isbase in hb. cbn in hb |- *. subst w. reflexivity.
Qed.
