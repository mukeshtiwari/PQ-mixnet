(* Executable field arithmetic, without proofs inside the data, and its
   refinement to the field Fq2 of ConcreteField.v.

   An element of GF(q^2) is a pair of integers (a, b) standing for
   a + b t, t^2 = 3. The functions are those of fp_core.py:

     xadd, xsub, xneg, xmul, xinv, xint      fadd, fsub, fneg, fmul, finv, fint
     xeq_eval, xzval                         eq_eval, zval

   Every function returns reduced pairs (both components in [0, q)).

   to_F maps a pair to Fq2, reducing mod q. Theorems to_F_add, .., to_F_inv,
   to_F_eq_eval, to_F_zval: the executable functions compute the field
   operations, and the functions eqp and Zp of the soundness proofs.
   to_F_inj: on reduced pairs to_F is injective, so comparing pairs with
   xeqb decides equality in the field. *)

From Stdlib Require Import Utf8 ZArith Zpow_facts Znumtheory List Lia Bool.
From Algebra Require Import Hierarchy.
From Utility Require Import Functions Zpstar.
From Crypto Require Import LogDer Mle MaskedExt. From Examples Require Import ConcreteField.
Import ListNotations.

Local Open Scope Z_scope.

Definition xf : Type := (Z * Z)%type.

Definition xzero : xf := (0, 0).
Definition xone : xf := (1, 0).
Definition xint (c : Z) : xf := (c mod Q, 0).
Definition xadd (x y : xf) : xf := ((fst x + fst y) mod Q, (snd x + snd y) mod Q).
Definition xsub (x y : xf) : xf := ((fst x - fst y) mod Q, (snd x - snd y) mod Q).
Definition xneg (x : xf) : xf := ((- fst x) mod Q, (- snd x) mod Q).
Definition xmul (x y : xf) : xf :=
  ((fst x * fst y + 3 * snd x * snd y) mod Q, (fst x * snd y + snd x * fst y) mod Q).
Definition xinv (x : xf) : xf :=
  let d := Zpow_mod ((fst x * fst x - 3 * snd x * snd x) mod Q) (Q - 2) Q in
  ((fst x * d) mod Q, ((- snd x) * d) mod Q).
Definition xeqb (x y : xf) : bool := Z.eqb (fst x) (fst y) && Z.eqb (snd x) (snd y).

Definition reduced (x : xf) : Prop := (0 <= fst x < Q) /\ (0 <= snd x < Q).

Fixpoint xeq_eval (r s : list xf) : xf :=
  match r, s with
  | a :: r', b :: s' => xmul (xadd (xmul a b) (xmul (xsub xone a) (xsub xone b))) (xeq_eval r' s')
  | _, _ => xone
  end.

Fixpoint xzval (r : list xf) : xf :=
  match r with
  | [] => xone
  | x :: r' => xmul (xmul x (xsub xone x)) (xzval r')
  end.

(* ---------------------------------------------------------------------- *)
(* zq_of is a ring homomorphism Z -> Zq *)

Lemma Q_nz : Q <> 0.
Proof. intro h. vm_compute in h. discriminate. Qed.

Lemma zq_of_mod : forall z, zq_of (z mod Q) = zq_of z.
Proof. intro z. apply zq_eq. cbn [zq_of Zpfield.v]. apply Zmod_mod. Qed.

Lemma zq_of_add : forall x y, zq_of (x + y) = qadd (zq_of x) (zq_of y).
Proof. intros x y. apply zq_eq. cbn [zq_of qadd Zpfield.zp_add Zpfield.v]. apply Zplus_mod. Qed.

Lemma zq_of_sub : forall x y, zq_of (x - y) = qsub (zq_of x) (zq_of y).
Proof. intros x y. apply zq_eq. cbn [zq_of qsub Zpfield.zp_sub Zpfield.v]. apply Zminus_mod. Qed.

Lemma zq_of_mul : forall x y, zq_of (x * y) = qmul (zq_of x) (zq_of y).
Proof. intros x y. apply zq_eq. cbn [zq_of qmul Zpfield.zp_mul Zpfield.v]. apply Zmult_mod. Qed.

Lemma zq_of_opp : forall x, zq_of (- x) = qopp (zq_of x).
Proof.
  intro x. apply zq_eq.
  cbn [zq_of qopp Zpfield.zp_opp Zpfield.zp_sub Zpfield.zero Zpfield.v].
  rewrite Zminus_mod_idemp_r. reflexivity.
Qed.

Lemma zq_of_0 : zq_of 0 = qzero.
Proof. apply zq_eq. vm_compute. reflexivity. Qed.

Lemma zq_of_1 : zq_of 1 = qone.
Proof. apply zq_eq. vm_compute. reflexivity. Qed.

Lemma zq_of_3 : zq_of 3 = qthree.
Proof. apply zq_eq. vm_compute. reflexivity. Qed.

Lemma zq_of_inv : forall z, zq_of (Zpow_mod (z mod Q) (Q - 2) Q) = qinv (zq_of z).
Proof.
  intro z. apply zq_eq. cbn [zq_of qinv Zpfield.zp_inv Zpfield.v].
  assert (h0 : 0 <= z mod Q) by (apply Z.mod_pos_bound; exact Q_pos).
  assert (h1 : 0 <= Q - 2) by (vm_compute; discriminate).
  assert (h2 : 0 <= Q) by (vm_compute; discriminate).
  rewrite (zmod_nmod (Z.to_N (Q - 2)) (Z.to_N (z mod Q)) (Z.to_N Q)) by (rewrite Z2N.id by exact h2; exact Q_prime).
  rewrite !Z2N.id by assumption. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Refinement *)

Definition to_F (x : xf) : Fq2 := (zq_of (fst x), zq_of (snd x)).

Lemma to_F_zero : to_F xzero = fzero.
Proof. unfold to_F, xzero, fzero, ezero. cbn [fst snd]. rewrite zq_of_0. reflexivity. Qed.

Lemma to_F_one : to_F xone = fone.
Proof. unfold to_F, xone, fone, eone. cbn [fst snd]. rewrite zq_of_0, zq_of_1. reflexivity. Qed.

Theorem to_F_add : forall x y, to_F (xadd x y) = fadd (to_F x) (to_F y).
Proof.
  intros x y. unfold to_F, xadd, fadd, eadd. cbn [fst snd]. rewrite !zq_of_mod, !zq_of_add. reflexivity.
Qed.

Theorem to_F_sub : forall x y, to_F (xsub x y) = fsub (to_F x) (to_F y).
Proof.
  intros x y. unfold to_F, xsub, fsub, esub. cbn [fst snd]. rewrite !zq_of_mod, !zq_of_sub. reflexivity.
Qed.

Theorem to_F_neg : forall x, to_F (xneg x) = fopp (to_F x).
Proof.
  intro x. unfold to_F, xneg, fopp, eopp. cbn [fst snd]. rewrite !zq_of_mod, !zq_of_opp. reflexivity.
Qed.

Theorem to_F_mul : forall x y, to_F (xmul x y) = fmul (to_F x) (to_F y).
Proof.
  intros x y. unfold to_F, xmul, fmul, emul. cbn [fst snd].
  rewrite !zq_of_mod, !zq_of_add, !zq_of_mul, zq_of_3. reflexivity.
Qed.

Theorem to_F_inv : forall x, to_F (xinv x) = finv (to_F x).
Proof.
  intro x. unfold to_F, xinv, finv, einv, enorm. cbn [fst snd].
  rewrite !zq_of_mod, !zq_of_mul, zq_of_opp, zq_of_inv, zq_of_sub, !zq_of_mul, zq_of_3. reflexivity.
Qed.

Theorem to_F_inj : forall x y, reduced x -> reduced y -> to_F x = to_F y -> x = y.
Proof.
  intros [a b] [c d] [h1 h2] [h3 h4] e. cbn [fst snd] in *. unfold to_F in e. cbn [fst snd] in e.
  injection e as e1 e2.
  rewrite !Z.mod_small in e1, e2 by assumption. subst. reflexivity.
Qed.

Theorem xeqb_spec : forall x y, reduced x -> reduced y -> (xeqb x y = true <-> to_F x = to_F y).
Proof.
  intros x y hx hy. unfold xeqb. rewrite andb_true_iff, !Z.eqb_eq. split.
  + intros [e1 e2]. destruct x, y. cbn in e1, e2. subst. reflexivity.
  + intro e. apply (to_F_inj x y hx hy) in e. subst. split; reflexivity.
Qed.

Lemma xadd_reduced : forall x y, reduced (xadd x y).
Proof. intros x y. split; apply Z.mod_pos_bound; exact Q_pos. Qed.
Lemma xsub_reduced : forall x y, reduced (xsub x y).
Proof. intros x y. split; apply Z.mod_pos_bound; exact Q_pos. Qed.
Lemma xmul_reduced : forall x y, reduced (xmul x y).
Proof. intros x y. split; apply Z.mod_pos_bound; exact Q_pos. Qed.
Lemma xinv_reduced : forall x, reduced (xinv x).
Proof. intro x. split; apply Z.mod_pos_bound; exact Q_pos. Qed.

Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).

Theorem to_F_eq_eval : forall r s, to_F (xeq_eval r s) = eqp2 (map to_F r) (map to_F s).
Proof.
  induction r as [| a r ih]; intro s; [exact to_F_one |].
  destruct s as [| b s]; [exact to_F_one |].
  cbn [xeq_eval map Mle.eqp].
  rewrite to_F_mul, to_F_add, !to_F_mul, !to_F_sub, to_F_one, ih. reflexivity.
Qed.

Theorem to_F_zval : forall r, to_F (xzval r) = Zp2 (map to_F r).
Proof.
  induction r as [| x r ih]; [exact to_F_one |].
  cbn [xzval map MaskedExt.Zp]. rewrite !to_F_mul, to_F_sub, to_F_one, ih. reflexivity.
Qed.
