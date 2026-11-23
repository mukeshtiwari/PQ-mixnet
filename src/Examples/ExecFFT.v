(* The radix-2 NTT and the Horner encoding, early in the dependency order so that the verifier's
   opening checks (ExecOpen.v) can encode whole vectors at once.

     zenc_horner om n msg   msg(om^j) mod q, j < n, by Horner (the specification);
     zfft d w p             the same values by a recursive radix-2 transform when n = 2^d, w^n = 1;
     zenc                   zfft when zntt_ok, otherwise Horner.

   The definitions moved here from ExecProveBase.v (which re-exports this file); ExecNtt.v keeps the
   prover-side statements. The lemmas below are the same as in ExecNtt.v under the names xfft_*,
   for the base-field embedding bz z = (z, 0). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Negacyclic. From Examples Require Import ConcreteField ExecField.
Import ListNotations.

Add Field fieldF2fft : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Open Scope Z_scope.

Fixpoint zhorner (p : list Z) (x : Z) : Z :=
  match p with
  | [] => 0
  | c :: p' => (c + x * zhorner p' x) mod Q
  end.

Fixpoint zpows (x : Z) (n : nat) (acc : Z) : list Z :=
  match n with
  | O => []
  | S n' => acc :: zpows x n' ((acc * x) mod Q)
  end.

(* the codeword by Horner evaluation at om^0, .., om^(n-1): the specification *)
Definition zenc_horner (om : Z) (n : nat) (msg : list Z) : list Z := map (zhorner msg) (zpows om n 1).

(* the same values by a radix-2 NTT (ExecNtt.v: zenc_spec); used when n = 2^d and om^n = 1 mod q *)
Fixpoint evens (l : list Z) : list Z := match l with [] => [] | a :: r => a :: odds r end
with odds (l : list Z) : list Z := match l with [] => [] | _ :: r => evens r end.

Fixpoint zfft (d : nat) (w : Z) (p : list Z) : list Z :=
  match d with
  | O => [zhorner p 1]
  | S d' =>
      let w2 := ((w * w) mod Q)%Z in
      let e := zfft d' w2 (evens p) in
      let o := zfft d' w2 (odds p) in
      map (fun t => ((fst (fst t) + snd t * snd (fst t)) mod Q)%Z) (combine (combine (e ++ e) (o ++ o)) (zpows w (2 ^ S d') 1))
  end.

Definition zntt_ok (om : Z) (n : nat) : bool :=
  Nat.eqb (2 ^ Nat.log2 n) n && Z.eqb ((last (zpows om n 1) 1 * om) mod Q)%Z 1.

Definition zenc (om : Z) (n : nat) (msg : list Z) : list Z :=
  if zntt_ok om n then zfft (Nat.log2 n) om msg else zenc_horner om n msg.


Local Close Scope Z_scope.

Local Notation peval := (@eval Fq2 fzero fadd fmul).
Local Notation pw2 := (@pw Fq2 fone fmul).
Definition bz (z : Z) : xf := (z, 0%Z).
Local Notation PF := (fun l : list Z => map to_F (map bz l)).

Lemma xfft_bz_mod : forall z, to_F (bz (z mod Q)) = to_F (bz z).
Proof. intro z. unfold to_F, bz. cbn [fst snd]. rewrite zq_of_mod. reflexivity. Qed.

Lemma xfft_bz0 : to_F (bz 0%Z) = fzero.
Proof. unfold to_F, bz. cbn [fst snd]. rewrite zq_of_0. reflexivity. Qed.

Lemma xfft_to_F_bx_add : forall x y, to_F (bz (x + y)) = fadd (to_F (bz x)) (to_F (bz y)).
Proof.
  intros x y. rewrite <-to_F_add. unfold to_F, xadd, bz. cbn [fst snd].
  rewrite zq_of_mod. replace (0 + 0)%Z with 0%Z by ring. rewrite Zmod_0_l. reflexivity.
Qed.

Lemma xfft_to_F_bx_mul : forall x y, to_F (bz (x * y)) = fmul (to_F (bz x)) (to_F (bz y)).
Proof.
  intros x y. rewrite <-to_F_mul. unfold to_F, xmul, bz. cbn [fst snd].
  replace (x * y + 3 * 0 * 0)%Z with (x * y)%Z by ring. replace (x * 0 + 0 * y)%Z with 0%Z by ring.
  rewrite zq_of_mod, Zmod_0_l. reflexivity.
Qed.

Lemma xfft_to_F_bx1 : to_F (bz 1%Z) = fone.
Proof. unfold to_F, bz. cbn [fst snd]. rewrite zq_of_1, zq_of_0. reflexivity. Qed.

Lemma xfft_bx_inj : forall x y, (0 <= x < Q)%Z -> (0 <= y < Q)%Z -> to_F (bz x) = to_F (bz y) -> x = y.
Proof.
  intros x y hx hy e. assert (h : bz x = bz y) by (apply to_F_inj; [split; cbn; lia.. | exact e]).
  injection h as h. exact h.
Qed.

Lemma xfft_Q_pos_q : (0 < Q)%Z.
Proof. unfold Q. lia. Qed.

Lemma xfft_zhorner_range : forall p x, (0 <= zhorner p x < Q)%Z.
Proof.
  intros [| c p] x; cbn [zhorner]; [pose proof xfft_Q_pos_q; lia |]. apply Z.mod_pos_bound, xfft_Q_pos_q.
Qed.

Lemma xfft_zhorner_F : forall p x, to_F (bz (zhorner p x)) = peval (PF p) (to_F (bz x)).
Proof.
  induction p as [| c p ih]; intro x; [exact xfft_bz0 |].
  cbn [zhorner map PolyRoots.eval]. rewrite xfft_bz_mod, xfft_to_F_bx_add, xfft_to_F_bx_mul, ih. reflexivity.
Qed.

Lemma xfft_zpows_F : forall n x acc j, (j < n)%nat ->
  to_F (bz (nth j (zpows x n acc) 0%Z)) = fmul (to_F (bz acc)) (pw2 (to_F (bz x)) j).
Proof.
  induction n as [| n ih]; intros x acc j hj; [lia |].
  cbn [zpows]. destruct j as [| j]; cbn [nth Negacyclic.pw].
  + field.
  + rewrite ih by lia. rewrite xfft_bz_mod, xfft_to_F_bx_mul. field.
Qed.

Lemma xfft_zpows_len : forall x n acc, List.length (zpows x n acc) = n.
Proof. intros x n; induction n as [| n ih]; intro acc; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

Lemma xfft_nth_map_ind : forall {A B : Type} (f : A -> B) (l : list A) i d d', (i < List.length l)%nat ->
  nth i (map f l) d' = f (nth i l d).
Proof. intros A B f l i d d' h. rewrite (nth_indep _ d' (f d)) by (rewrite length_map; exact h). apply map_nth. Qed.

(* ---------------------------------------------------------------------- *)
(* powers *)

Lemma xfft_pw_add : forall x a b, pw2 x (a + b) = fmul (pw2 x a) (pw2 x b).
Proof. intros x a b. induction a as [| a ih]; cbn [Nat.add Negacyclic.pw]; [field | rewrite ih; field]. Qed.

Lemma xfft_pw_sq : forall x k, pw2 (fmul x x) k = pw2 x (2 * k).
Proof.
  intros x k. induction k as [| k ih]; [reflexivity |].
  replace (2 * S k)%nat with (S (S (2 * k))) by lia. cbn [Negacyclic.pw]. rewrite ih. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the split into even and odd coefficients *)

Lemma xfft_peval_split : forall l x,
  peval (PF l) x = fadd (peval (PF (evens l)) (fmul x x)) (fmul x (peval (PF (odds l)) (fmul x x))).
Proof.
  induction l as [| a r ih]; intro x; cbn [evens odds map PolyRoots.eval]; [field |].
  rewrite ih. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the transform *)

Lemma xfft_zfft_length : forall d w p, List.length (zfft d w p) = (2 ^ d)%nat.
Proof.
  induction d as [| d ih]; intros w p; [reflexivity |].
  cbn [zfft]. rewrite length_map, !length_combine, !length_app, !ih, xfft_zpows_len. cbn [Nat.pow]. lia.
Qed.

Lemma xfft_zfft_range : forall d w p, Forall (fun z => (0 <= z < Q)%Z) (zfft d w p).
Proof.
  induction d as [| d ih]; intros w p; cbn [zfft].
  + constructor; [apply xfft_zhorner_range | constructor].
  + apply Forall_map, Forall_forall. intros t _. apply Z.mod_pos_bound, xfft_Q_pos_q.
Qed.

Theorem xfft_zfft_F : forall d w p, pw2 (to_F (bz w)) (2 ^ d) = fone ->
  forall j, (j < 2 ^ d)%nat -> to_F (bz (nth j (zfft d w p) 0%Z)) = peval (PF p) (pw2 (to_F (bz w)) j).
Proof.
  induction d as [| d ih]; intros w p hw j hj.
  - cbn in hj. replace j with 0%nat by lia. cbn [zfft nth Negacyclic.pw]. rewrite xfft_zhorner_F, xfft_to_F_bx1. reflexivity.
  - cbn [zfft]. set (w2 := ((w * w) mod Q)%Z).
    assert (hw2 : to_F (bz w2) = fmul (to_F (bz w)) (to_F (bz w))) by (unfold w2; rewrite xfft_bz_mod, xfft_to_F_bx_mul; reflexivity).
    assert (hsub : pw2 (to_F (bz w2)) (2 ^ d) = fone).
    { rewrite hw2, xfft_pw_sq. replace (2 * 2 ^ d)%nat with (2 ^ S d)%nat by (cbn [Nat.pow]; lia). exact hw. }
    set (e := zfft d w2 (evens p)). set (o := zfft d w2 (odds p)).
    assert (he : List.length e = (2 ^ d)%nat) by apply xfft_zfft_length.
    assert (ho : List.length o = (2 ^ d)%nat) by apply xfft_zfft_length.
    set (j0 := (j mod 2 ^ d)%nat).
    assert (hpos : (0 < 2 ^ d)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    assert (hj0 : (j0 < 2 ^ d)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (happ : forall l : list Z, List.length l = (2 ^ d)%nat -> nth j (l ++ l) 0%Z = nth j0 l 0%Z).
    { intros l hl. cbn [Nat.pow] in hj. destruct (Nat.ltb_spec j (2 ^ d)) as [h | h].
      + rewrite app_nth1 by lia. unfold j0. rewrite Nat.mod_small by exact h. reflexivity.
      + rewrite app_nth2 by lia. rewrite hl. unfold j0.
        replace j with ((j - 2 ^ d) + 1 * 2 ^ d)%nat at 2 by lia. rewrite Nat.Div0.mod_add, Nat.mod_small by lia.
        reflexivity. }
    assert (hlen : List.length (combine (combine (e ++ e) (o ++ o)) (zpows w (2 ^ S d) 1)) = (2 ^ S d)%nat).
    { rewrite !length_combine, !length_app, he, ho, xfft_zpows_len. cbn [Nat.pow]. lia. }
    rewrite (xfft_nth_map_ind _ _ j (0%Z, 0%Z, 0%Z)) by (rewrite hlen; exact hj).
    rewrite !combine_nth by (rewrite ?length_combine, ?length_app, ?he, ?ho, ?xfft_zpows_len; cbn [Nat.pow]; lia).
    cbn [fst snd]. rewrite xfft_bz_mod, xfft_to_F_bx_add, xfft_to_F_bx_mul.
    rewrite (happ e he), (happ o ho), xfft_zpows_F by exact hj. rewrite xfft_to_F_bx1.
    unfold e, o. rewrite !(ih w2) by assumption.
    rewrite (xfft_peval_split p).
    assert (hsq : fmul (pw2 (to_F (bz w)) j) (pw2 (to_F (bz w)) j) = pw2 (to_F (bz w2)) j0).
    { rewrite hw2, xfft_pw_sq, <-xfft_pw_add.
      cbn [Nat.pow] in hw, hj. destruct (Nat.ltb_spec j (2 ^ d)) as [h | h].
      + unfold j0. rewrite Nat.mod_small by exact h. f_equal. lia.
      + unfold j0. replace j with ((j - 2 ^ d) + 1 * 2 ^ d)%nat at 3 by lia. rewrite Nat.Div0.mod_add, Nat.mod_small by lia.
        replace (j + j)%nat with (2 * (j - 2 ^ d) + 2 * 2 ^ d)%nat by lia.
        rewrite xfft_pw_add, hw. field. }
    rewrite hsq. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the encoding *)

Lemma xfft_last_nth_q : forall {A : Type} (l : list A) d, last l d = nth (List.length l - 1) l d.
Proof.
  intros A l d. induction l as [| x l ih]; [reflexivity |].
  destruct l as [| y l]; [reflexivity |]. change (last (x :: y :: l) d) with (last (y :: l) d). rewrite ih.
  change (List.length (x :: y :: l)) with (S (S (List.length l))). change (List.length (y :: l)) with (S (List.length l)).
  replace (S (S (List.length l)) - 1)%nat with (S (S (List.length l) - 1)) by lia. reflexivity.
Qed.

Theorem xfft_zenc_spec : forall om n msg, zenc om n msg = zenc_horner om n msg.
Proof.
  intros om n msg. unfold zenc. destruct (zntt_ok om n) eqn:hk; [| reflexivity].
  unfold zntt_ok in hk. apply andb_true_iff in hk. destruct hk as [hn hq].
  apply Nat.eqb_eq in hn. apply Z.eqb_eq in hq.
  set (d := Nat.log2 n) in *.
  assert (hpos : (0 < n)%nat) by (rewrite <-hn; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (hw : pw2 (to_F (bz om)) (2 ^ d) = fone).
  { apply (f_equal (fun z => to_F (bz z))) in hq. rewrite xfft_bz_mod, xfft_to_F_bx_mul, xfft_to_F_bx1 in hq.
    rewrite xfft_last_nth_q, xfft_zpows_len in hq. rewrite (nth_indep _ 1%Z 0%Z) in hq by (rewrite xfft_zpows_len; lia).
    rewrite xfft_zpows_F in hq by lia. rewrite xfft_to_F_bx1 in hq.
    rewrite hn. etransitivity; [| exact hq]. replace n with (S (n - 1)) at 1 by lia. cbn [Negacyclic.pw]. field. }
  apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - rewrite xfft_zfft_length. unfold zenc_horner. rewrite length_map, xfft_zpows_len. exact hn.
  - intros j hj. rewrite xfft_zfft_length in hj. apply xfft_bx_inj.
    + pose proof (xfft_zfft_range d om msg) as hr. rewrite Forall_forall in hr. apply hr, nth_In. rewrite xfft_zfft_length. exact hj.
    + unfold zenc_horner. rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, xfft_zpows_len; lia).
      rewrite map_nth. apply xfft_zhorner_range.
    + rewrite (xfft_zfft_F d om msg hw j hj). unfold zenc_horner.
      rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, xfft_zpows_len; lia).
      rewrite map_nth, xfft_zhorner_F, xfft_zpows_F by lia. rewrite xfft_to_F_bx1. f_equal. field.
Qed.

Lemma xfft_zenc_length : forall om n msg, List.length (zenc om n msg) = n.
Proof. intros. rewrite xfft_zenc_spec. unfold zenc_horner. rewrite length_map. apply xfft_zpows_len. Qed.

Lemma xfft_zenc_F : forall om n msg j, (j < n)%nat ->
  to_F (bz (nth j (zenc om n msg) 0%Z)) = peval (PF msg) (pw2 (to_F (bz om)) j).
Proof.
  intros om n msg j hj. rewrite xfft_zenc_spec. unfold zenc_horner.
  rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, xfft_zpows_len; exact hj).
  rewrite map_nth, xfft_zhorner_F, xfft_zpows_F by exact hj. rewrite xfft_to_F_bx1. f_equal. field.
Qed.
