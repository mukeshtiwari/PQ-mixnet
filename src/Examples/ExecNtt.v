(* The row encoding by a radix-2 NTT gives the codeword of the specification.

   zenc_horner om n msg is the list msg(om^j) mod q, j < n, by Horner
   evaluation (O(n * |msg|) operations). zenc computes it by the recursive
   radix-2 transform zfft when n = 2^d and om^n = 1 mod q (zntt_ok), and
   falls back to Horner otherwise.

     zfft_F     entry j of zfft d w p is p(w^j), for j < 2^d, if w^(2^d) = 1:
                p(x) = p_even(x^2) + x p_odd(x^2), and (w^2)^j depends only on
                j mod 2^(d-1);
     zenc_spec  zenc = zenc_horner (no hypothesis), so every theorem about
                the prover holds for the faster code.

   The field-level facts about Horner evaluation and the powers of om
   (zhorner_F, zpows_F, zenc_F) live here too. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Negacyclic. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecVerify ExecProveBase ExecRows.
Import ListNotations.

Add Field fieldF2n : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation peval := (@eval Fq2 fzero fadd fmul).
Local Notation pw2 := (@pw Fq2 fone fmul).
Local Notation PF := (fun l : list Z => map to_F (map bx l)).

(* ---------------------------------------------------------------------- *)
(* integers mod q as base-field elements *)

Lemma to_F_bx_mod' : forall z, to_F (bx (z mod Q)) = to_F (bx z).
Proof. intro z. exact (to_F_bx_zm z). Qed.

Lemma to_F_bx_add : forall x y, to_F (bx (x + y)) = fadd (to_F (bx x)) (to_F (bx y)).
Proof.
  intros x y. rewrite <-to_F_add. unfold to_F, xadd, bx. cbn [fst snd].
  rewrite zq_of_mod. replace (0 + 0)%Z with 0%Z by ring. rewrite Zmod_0_l. reflexivity.
Qed.

Lemma to_F_bx_mul : forall x y, to_F (bx (x * y)) = fmul (to_F (bx x)) (to_F (bx y)).
Proof.
  intros x y. rewrite <-to_F_mul. unfold to_F, xmul, bx. cbn [fst snd].
  replace (x * y + 3 * 0 * 0)%Z with (x * y)%Z by ring. replace (x * 0 + 0 * y)%Z with 0%Z by ring.
  rewrite zq_of_mod, Zmod_0_l. reflexivity.
Qed.

Lemma to_F_bx1 : to_F (bx 1%Z) = fone.
Proof. unfold to_F, bx. cbn [fst snd]. rewrite zq_of_1, zq_of_0. reflexivity. Qed.

Lemma bx_inj : forall x y, (0 <= x < Q)%Z -> (0 <= y < Q)%Z -> to_F (bx x) = to_F (bx y) -> x = y.
Proof.
  intros x y hx hy e. assert (h : bx x = bx y) by (apply to_F_inj; [split; cbn; lia.. | exact e]).
  injection h as h. exact h.
Qed.

Lemma Q_pos' : (0 < Q)%Z.
Proof. unfold Q. lia. Qed.

Lemma zhorner_range : forall p x, (0 <= zhorner p x < Q)%Z.
Proof.
  intros [| c p] x; cbn [zhorner]; [pose proof Q_pos'; lia |]. apply Z.mod_pos_bound, Q_pos'.
Qed.

Lemma zhorner_F : forall p x, to_F (bx (zhorner p x)) = peval (PF p) (to_F (bx x)).
Proof.
  induction p as [| c p ih]; intro x; [exact to_F_bx0 |].
  cbn [zhorner map PolyRoots.eval]. rewrite to_F_bx_mod', to_F_bx_add, to_F_bx_mul, ih. reflexivity.
Qed.

Lemma zpows_F : forall n x acc j, (j < n)%nat ->
  to_F (bx (nth j (zpows x n acc) 0%Z)) = fmul (to_F (bx acc)) (pw2 (to_F (bx x)) j).
Proof.
  induction n as [| n ih]; intros x acc j hj; [lia |].
  cbn [zpows]. destruct j as [| j]; cbn [nth Negacyclic.pw].
  + field.
  + rewrite ih by lia. rewrite to_F_bx_mod', to_F_bx_mul. field.
Qed.

Lemma zpows_len : forall x n acc, List.length (zpows x n acc) = n.
Proof. intros x n; induction n as [| n ih]; intro acc; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

Lemma nth_map_ind : forall {A B : Type} (f : A -> B) (l : list A) i d d', (i < List.length l)%nat ->
  nth i (map f l) d' = f (nth i l d).
Proof. intros A B f l i d d' h. rewrite (nth_indep _ d' (f d)) by (rewrite length_map; exact h). apply map_nth. Qed.

(* ---------------------------------------------------------------------- *)
(* powers *)

Lemma pw_add : forall x a b, pw2 x (a + b) = fmul (pw2 x a) (pw2 x b).
Proof. intros x a b. induction a as [| a ih]; cbn [Nat.add Negacyclic.pw]; [field | rewrite ih; field]. Qed.

Lemma pw_sq : forall x k, pw2 (fmul x x) k = pw2 x (2 * k).
Proof.
  intros x k. induction k as [| k ih]; [reflexivity |].
  replace (2 * S k)%nat with (S (S (2 * k))) by lia. cbn [Negacyclic.pw]. rewrite ih. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the split into even and odd coefficients *)

Lemma peval_split : forall l x,
  peval (PF l) x = fadd (peval (PF (evens l)) (fmul x x)) (fmul x (peval (PF (odds l)) (fmul x x))).
Proof.
  induction l as [| a r ih]; intro x; cbn [evens odds map PolyRoots.eval]; [field |].
  rewrite ih. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the transform *)

Lemma zfft_length : forall d w p, List.length (zfft d w p) = (2 ^ d)%nat.
Proof.
  induction d as [| d ih]; intros w p; [reflexivity |].
  cbn [zfft]. rewrite length_map, !length_combine, !length_app, !ih, zpows_len. cbn [Nat.pow]. lia.
Qed.

Lemma zfft_range : forall d w p, Forall (fun z => (0 <= z < Q)%Z) (zfft d w p).
Proof.
  induction d as [| d ih]; intros w p; cbn [zfft].
  + constructor; [apply zhorner_range | constructor].
  + apply Forall_map, Forall_forall. intros t _. apply Z.mod_pos_bound, Q_pos'.
Qed.

Theorem zfft_F : forall d w p, pw2 (to_F (bx w)) (2 ^ d) = fone ->
  forall j, (j < 2 ^ d)%nat -> to_F (bx (nth j (zfft d w p) 0%Z)) = peval (PF p) (pw2 (to_F (bx w)) j).
Proof.
  induction d as [| d ih]; intros w p hw j hj.
  - cbn in hj. replace j with 0%nat by lia. cbn [zfft nth Negacyclic.pw]. rewrite zhorner_F, to_F_bx1. reflexivity.
  - cbn [zfft]. set (w2 := ((w * w) mod Q)%Z).
    assert (hw2 : to_F (bx w2) = fmul (to_F (bx w)) (to_F (bx w))) by (unfold w2; rewrite to_F_bx_mod', to_F_bx_mul; reflexivity).
    assert (hsub : pw2 (to_F (bx w2)) (2 ^ d) = fone).
    { rewrite hw2, pw_sq. replace (2 * 2 ^ d)%nat with (2 ^ S d)%nat by (cbn [Nat.pow]; lia). exact hw. }
    set (e := zfft d w2 (evens p)). set (o := zfft d w2 (odds p)).
    assert (he : List.length e = (2 ^ d)%nat) by apply zfft_length.
    assert (ho : List.length o = (2 ^ d)%nat) by apply zfft_length.
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
    { rewrite !length_combine, !length_app, he, ho, zpows_len. cbn [Nat.pow]. lia. }
    rewrite (nth_map_ind _ _ j (0%Z, 0%Z, 0%Z)) by (rewrite hlen; exact hj).
    rewrite !combine_nth by (rewrite ?length_combine, ?length_app, ?he, ?ho, ?zpows_len; cbn [Nat.pow]; lia).
    cbn [fst snd]. rewrite to_F_bx_mod', to_F_bx_add, to_F_bx_mul.
    rewrite (happ e he), (happ o ho), zpows_F by exact hj. rewrite to_F_bx1.
    unfold e, o. rewrite !(ih w2) by assumption.
    rewrite (peval_split p).
    assert (hsq : fmul (pw2 (to_F (bx w)) j) (pw2 (to_F (bx w)) j) = pw2 (to_F (bx w2)) j0).
    { rewrite hw2, pw_sq, <-pw_add.
      cbn [Nat.pow] in hw, hj. destruct (Nat.ltb_spec j (2 ^ d)) as [h | h].
      + unfold j0. rewrite Nat.mod_small by exact h. f_equal. lia.
      + unfold j0. replace j with ((j - 2 ^ d) + 1 * 2 ^ d)%nat at 3 by lia. rewrite Nat.Div0.mod_add, Nat.mod_small by lia.
        replace (j + j)%nat with (2 * (j - 2 ^ d) + 2 * 2 ^ d)%nat by lia.
        rewrite pw_add, hw. field. }
    rewrite hsq. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the encoding *)

Lemma last_nth' : forall {A : Type} (l : list A) d, last l d = nth (List.length l - 1) l d.
Proof.
  intros A l d. induction l as [| x l ih]; [reflexivity |].
  destruct l as [| y l]; [reflexivity |]. change (last (x :: y :: l) d) with (last (y :: l) d). rewrite ih.
  change (List.length (x :: y :: l)) with (S (S (List.length l))). change (List.length (y :: l)) with (S (List.length l)).
  replace (S (S (List.length l)) - 1)%nat with (S (S (List.length l) - 1)) by lia. reflexivity.
Qed.

Theorem zenc_spec : forall om n msg, zenc om n msg = zenc_horner om n msg.
Proof.
  intros om n msg. unfold zenc. destruct (zntt_ok om n) eqn:hk; [| reflexivity].
  unfold zntt_ok in hk. apply andb_true_iff in hk. destruct hk as [hn hq].
  apply Nat.eqb_eq in hn. apply Z.eqb_eq in hq.
  set (d := Nat.log2 n) in *.
  assert (hpos : (0 < n)%nat) by (rewrite <-hn; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (hw : pw2 (to_F (bx om)) (2 ^ d) = fone).
  { apply (f_equal (fun z => to_F (bx z))) in hq. rewrite to_F_bx_mod', to_F_bx_mul, to_F_bx1 in hq.
    rewrite last_nth', zpows_len in hq. rewrite (nth_indep _ 1%Z 0%Z) in hq by (rewrite zpows_len; lia).
    rewrite zpows_F in hq by lia. rewrite to_F_bx1 in hq.
    rewrite hn. etransitivity; [| exact hq]. replace n with (S (n - 1)) at 1 by lia. cbn [Negacyclic.pw]. field. }
  apply nth_ext with (d := 0%Z) (d' := 0%Z).
  - rewrite zfft_length. unfold zenc_horner. rewrite length_map, zpows_len. exact hn.
  - intros j hj. rewrite zfft_length in hj. apply bx_inj.
    + pose proof (zfft_range d om msg) as hr. rewrite Forall_forall in hr. apply hr, nth_In. rewrite zfft_length. exact hj.
    + unfold zenc_horner. rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, zpows_len; lia).
      rewrite map_nth. apply zhorner_range.
    + rewrite (zfft_F d om msg hw j hj). unfold zenc_horner.
      rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, zpows_len; lia).
      rewrite map_nth, zhorner_F, zpows_F by lia. rewrite to_F_bx1. f_equal. field.
Qed.

Lemma zenc_length : forall om n msg, List.length (zenc om n msg) = n.
Proof. intros. rewrite zenc_spec. unfold zenc_horner. rewrite length_map. apply zpows_len. Qed.

Lemma zenc_F : forall om n msg j, (j < n)%nat ->
  to_F (bx (nth j (zenc om n msg) 0%Z)) = peval (PF msg) (pw2 (to_F (bx om)) j).
Proof.
  intros om n msg j hj. rewrite zenc_spec. unfold zenc_horner.
  rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, zpows_len; exact hj).
  rewrite map_nth, zhorner_F, zpows_F by exact hj. rewrite to_F_bx1. f_equal. field.
Qed.
