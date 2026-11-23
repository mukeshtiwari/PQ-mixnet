(* The nine claims of mix_derive (mix_proof.py) as executable functions,
   and their refinement to claims9 of MixLayout.v.

   A term is (slot, row, coefficient, functional). Rows are numbered as in
   MixLayout.v: rows of the small matrix are shifted by SO. Functionals of
   func slots are dense lists (mix_proof.py uses dicts {position: value};
   the values at the listed positions are the same, the other positions
   are zero).

   Theorem to_F_claims9: mapping to_F over every coefficient and functional
   of xclaims9 gives claims9 at the field GF(q^2), for the same challenges.
   The values mle n1 rp_k ry are inputs here (the verifier computes them
   from the statement). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import Counting LogDer Mle MaskedExt SlotKinds LayoutLemmas RowLayout MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck.
Import ListNotations.

Add Field fieldF2c : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Definition xterm : Type := (nat * nat * xf * list xf)%type.

Definition tF (t : xterm) : @gterm Fq2 :=
  let '(s, r, c, lv) := t in mk_gterm s r (to_F c) (map to_F lv).

Definition xtg : xf := (0%Z, 1%Z).

Lemma to_F_tg : to_F xtg = ftg.
Proof. unfold to_F, xtg, ftg, egen. cbn [fst snd]. rewrite zq_of_0, zq_of_1. reflexivity. Qed.

Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation pt2 := (@CubeIndex.pt Fq2 fzero fone).
Local Notation eqvec2 := (@eqvec Fq2 fzero fone fadd fmul fsub).
Local Notation tabt2 := (@tabt Fq2 fzero fone fadd fmul fsub).

(* ---------------------------------------------------------------------- *)
(* tensor claims *)

Definition xtabt (slot start : nat) (coef : xf) (lo : nat) (x : list xf) : list xterm :=
  let hi := xhi_coefs lo x in
  map (fun i => (slot, (start + i)%nat, xmul coef (nth i hi xzero), [])) (seq 0 (length hi)).

Lemma eqvec2_length : forall k (x : list Fq2), length (eqvec2 k x) = (2 ^ k)%nat.
Proof. intros k x. unfold RowLayout.eqvec. rewrite length_map, length_seq. reflexivity. Qed.

Theorem to_F_tabt : forall slot start coef lo x,
  map tF (xtabt slot start coef lo x) = tabt2 slot start (to_F coef) (length x) lo (map to_F x).
Proof.
  intros slot start coef lo x. unfold xtabt, RowLayout.tabt.
  pose proof (to_F_hi_coefs lo x) as eh.
  assert (hl : length (xhi_coefs lo x) = (2 ^ hiE (length x) lo)%nat)
    by (rewrite <-(length_map to_F), eh, eqvec2_length; reflexivity).
  rewrite map_map, hl. apply map_ext_in. intros i hi. apply in_seq in hi.
  unfold tF. cbn [map]. f_equal. rewrite to_F_mul, to_F_nth, eh. f_equal.
  unfold RowLayout.eqvec. rewrite (nth_indep _ fzero (eqp2 (pt2 (hiE (length x) lo) 0) (skipn (loE (length x) lo) (map to_F x))))
    by (rewrite length_map, length_seq; lia).
  rewrite (map_nth (fun y => eqp2 (pt2 (hiE (length x) lo) y) (skipn (loE (length x) lo) (map to_F x)))).
  rewrite seq_nth by lia. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* functionals on the mask-table row *)

Fixpoint xpows (x : xf) (k : nat) (p : xf) : list xf :=
  match k with
  | O => []
  | S k' => p :: xpows x k' (xmul p x)
  end.

Fixpoint xfnl (degs : list nat) (r : list xf) : list xf :=
  match degs, r with
  | d :: ds, ri :: r' => xpows ri d ri ++ xfnl ds r'
  | _, _ => []
  end.

Definition xfuncv (degs : list nat) (r : list xf) : list xf := xone :: xfnl degs r.

Definition xgfunv (off : nat) (cf : list xf) : list xf :=
  repeat xzero (2 * off) ++ flat_map (fun c => [c; xmul c xtg]) cf.

Definition xunitv (e : nat) : list xf := repeat xzero (2 * e) ++ [xone; xtg].

Lemma to_F_pows : forall x k p, map to_F (xpows x k p) = @pows Fq2 fmul (to_F x) k (to_F p).
Proof.
  intros x k; induction k as [| k ih]; intro p; [reflexivity |].
  cbn [xpows LayoutLemmas.pows map]. rewrite ih, to_F_mul. reflexivity.
Qed.

Lemma to_F_fnl : forall degs r, map to_F (xfnl degs r) = @fnl Fq2 fmul degs (map to_F r).
Proof.
  induction degs as [| d ds ih]; intro r; [reflexivity |]. destruct r as [| ri r]; [reflexivity |].
  cbn [xfnl RowLayout.fnl map]. rewrite map_app, to_F_pows, ih. reflexivity.
Qed.

Lemma to_F_funcv : forall degs r, map to_F (xfuncv degs r) = @funcv Fq2 fone fmul degs (map to_F r).
Proof. intros degs r. unfold xfuncv, RowLayout.funcv. cbn [map]. rewrite to_F_one, to_F_fnl. reflexivity. Qed.

Lemma to_F_gfunv : forall off cf, map to_F (xgfunv off cf) = @gfunv Fq2 fzero fmul ftg off (map to_F cf).
Proof.
  intros off cf. unfold xgfunv, RowLayout.gfunv. rewrite map_app, map_repeat', to_F_zero. f_equal.
  induction cf as [| c cf ih]; [reflexivity |]. cbn [flat_map map app]. rewrite to_F_mul, to_F_tg, ih. reflexivity.
Qed.

Lemma to_F_unitv : forall e, map to_F (xunitv e) = @unitv Fq2 fzero fone ftg e.
Proof.
  intro e. unfold xunitv, RowLayout.unitv. rewrite map_app, map_repeat', to_F_zero. cbn [map].
  rewrite to_F_one, to_F_tg. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the nine claims *)

Section Claims.

  Variables n1 ell lo1 lo2 SO : nat.
  Local Notation m := (n1 + ell)%nat.
  Variables dA dB dC : list nat.
  Variable invN : xf.
  Variables r ry rz : list xf.
  Variable rhoB : xf.
  Variables mrp1 mrp2 mrp3 : xf.

  Local Notation rw := (MixLayout.rw n1 ell lo1).
  Local Notation rs := (MixLayout.rs ell lo2).
  Local Notation rM := (MixLayout.rM ell lo2 SO).

  Definition xgt4 (coef : xf) (lv : list xf) : xterm := (4%nat, rM, coef, lv).

  Definition xcl1 : list xterm :=
    xtabt 3 (rU0 ell lo2 SO) xone lo2 r ++ xtabt 3 (rU1 ell lo2 SO) xtg lo2 r ++ [xgt4 (xzval r) (xunitv 0)].
  Definition xcl2 : list xterm :=
    xtabt 3 (rUh0 ell lo2 SO) xone lo2 r ++ xtabt 3 (rUh1 ell lo2 SO) xtg lo2 r ++ [xgt4 (xzval r) (xunitv 1)].
  Definition xcl3 : list xterm := xtabt 3 (rSg SO) xone lo2 r ++ [xgt4 (xzval r) (xunitv 2)].
  Definition xcl4 : list xterm :=
    xtabt 1 (rW n1 ell lo1 0) mrp1 lo1 (ry ++ r) ++ xtabt 1 (rW n1 ell lo1 1) mrp2 lo1 (ry ++ r)
    ++ xtabt 1 (rW n1 ell lo1 2) mrp3 lo1 (ry ++ r)
    ++ [xgt4 (xmul (xzval r) invN) (xunitv 3); xgt4 rhoB (xgfunv (offB dA) (xfuncv dB ry))].
  Definition xcl5 : list xterm := xtabt 2 (rW n1 ell lo1 0) xone lo1 rz ++ [xgt4 (xzval rz) (xunitv 4)].
  Definition xcl6 : list xterm := xtabt 2 (rW n1 ell lo1 1) xone lo1 rz ++ [xgt4 (xzval rz) (xunitv 5)].
  Definition xcl7 : list xterm := xtabt 2 (rW n1 ell lo1 2) xone lo1 rz ++ [xgt4 (xzval rz) (xunitv 6)].
  Definition xcl8 : list xterm := [xgt4 xone (xgfunv offA (xfuncv dA r))].
  Definition xcl9 : list xterm := [xgt4 xone (xgfunv (offC dA dB) (xfuncv dC rz))].

  Definition xclaims9 : list (list xterm) := [xcl1; xcl2; xcl3; xcl4; xcl5; xcl6; xcl7; xcl8; xcl9].

  Variables rp1 rp2 rp3 : list Fq2 -> Fq2.
  Hypothesis Hr : length r = ell.
  Hypothesis Hry : length ry = n1.
  Hypothesis Hrz : length rz = m.
  Hypothesis Hm1 : to_F mrp1 = @mle Fq2 fzero fone fadd fmul fsub n1 rp1 (map to_F ry).
  Hypothesis Hm2 : to_F mrp2 = @mle Fq2 fzero fone fadd fmul fsub n1 rp2 (map to_F ry).
  Hypothesis Hm3 : to_F mrp3 = @mle Fq2 fzero fone fadd fmul fsub n1 rp3 (map to_F ry).

  Lemma tF_gt4 : forall c lv, tF (xgt4 c lv) = @gt4 Fq2 ell lo2 SO (to_F c) (map to_F lv).
  Proof. reflexivity. Qed.

  Theorem to_F_claims9 :
    map (map tF) xclaims9
    = @claims9 Fq2 fzero fone fadd fmul fsub ftg (to_F invN) n1 ell lo1 lo2 SO dA dB dC
               (map to_F r) (map to_F ry) (map to_F rz) (to_F rhoB) rp1 rp2 rp3.
  Proof.
    assert (lr : length (map to_F r) = ell) by (rewrite length_map; exact Hr).
    assert (lz : length (map to_F rz) = m) by (rewrite length_map; exact Hrz).
    assert (lyr : length (ry ++ r) = m) by (rewrite length_app; lia).
    unfold xclaims9, MixLayout.claims9. cbn [map].
    unfold xcl1, xcl2, xcl3, xcl4, xcl5, xcl6, xcl7, xcl8, xcl9,
           MixLayout.cl1, MixLayout.cl2, MixLayout.cl3, MixLayout.cl4, MixLayout.cl5, MixLayout.cl6,
           MixLayout.cl7, MixLayout.cl8, MixLayout.cl9.
    rewrite !map_app, !to_F_tabt. cbn [map]. rewrite !tF_gt4.
    rewrite !to_F_unitv, !to_F_gfunv, !to_F_funcv, !to_F_zval, to_F_mul, to_F_zval, to_F_one, to_F_tg.
    rewrite Hr, Hrz, lyr, map_app, Hm1, Hm2, Hm3. reflexivity.
  Qed.

End Claims.
