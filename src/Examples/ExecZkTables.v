(* The extracted prover against the model (zero knowledge for the running
   code, step 2): the masked summand Sfull of the prover's tables (ExecZkSC.v)
   is, pointwise, the model summand of ZkLayer.v.

     SfullA   tablesA, tmaskA, termsA   give fA (mask values kmask 0..3)
*)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckMask MaskedExt MixSummands LayoutLemmas Interp RowLayout.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecVerify ExecProveBase ExecFold ExecProve ExecBackD ZkLayer ExecZkSC.
Import ListNotations.

Add Field fieldF2zt : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation cube2 := (@Mle.cube Fq2 fzero fone).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation tabOf := ExecPublic.tabOf.

(* ---------------------------------------------------------------------- *)
(* tables as functions on the cube *)

Lemma cube_pt_ex : forall k b, In b (cube2 k) -> exists i, (i < 2 ^ k)%nat /\ b = pt2 k i.
Proof.
  intros k b hb.
  apply (Permutation.Permutation_in _ (Permutation.Permutation_sym
           (@pt_perm Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field k))) in hb.
  apply in_map_iff in hb. destruct hb as (i & <- & hi). apply in_seq in hi. exists i. split; [lia | reflexivity].
Qed.

Lemma mle_tab_ext : forall k (l : list F) (g : list F -> F),
  (forall i, (i < 2 ^ k)%nat -> nth i l fzero = g (pt2 k i)) -> forall x, mle2 k (tabOf l) x = mle2 k g x.
Proof.
  intros k l g h x. apply mle_ext. intros b hb. destruct (cube_pt_ex k b hb) as (i & hi & ->).
  rewrite tabOf_pt by exact hi. apply h, hi.
Qed.

Lemma mle_eqtab : forall (tc : list xf) (x : list F), List.length x = List.length tc ->
  mle2 (List.length tc) (tabOf (map to_F (xeq_table tc))) x = eqp2 x (map to_F tc).
Proof.
  intros tc x hx. rewrite (mle_tab_ext _ _ (fun b => eqp2 b (map to_F tc))).
  - apply mle_eqp; rewrite ?length_map; lia.
  - intros i hi. rewrite eqp_table_pt by exact hi. reflexivity.
Qed.

Lemma nth_map_combine : forall {A B C : Type} (g : A * B -> C) (l1 : list A) (l2 : list B) d1 d2 dc i,
  List.length l1 = List.length l2 -> (i < List.length l1)%nat ->
  nth i (map g (combine l1 l2)) dc = g (nth i l1 d1, nth i l2 d2).
Proof.
  intros A B C g l1 l2 d1 d2 dc i hl hi.
  rewrite (nth_indep _ dc (g (d1, d2))) by (rewrite length_map, length_combine; lia).
  rewrite map_nth, combine_nth by exact hl. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* sumcheck A *)

Section A.

  Variable ell : nat.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variables ru rv : list xf.
  Variables al be : xf.
  Variables tc kA : list xf.
  Variable k : coins.

  Hypothesis Hsig : List.length sig = (2 ^ ell)%nat.
  Hypothesis Hcout : List.length cout = (2 ^ ell)%nat.
  Hypothesis Htc : List.length tc = ell.

  Lemma mle_hh : forall x, List.length x = ell ->
    mle2 ell (tabOf (map to_F (hhP cout sig ru rv al be))) x
    = fsub (fadd (mle2 ell (TZh cout ru rv) x) (fmul (to_F be) (mle2 ell (TS sig) x))) (to_F al).
  Proof.
    intros x hx.
    rewrite (mle_tab_ext _ _ (fun bq => fsub (fadd (TZh cout ru rv bq) (fmul (to_F be) (TS sig bq))) (to_F al))).
    - rewrite (@mle_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
              (@mle_add Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
              (@mle_scale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
              (@mle_const Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field) by exact hx.
      reflexivity.
    - intros i hi. unfold TZh, TS. rewrite !tabOf_pt by exact hi.
      assert (hz : List.length (zhatP cout ru rv) = (2 ^ ell)%nat) by (unfold zhatP, cinX; rewrite !length_map; exact Hcout).
      assert (hs : List.length (sigZ sig) = (2 ^ ell)%nat) by (unfold sigZ; rewrite length_map; exact Hsig).
      unfold hhP. rewrite map_map.
      rewrite (nth_map_combine _ _ _ xzero 0%Z) by (rewrite ?hz, ?hs; lia).
      cbn [fst snd]. rewrite <-!to_F_nth.
      rewrite (nth_indep (map bx (sigZ sig)) xzero (bx 0%Z)) by (rewrite length_map; lia).
      rewrite (map_nth bx (sigZ sig) 0%Z i). rewrite to_F_sub, to_F_add, to_F_mul. reflexivity.
  Qed.

  Local Notation avs := (map to_F (kmask k)).

  Theorem SfullA : forall x, List.length x = ell ->
    Sfull (map sF (termsA kA)) ell (tablesA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc) (mF (tmaskA k be)) x
    = fA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA avs x.
  Proof.
    intros x hx.
    unfold Sfull, tablesA, tmaskA, termsA, mF. cbn [combine map fst snd option_map mval sF].
    rewrite <-Htc at 1. rewrite mle_eqtab by lia. rewrite mle_hh by exact hx.
    unfold fA, MixSummands.gA, ustar, uhstar, hstar, hhstar, sgstar, mstar, TU, TUh, TH.
    rewrite <-!to_F_nth. unfold a_u, a_uh, a_h, a_sig.
    unfold termsF, termF, sF. cbn [map fold_left nth LogDer.fsum fst snd].
    rewrite to_F_neg, to_F_mul. field.
  Qed.

End A.

(* ---------------------------------------------------------------------- *)
(* sumcheck B *)

Section B.

  Variables n1 ell : nat.
  Variable pplain : Z.
  Variables (a b : list Z) (cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variables ru rv rA : list xf.
  Variable k : coins.

  Hypothesis Hw : witness_shape n1 ell cout sig wr we1 we2.
  Hypothesis HrA : List.length rA = ell.
  Hypothesis HN : @nF Fq2 fzero fone fadd (2 ^ n1) <> fzero.

  Local Notation rAF := (map to_F rA).

  (* the folded witness table is the witness extension with its last ell variables at rA *)
  Lemma mle_WpP : forall kk y, (kk < 3)%nat -> List.length y = n1 ->
    mle2 n1 (tabOf (map to_F (nth kk (WpP wr we1 we2 rA) []))) y = mle2 (n1 + ell) (TW wr we1 we2 kk) (y ++ rAF).
  Proof.
    intros kk y hkk hy.
    rewrite (@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell _ y rAF) by exact hy.
    apply mle_tab_ext. intros i hi.
    rewrite <-(@mle_cube Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1
                 (fun yy => mle2 ell (fun bb => TW wr we1 we2 kk (yy ++ bb)) rAF) (pt2 n1 i)) by apply pt_cube.
    rewrite <-(@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell _ (pt2 n1 i) rAF)
      by apply (@pt_length Fq2 fzero fone).
    rewrite TW_concat by exact hkk.
    rewrite (W_mle n1 ell cout sig wr we1 we2 rA Hw) by (first [exact hi | exact HrA | apply nth_In; cbn; lia]).
    set (g := fun pols => fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) pols))).
    unfold WpP, Wpol. fold g.
    destruct kk as [| [| [| kk]]]; try lia; reflexivity.
  Qed.

  Local Notation avs := (map to_F (kmask k)).

  Theorem SfullB : forall y, List.length y = n1 ->
    Sfull (map sF termsB) n1 (tablesB n1 pplain a b wr we1 we2 k ru rv rA) (mF (repeat None 7)) y
    = fB n1 ell pplain a b wr we1 we2 ru rv rA avs y.
  Proof.
    intros y hy.
    assert (hc : mle2 n1 (tabOf (map to_F (repeat (cstP n1 k rA) (2 ^ n1)))) y = to_F (cstP n1 k rA)).
    { rewrite (mle_tab_ext _ _ (fun _ => to_F (cstP n1 k rA))).
      - apply (@mle_const Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). exact hy.
      - intros i hi. rewrite map_repeat, (nth_indep _ fzero (to_F (cstP n1 k rA))) by (rewrite repeat_length; exact hi).
        apply nth_repeat. }
    assert (hW : forall kk, (kk < 3)%nat ->
      mle2 n1 (tabOf (map to_F (nth kk (WpP wr we1 we2 rA) []))) y = mle2 (n1 + ell) (TW wr we1 we2 kk) (y ++ rAF))
      by (intros kk hkk; apply mle_WpP; [exact hkk | exact hy]).
    unfold Sfull, tablesB, mF. cbn [repeat map option_map].
    unfold WpP at 1. unfold Wpol at 1. cbn [map app combine fst snd mval].
    unfold rpP. cbn [map app combine fst snd mval].
    rewrite hc.
    pose proof (hW 0%nat ltac:(lia)) as h0. pose proof (hW 1%nat ltac:(lia)) as h1. pose proof (hW 2%nat ltac:(lia)) as h2.
    unfold WpP, Wpol in h0, h1, h2. cbn [map nth] in h0, h1, h2. rewrite h0, h1, h2.
    unfold fB, MixSummands.gB, TRP, rpP. cbn [nth].
    unfold cstP, cBv. rewrite <-!to_F_nth. unfold a_h. rewrite !to_F_mul, to_F_inv, to_F_xfint, to_F_zval.
    unfold termsF, termF, sF, termsB. cbn [map fold_left nth LogDer.fsum fst snd]. rewrite to_F_one.
    field. exact HN.
  Qed.

End B.

(* ---------------------------------------------------------------------- *)
(* sumcheck C *)

Section C.

  Variables n1 ell : nat.
  Variables wr we1 we2 : list (list Z).
  Variables tz kC : list xf.
  Variable k : coins.

  Hypothesis Htz : List.length tz = (n1 + ell)%nat.

  Local Notation avs := (map to_F (kmask k)).

  Theorem SfullC : forall x, List.length x = (n1 + ell)%nat ->
    Sfull (map sF (termsC kC)) (n1 + ell) (tablesC wr we1 we2 tz) (mF (tmaskC k)) x
    = fC n1 ell wr we1 we2 tz kC avs x.
  Proof.
    intros x hx.
    unfold Sfull, tablesC, tmaskC, mF, a_w, Wk, Wpol. cbn [map combine fst snd option_map mval].
    rewrite <-Htz at 1. rewrite mle_eqtab by lia.
    unfold fC, MixSummands.gC, wstar1, wstar2, wstar3, mstar, cube3, TW, Wk, Wpol. cbn [map nth].
    rewrite <-!to_F_nth.
    unfold termsF, termF, sF, termsC. cbn [map fold_left nth LogDer.fsum fst snd].
    rewrite !to_F_neg. unfold SumcheckMask.gmask.
    field.
  Qed.

End C.
