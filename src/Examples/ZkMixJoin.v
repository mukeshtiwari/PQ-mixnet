(* Zero knowledge, step Z5: the sumcheck layer and the opening of the
   shuffle proof joined (paper, Theorem 5.3).

   The prover's coins are those of the layer (ZkLayer: the mask table,
   i.e. the coefficients avs of the masked evaluations and the three
   sumcheck masks) and those of the opening (ZkOpenMix: pads, slot masks,
   proximity masks). The mask table is also data of a committed row (the
   last row of the second small batch), so the opening depends on the
   layer coins: kOf x is the coin record whose mask table is the one of x.

   The opening's simulator needs one value from the layer, cv (the
   batched targets times the challenge c). cvV computes it from the layer
   transcript as the verifier does: the masked evaluations, the final
   value of sumcheck B, and the mask values of sumchecks A and C solved
   from their final values. cv_honest: on honest transcripts cvV gives
   the true cv. The batching weights depend on the challenges only.

   mix_zk: over all coins, the honest transcripts (layer, opening) are a
   permutation of the simulated ones (zk_join). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Utility Require Import Zpstar.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex Sumcheck SumcheckMask MaskedExt PolyFun MixSummands Interp ZkBlocks ZkSumcheck ZkMix ZkTranscript ZkOpen ZkOpenTranscript ZkJoin LayoutLemmas RowLayout MixBridge Opening MixLayout OpenClaims. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecProveBase ExecFold ExecDec ExecProve ExecRows ExecNtt ExecBack ExecBackD ExecBackO ZkLayer ZkOpenMix ExecFront.
Import ListNotations.

Add Field fieldF2j : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation gmask2 := (@gmask Fq2 fzero fadd fmul).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation nF2 := (@nF Fq2 fzero fone fadd).

(* ---------------------------------------------------------------------- *)
(* field elements as exec values *)

Definition of_F (y : F) : xf := (Zof (fst y), Zof (snd y)).

Lemma to_F_of_F : forall y, to_F (of_F y) = y.
Proof. intros [y1 y2]. unfold to_F, of_F. cbn [fst snd]. rewrite !zq_of_Zof. reflexivity. Qed.

Lemma map_to_F_of_F : forall l, map to_F (map of_F l) = l.
Proof. intro l. rewrite map_map. rewrite (map_ext _ (fun y => y)) by apply to_F_of_F. apply map_id. Qed.

Lemma cuts_concat : forall {A : Type} (ds : list nat) (cs : list (list A)) (rest : list A),
  Forall2 (fun d l => length l = d) ds cs -> cuts ds (List.concat cs ++ rest) = (cs, rest).
Proof.
  intros A ds cs rest h. induction h as [| d l ds cs hl h ih]; [reflexivity |].
  cbn [cuts List.concat cut]. rewrite <-app_assoc. subst d.
  rewrite firstn_app, skipn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r, skipn_all, skipn_O.
  cbn [app]. rewrite ih. reflexivity.
Qed.

Lemma concat_length_shaped : forall {A : Type} (ds : list nat) (cs : list (list A)),
  Forall2 (fun d l => length l = d) ds cs -> length (List.concat cs) = list_sum ds.
Proof.
  intros A ds cs h. induction h as [| d l ds cs hl h ih]; [reflexivity |].
  cbn [List.concat list_sum fold_right]. rewrite length_app, hl, ih. reflexivity.
Qed.

(* the mask table of the layer coins (avs, (A mask), (B mask), (C mask)) *)
Definition mflat (m : F * list (list F)) : list F := fst m :: List.concat (snd m).

Definition kmaskOf' (avs : list F) (aA : F) (csA : list (list F)) (aB : F) (csB : list (list F))
  (aC : F) (csC : list (list F)) : list xf :=
  map of_F (avs ++ (aA :: List.concat csA) ++ (aB :: List.concat csB) ++ (aC :: List.concat csC)).

Definition kOf' (k0 : coins) avs aA csA aB csB aC csC : coins :=
  mk_coins (kfB k0) (kpB k0) (ksB k0) (kfS k0) (kpS1 k0) (ksS1 k0) (kmaskOf' avs aA csA aB csB aC csC) (kpS2 k0) (ksS2 k0).

Definition kOf (k0 : coins) (x : @rand F) : coins :=
  kOf' k0 (fst x) (fst (fst (snd x))) (snd (fst (snd x))) (fst (fst (snd (snd x)))) (snd (fst (snd (snd x))))
       (fst (snd (snd (snd x)))) (snd (snd (snd (snd x)))).

Section Masks.

  Variables n1 ell : nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation dsA := (map (MixSummands.degA ell) (seq 0 ell)).
  Local Notation dsB := (map (fun _ : nat => 2%nat) (seq 0 n1)).
  Local Notation dsC := (map (MixSummands.degC m) (seq 0 m)).

  Variable k0 : coins.
  Variables (avs : list F) (aA aB aC : F) (csA csB csC : list (list F)).
  Hypothesis Havs : length avs = 7%nat.
  Hypothesis HcA : @shaped F dsA csA.
  Hypothesis HcB : @shaped F dsB csB.
  Hypothesis HcC : @shaped F dsC csC.

  Local Notation kx := (kOf' k0 avs aA csA aB csB aC csC).
  Local Notation km := (kmask kx).

  Lemma dA_eq : dA ell = dsA.
  Proof. unfold dA, dAE. apply map_ext. intro i. reflexivity. Qed.
  Lemma dB_eq : ExecProve.dB n1 = dsB.
  Proof. reflexivity. Qed.
  Lemma dC_eq : dC n1 ell = dsC.
  Proof. unfold dC, dCE. apply map_ext. intro i. reflexivity. Qed.

  Lemma km_len : length km = n_mask n1 ell.
  Proof.
    cbn [kOf' kmask]. unfold kmaskOf', n_mask.
    rewrite length_map, !length_app. cbn [length].
    rewrite (concat_length_shaped _ _ HcA), (concat_length_shaped _ _ HcB), (concat_length_shaped _ _ HcC).
    rewrite Havs, dA_eq, dB_eq, dC_eq. lia.
  Qed.

  Lemma km_avs : forall i, (i < 7)%nat -> to_F (nth i km xzero) = nth i avs fzero.
  Proof.
    intros i hi. cbn [kOf' kmask]. unfold kmaskOf'.
    rewrite to_F_nth, map_to_F_of_F, app_nth1 by lia. reflexivity.
  Qed.

  Lemma km_skip7 : skipn 7 km = map of_F (mflat (aA, csA) ++ mflat (aB, csB) ++ mflat (aC, csC)).
  Proof.
    cbn [kOf' kmask]. unfold kmaskOf'. rewrite map_app, skipn_app.
    rewrite length_map, Havs, Nat.sub_diag, skipn_O.
    rewrite skipn_all2 by (rewrite length_map; lia). reflexivity.
  Qed.

  Lemma mask_of_flat : forall ds a0 cs rest, @shaped F ds cs ->
    mask_of ds (map of_F (mflat (a0, cs) ++ rest)) = (of_F a0, map (map of_F) cs).
  Proof.
    intros ds a0 cs rest h. unfold mask_of, mflat. cbn [fst snd app map nth tl].
    rewrite map_app, concat_map. rewrite cuts_concat; [reflexivity |].
    unfold shaped in h. clear -h. induction h as [| d l ds cs hl h ih]; constructor; [| exact ih].
    rewrite length_map. exact hl.
  Qed.

  Lemma gA_km : ExecProve.gA ell kx = (of_F aA, map (map of_F) csA).
  Proof.
    unfold ExecProve.gA. etransitivity; [apply f_equal; exact km_skip7 |].
    rewrite dA_eq. apply mask_of_flat. exact HcA.
  Qed.

  Lemma skip_B : skipn (8 + list_sum (dA ell)) km = map of_F (mflat (aB, csB) ++ mflat (aC, csC)).
  Proof.
    replace (8 + list_sum (dA ell))%nat with ((1 + list_sum (dA ell)) + 7)%nat by lia.
    rewrite <-skipn_skipn, km_skip7, map_app, skipn_app.
    rewrite length_map. unfold mflat. cbn [fst snd length].
    rewrite (concat_length_shaped _ _ HcA), dA_eq, Nat.sub_diag, skipn_O.
    rewrite skipn_all2 by (rewrite length_map; cbn [length]; rewrite (concat_length_shaped _ _ HcA); lia). reflexivity.
  Qed.

  Lemma gB_km : ExecProve.gB n1 ell kx = (of_F aB, map (map of_F) csB).
  Proof.
    unfold ExecProve.gB. etransitivity; [apply f_equal; exact skip_B |].
    rewrite dB_eq. apply mask_of_flat. exact HcB.
  Qed.

  Lemma skip_C : skipn (9 + list_sum (dA ell) + list_sum (ExecProve.dB n1)) km = map of_F (mflat (aC, csC) ++ []).
  Proof.
    replace (9 + list_sum (dA ell) + list_sum (ExecProve.dB n1))%nat
      with ((1 + list_sum (ExecProve.dB n1)) + (8 + list_sum (dA ell)))%nat by lia.
    rewrite <-skipn_skipn, skip_B, map_app, skipn_app.
    rewrite length_map. unfold mflat. cbn [fst snd length].
    rewrite (concat_length_shaped _ _ HcB), dB_eq, Nat.sub_diag, skipn_O.
    rewrite skipn_all2 by (rewrite length_map; cbn [length]; rewrite (concat_length_shaped _ _ HcB); lia).
    rewrite app_nil_r. reflexivity.
  Qed.

  Lemma gC_km : ExecProve.gC n1 ell kx = (of_F aC, map (map of_F) csC).
  Proof.
    unfold ExecProve.gC. etransitivity; [apply f_equal; exact skip_C |].
    rewrite dC_eq. apply mask_of_flat. exact HcC.
  Qed.

  Lemma csF_of_F : forall cs, csF (map (map of_F) cs) = cs.
  Proof.
    intro cs. unfold csF. rewrite map_map. rewrite (map_ext _ (fun l => l)) by apply map_to_F_of_F. apply map_id.
  Qed.

End Masks.

(* ---------------------------------------------------------------------- *)
(* the batched targets from the layer transcript *)

Section Join.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable sigma : list nat.
  Variable k0 : coins.                  (* the coins of the commitments other than the mask table *)
  Variable T : ptrace.                  (* the challenges *)

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation ru := (tru T).
  Local Notation rv := (trv T).
  Local Notation al := (ExecProve.alT T).
  Local Notation be := (ExecProve.beT T).
  Local Notation tc := (ttc T).
  Local Notation kA := (tkA T).
  Local Notation rhoA := (nth 0 (trhoA T) xzero).
  Local Notation rhoB := (nth 0 (trhoB T) xzero).
  Local Notation rhoC := (nth 0 (trhoC T) xzero).
  Local Notation rA := (trA T).
  Local Notation ry := (try T).
  Local Notation tz := (ttz T).
  Local Notation kC := (tkC T).
  Local Notation rz := (trz T).
  Local Notation rAF := (map to_F rA).
  Local Notation ryF := (map to_F ry).
  Local Notation rzF := (map to_F rz).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).
  Local Notation tablesBk := (fun k => tablesB n1 pplain a b wr we1 we2 k ru rv rA).

  Hypothesis Hw : wshape.
  Hypothesis Hs : stmt_ok n1 ell a b cin.
  Hypothesis Hu : length ru = N.
  Hypothesis Hv : length rv = N.
  Hypothesis HrA : length rA = ell.
  Hypothesis Hry : length ry = n1.
  Hypothesis Hrz : length rz = m.

  (* ------------------------------------------------------------------ *)
  (* the final value of sumcheck B, pointwise *)

  Lemma W_point : forall k j, (j < 3)%nat ->
    mle2 m (TW wr we1 we2 j) (ryF ++ rAF) = to_F (xmle (nth (3 + j) (tablesBk k) []) ry).
  Proof.
    intros k j hj.
    assert (hin : In (nth j [wr; we1; we2] []) [wr; we1; we2]) by (apply nth_In; cbn; lia).
    set (g := fun pols => fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) pols))).
    assert (hnth : nth (3 + j) (tablesBk k) [] = g (map (map zm) (nth j [wr; we1; we2] []))).
    { cbv beta. unfold tablesB. rewrite app_nth2 by (unfold rpP; cbn; lia).
      unfold rpP. cbn [length]. replace (3 + j - 3)%nat with j by lia.
      rewrite app_nth1 by (unfold WpP, Wpol; rewrite !length_map; cbn; lia).
      unfold WpP. fold g. rewrite (nth_indep _ [] (g [])) by (unfold Wpol; rewrite !length_map; cbn; lia).
      rewrite (map_nth g). unfold Wpol.
      rewrite (nth_indep _ [] (map (map zm) [])) by (rewrite length_map; cbn; lia).
      rewrite (map_nth (map (map zm))). reflexivity. }
    cbv beta in hnth |- *. rewrite hnth.
    rewrite (@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell _ ryF rAF)
      by (rewrite length_map; exact Hry).
    apply (mle_list n1 _ _ ry); [| exact Hry |].
    { apply (WpP_length n1 ell cout sig wr we1 we2 Hw rA _ hin HrA). }
    intros i hi. cbv beta.
    pose proof (W_mle n1 ell cout sig wr we1 we2 rA Hw (nth j [wr; we1; we2] []) i hin hi HrA) as e.
    rewrite (@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell _ (pt2 n1 i) rAF) in e
      by apply (@pt_length Fq2 fzero fone).
    rewrite (@mle_cube Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field) in e by apply pt_cube.
    cbv beta in e. rewrite (TW_concat wr we1 we2 j hj). rewrite to_F_nth. exact e.
  Qed.

  Lemma rp_point : forall k j, (j < 3)%nat ->
    mle2 n1 (TRP pplain a b ru rv j) ryF = to_F (xmle (nth j (tablesBk k) []) ry).
  Proof.
    intros k j hj. pose proof Hs as (ha & hb & _ & hn1 & _).
    pose proof (rpP_lengths n1 pplain a b ru rv ha hb hn1 Hu Hv) as hrp. rewrite Forall_forall in hrp.
    cbv beta. unfold tablesB. rewrite app_nth1 by (unfold rpP; cbn; lia).
    rewrite to_F_mle by (rewrite Hry; apply hrp, nth_In; unfold rpP; cbn; lia).
    rewrite Hry. reflexivity.
  Qed.

  Lemma cst_point : forall k, to_F (xmle (nth 6 (tablesBk k) []) ry) = to_F (cstP n1 k rA).
  Proof.
    intro k. cbv beta. unfold tablesB.
    rewrite app_nth2 by (unfold rpP; cbn; lia). unfold rpP. cbn [length].
    rewrite app_nth2 by (unfold WpP, Wpol; rewrite !length_map; cbn; lia).
    unfold WpP, Wpol. rewrite !length_map. cbn [length Nat.sub nth].
    rewrite xmle_sum by (rewrite repeat_length, Hry; reflexivity).
    rewrite (fsum_seq_ext _ (fun i => fmul (nth i (map to_F (xeq_table ry)) fzero) (to_F (cstP n1 k rA)))).
    2: { intros i hi. rewrite (nth_indep _ xzero (cstP n1 k rA)) by (rewrite repeat_length, <-Hry; exact hi).
         rewrite nth_repeat. reflexivity. }
    rewrite fsum_map_mul_r, eq_table_sum. field.
  Qed.

  Lemma fB_point : forall k avs, to_F (a_h k) = nth 3 avs fzero ->
    fB n1 ell pplain a b wr we1 we2 ru rv rA avs ryF
    = (let mB j := to_F (xmle (nth j (tablesBk k) []) ry) in
       fadd (fadd (fadd (fmul (mB 0%nat) (mB 3%nat)) (fmul (mB 1%nat) (mB 4%nat))) (fmul (mB 2%nat) (mB 5%nat))) (mB 6%nat)).
  Proof.
    intros k avs hah. cbv zeta. unfold fB, MixSummands.gB.
    rewrite !(rp_point k) by lia.
    rewrite (W_point k 0 ltac:(lia)), (W_point k 1 ltac:(lia)), (W_point k 2 ltac:(lia)).
    rewrite cst_point. cbn [Nat.add].
    unfold cBv, cstP. rewrite !to_F_mul, to_F_inv, to_F_xfint, to_F_zval, hah.
    assert (hN : nF2 N <> fzero).
    { pose proof Hs as (_ & _ & _ & _ & _ & hQ). apply (Fq2_char_upto (N + tau)); [lia |]. split; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | lia]. }
    unfold SumcheckMask.gmask. field. exact hN.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the unmasked summands of A and C at the end point, from the masked evaluations *)

  Local Notation specsJ := (specsL n1 ell pplain a b cin cout sig wr we1 we2 ru rv al be rA rz).
  Local Notation kkx := (fun (l : list xf) i => to_F (nth i l xzero)).
  Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
  Local Notation cube3 := (@MixSummands.cube3 Fq2 fmul fsub).

  Definition EA (ys : list F) : F :=
    fadd (fadd (fmul (eqp2 rAF (map to_F tc))
                     (fadd (fmul (kkx kA 0) (fmul (nth 0 ys fzero) (nth 3 ys fzero)))
                           (fmul (kkx kA 1) (fmul (nth 1 ys fzero)
                                 (fsub (fadd (mle2 ell (TZh cout ru rv) rAF) (fmul (to_F be) (nth 2 ys fzero))) (to_F al))))))
               (fmul (kkx kA 2) (fsub (nth 0 ys fzero) (nth 1 ys fzero))))
         (fmul fzero fzero).

  Definition EC (ys : list F) : F :=
    fmul (eqp2 rzF (map to_F tz))
         (fadd (fadd (fmul (kkx kC 0) (cube3 (nth 4 ys fzero))) (fmul (kkx kC 1) (cube3 (nth 5 ys fzero))))
               (fmul (kkx kC 2) (cube3 (nth 6 ys fzero)))).

  Lemma fA_EA : forall avs, length avs = 7%nat ->
    fA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA avs rAF = EA (@evs Fq2 fzero fone fadd fmul fsub specsJ avs).
  Proof.
    intros avs h. do 7 (destruct avs as [| ? avs]; [cbn in h; lia |]). destruct avs; [| cbn in h; lia].
    unfold EA, specsL. cbn [evs nth]. unfold ev. cbn [fst snd].
    unfold fA, MixSummands.gA, ustar, uhstar, sgstar, hstar, hhstar. cbn [nth].
    unfold sgstar, SumcheckMask.gmask. f_equal. field.
  Qed.

  Lemma fC_EC : forall avs, length avs = 7%nat ->
    fC n1 ell wr we1 we2 tz kC avs rzF = EC (@evs Fq2 fzero fone fadd fmul fsub specsJ avs).
  Proof.
    intros avs h. do 7 (destruct avs as [| ? avs]; [cbn in h; lia |]). destruct avs; [| cbn in h; lia].
    unfold EC, specsL. cbn [evs nth]. unfold ev. cbn [fst snd].
    unfold fC, MixSummands.gC, wstar1, wstar2, wstar3. cbn [nth].
    unfold SumcheckMask.gmask. field.
  Qed.

  (* the final value of a sumcheck, as the verifier computes it *)
  Definition finOf (msgs : list (list F)) (rs : list F) (cl : F) : F :=
    match @Sumcheck.sc_verify Fq2 fzero fone fadd fmul Fq2_dec msgs rs cl with Some v => v | None => fzero end.

  Local Notation rhoAF := (to_F rhoA).
  Local Notation rhoBF := (to_F rhoB).
  Local Notation rhoCF := (to_F rhoC).

  (* the nine targets, from a transcript of the layer *)
  Definition valsV (t : @view F) : list F :=
    let ys := fst t in
    let finA := finOf (snd (fst (snd t))) rAF (fadd (cA kA ys) (fmul rhoAF (fst (fst (snd t))))) in
    let finB := finOf (snd (fst (snd (snd t)))) ryF (fadd (cB cin ru rv al be rA ys) (fmul rhoBF (fst (fst (snd (snd t)))))) in
    let finC := finOf (snd (snd (snd (snd t)))) rzF (fadd (cC ys) (fmul rhoCF (fst (snd (snd (snd t)))))) in
    [nth 0 ys fzero; nth 1 ys fzero; nth 2 ys fzero; finB; nth 4 ys fzero; nth 5 ys fzero; nth 6 ys fzero;
     fdiv (fsub finA (EA ys)) rhoAF; fdiv (fsub finC (EC ys)) rhoCF].

  Local Notation cc := (to_F (nth 0 (tcl T) xzero)).

  Definition cvV (t : @view F) : F := fmul cc (@LogDer.dot Fq2 fzero fadd fmul (map to_F (tkp T)) (valsV t)).


  (* ------------------------------------------------------------------ *)
  (* on honest layer transcripts, cvV is the true cv *)

  Local Notation validx := (valid n1 ell pplain a b cin cout sig wr we1 we2 sigma).
  Local Notation hPx := (hP ell pplain a b cin wr we1 we2 ru rv al be).
  Local Notation hhPx := (hhP cout sig ru rv al be).
  Local Notation dsA := (map (MixSummands.degA ell) (seq 0 ell)).
  Local Notation dsB := (map (fun _ : nat => 2%nat) (seq 0 n1)).
  Local Notation dsC := (map (MixSummands.degC m) (seq 0 m)).

  Hypothesis Hval : validx.
  Hypothesis Htc : length tc = ell.
  Hypothesis HkA : length kA = 3%nat.
  Hypothesis Hnz : existsb (fun x => negb (xnz x)) (hPx ++ hhPx) = false.
  Hypothesis HrhoA : rhoAF <> fzero.
  Hypothesis HrhoC : rhoCF <> fzero.

  Local Notation honLJ := (honLx n1 ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA rhoA rhoB rhoC rA ry tz kC rz).

  Ltac lsplit := match goal with
                 | |- (?x :: ?l) = (?y :: ?l') => apply (f_equal2 (@cons _)); [| lsplit]
                 | |- [] = [] => reflexivity
                 end.

  Local Notation ysJ := (fun avs => @evs Fq2 fzero fone fadd fmul fsub specsJ avs).

  Lemma targets_k : forall avs aA aB aC csA csB csC, length avs = 7%nat ->
    @shaped F dsA csA -> @shaped F dsB csB -> @shaped F dsC csC ->
    targets n1 ell pplain a b cin cout sig wr we1 we2 (kOf' k0 avs aA csA aB csB aC csC) T =
    [nth 0 (ysJ avs) fzero; nth 1 (ysJ avs) fzero; nth 2 (ysJ avs) fzero;
     fadd (fB n1 ell pplain a b wr we1 we2 ru rv rA avs ryF) (fmul rhoBF (gmask2 aB csB ryF));
     nth 4 (ysJ avs) fzero; nth 5 (ysJ avs) fzero; nth 6 (ysJ avs) fzero;
     gmask2 aA csA rAF; gmask2 aC csC rzF].
  Proof.
    intros avs aA aB aC csA csB csC h7 hA hB hC.
    unfold targets. cbv zeta.
    pose proof (km_avs k0 avs aA aB aC csA csB csC h7) as hkm.
    pose proof (gA_km ell k0 avs aA aB aC csA csB csC h7 hA) as gAe.
    pose proof (gB_km n1 ell k0 avs aA aB aC csA csB csC h7 hA hB) as gBe.
    pose proof (gC_km n1 ell k0 avs aA aB aC csA csB csC h7 hA hB hC) as gCe.
    set (k := kOf' k0 avs aA csA aB csB aC csC) in *.
    assert (hah : to_F (a_h k) = nth 3 avs fzero) by (unfold a_h; apply hkm; lia).
    pose proof (fB_point k avs hah) as fBe. cbv zeta in fBe.
    rewrite fBe, gAe, gBe, gCe. cbn [fst snd]. rewrite !to_F_of_F, !csF_of_F.
    assert (hsig : length (map bx (sigZ sig)) = (2 ^ length rA)%nat)
      by (destruct Hw as (hs & _); unfold sigZ; rewrite !length_map, hs, HrA; reflexivity).
    assert (hW : forall j, (j < 3)%nat -> length (map bx (nth j (Wk wr we1 we2) [])) = (2 ^ length rz)%nat).
    { intros j hj. rewrite length_map, Hrz. destruct j as [| [| [| j]]]; try lia; unfold Wk, Wpol; cbn [map nth];
        apply (Wk_length n1 ell cout sig wr we1 we2 Hw); cbn; tauto. }
    do 7 (destruct avs as [| ? avs]; [cbn in h7; lia |]). destruct avs; [| cbn in h7; lia].
    unfold specsL. cbn [evs nth]. unfold ev. cbn [fst snd]. unfold mstar.
    lsplit.
    - unfold a_u. rewrite (hkm 0%nat) by lia.
      rewrite to_F_mle by (rewrite HrA; unfold uP; rewrite length_map; apply hP_length).
      rewrite HrA. reflexivity.
    - unfold a_uh. rewrite (hkm 1%nat) by lia.
      rewrite to_F_mle by (rewrite HrA; unfold uhP; rewrite length_map; apply (hhP_length n1 ell cout sig wr we1 we2); exact Hw).
      rewrite HrA. reflexivity.
    - unfold s_valP. rewrite to_F_add, to_F_mul, to_F_zval. unfold a_sig. rewrite (hkm 2%nat) by lia.
      rewrite to_F_mle by exact hsig. rewrite HrA. reflexivity.
    - reflexivity.
    - unfold a_w. cbn [nth]. rewrite (hkm 4%nat) by lia. rewrite to_F_mle by (apply hW; lia). rewrite Hrz. reflexivity.
    - unfold a_w. cbn [nth]. rewrite (hkm 5%nat) by lia. rewrite to_F_mle by (apply hW; lia). rewrite Hrz. reflexivity.
    - unfold a_w. cbn [nth]. rewrite (hkm 6%nat) by lia. rewrite to_F_mle by (apply hW; lia). rewrite Hrz. reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.

  (* stated on the coin components, not on membership in RLx: that list enumerates GF(q^2), and a
     conversion through it makes the kernel start computing it *)
  Theorem cv_honest : forall avs aA csA aB csB aC csC, length avs = 7%nat ->
    @shaped F dsA csA -> @shaped F dsB csB -> @shaped F dsC csC ->
    cvT n1 ell pplain a b cin cout sig wr we1 we2 (kOf' k0 avs aA csA aB csB aC csC) T
    = cvV (honLJ (avs, ((aA, csA), ((aB, csB), (aC, csC))))).
  Proof.
    intros avs aA csA aB csB aC csC h7 hA hB hC.
    assert (h0 : length avs = length specsJ) by (rewrite h7; reflexivity).
    pose proof (Forall2_length hA) as lA. pose proof (Forall2_length hB) as lB. pose proof (Forall2_length hC) as lC.
    rewrite length_map, length_seq in lA, lB, lC.
    (* the final values of the three sumchecks *)
    pose proof (@sc_complete Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field ell
                  (fA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA avs)
                  (pfA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA avs) rhoAF rAF dsA
                  ltac:(rewrite length_map; exact HrA) ltac:(rewrite length_map, length_seq; reflexivity)
                  (fun j X hj => HpfA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA rA HrA avs j X hj)
                  aA csA (eq_sym lA)) as scA.
    pose proof (@sc_complete Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field n1
                  (fB n1 ell pplain a b wr we1 we2 ru rv rA avs)
                  (pfB n1 ell pplain a b wr we1 we2 ru rv rA avs) rhoBF ryF dsB
                  ltac:(rewrite length_map; exact Hry) ltac:(rewrite length_map, length_seq; reflexivity)
                  (fun j X hj => HpfB n1 ell pplain a b wr we1 we2 ru rv rA ry Hry avs j X hj)
                  aB csB (eq_sym lB)) as scB.
    pose proof (@sc_complete Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field m
                  (fC n1 ell wr we1 we2 tz kC avs)
                  (pfC n1 ell wr we1 we2 tz kC avs) rhoCF rzF dsC
                  ltac:(rewrite length_map; exact Hrz) ltac:(rewrite length_map, length_seq; reflexivity)
                  (fun j X hj => HpfC n1 ell wr we1 we2 tz kC rz Hrz avs j X hj)
                  aC csC (eq_sym lC)) as scC.
    pose proof (HcA_true n1 ell pplain a b cin cout sig wr we1 we2 sigma ru rv al be tc kA rA rz Hval Hw Hs Hu Hv Htc HkA Hnz avs) as eA.
    pose proof (HcB_true n1 ell pplain a b cin cout sig wr we1 we2 ru rv al be rA rz Hw Hs Hu Hv HrA avs h0) as eB.
    pose proof (HcC_true n1 ell pplain a b cin cout sig wr we1 we2 sigma ru rv al be rA tz kC rz Hval Hw Hs avs) as eC.
    cbv beta in eA, eB, eC. rewrite eA in scA. rewrite eB in scB. rewrite eC in scC.
    unfold cvV, cvT. f_equal. f_equal.
    rewrite (targets_k avs aA aB aC csA csB csC h7 hA hB hC).
    unfold valsV, honLx, honL. cbn [fst snd]. unfold honT. cbn [fst snd].
    unfold finOf. rewrite scA, scB, scC.
    rewrite <-(fA_EA avs h7), <-(fC_EC avs h7).
    lsplit; try reflexivity.
    - generalize (fA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA avs rAF).
      generalize (gmask2 aA csA rAF). intros g u. field. exact HrhoA.
    - generalize (fC n1 ell wr we1 we2 tz kC avs rzF).
      generalize (gmask2 aC csC rzF). intros g u. field. exact HrhoC.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the join *)

  Local Notation pok := (params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS).
  Local Notation cok := (fun k => coins_ok n1 ell lo1 lo2 nB nqB nS nqS k).
  Local Notation omBK := (zq_of omB).
  Local Notation omSK := (zq_of omS).
  Local Notation JBn := (map Z.to_nat (tJB T)).
  Local Notation JSn := (map Z.to_nat (tJS T)).
  Local Notation pwK := (@pw Zq qone qmul).

  Hypothesis Hp : pok.
  Hypothesis Hk0 : cok k0.
  Hypothesis Hkp : length (tkp T) = 9%nat.
  Hypothesis HnB : forall i j, (i < nB)%nat -> (j < nB)%nat -> pwK omBK i = pwK omBK j -> i = j.
  Hypothesis HnS : forall i j, (i < nS)%nat -> (j < nS)%nat -> pwK omSK i = pwK omSK j -> i = j.
  Hypothesis HomB0 : omBK <> qzero.
  Hypothesis HomS0 : omSK <> qzero.
  (* the opened columns are the ones the verifier's challenger draws (fp_core: pcs.J.big, pcs.J.small;
     the facts below hold for any challenge name) *)
  Hypothesis HdJB : exists c nm c', get_I c (sb nm) nqB (Z.of_nat nB) = Some (tJB T, c').
  Hypothesis HdJS : exists c nm c', get_I c (sb nm) nqS (Z.of_nat nS) = Some (tJS T, c').

  Lemma nB_pow : nB = (2 ^ log2n 64 nB)%nat.
  Proof. exact (proj1 (proj2 (proj2 Hp))). Qed.
  Lemma nS_pow : nS = (2 ^ log2n 64 nS)%nat.
  Proof. exact (proj1 (proj2 (proj2 (proj2 (proj2 Hp))))). Qed.

  (* hence distinct, in range, and as many as the pads *)
  Lemma HJBnd : NoDup JBn.
  Proof. destruct HdJB as (c & nm & c' & h). exact (drawn_nodup _ _ _ nm _ nB_pow (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJSnd : NoDup JSn.
  Proof. destruct HdJS as (c & nm & c' & h). exact (drawn_nodup _ _ _ nm _ nS_pow (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJBlt : forall j, In j JBn -> (j < nB)%nat.
  Proof. destruct HdJB as (c & nm & c' & h). apply Forall_forall. exact (drawn_indices _ _ _ nm _ nB_pow (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJSlt : forall j, In j JSn -> (j < nS)%nat.
  Proof. destruct HdJS as (c & nm & c' & h). apply Forall_forall. exact (drawn_indices _ _ _ nm _ nS_pow (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJBlen : length JBn = nqB.
  Proof. destruct HdJB as (c & nm & c' & h). rewrite length_map. exact (drawn_count _ _ _ nm _ nB_pow (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJSlen : length JSn = nqS.
  Proof. destruct HdJS as (c & nm & c' & h). rewrite length_map. exact (drawn_count _ _ _ nm _ nS_pow (ex_intro _ c (ex_intro _ c' h))). Qed.
  Hypothesis Hgood : @goodspecs Fq2 fzero fone fmul fsub specsJ.
  Hypothesis HrhoB : rhoBF <> fzero.

  Lemma kOf_ok : forall avs aA csA aB csB aC csC, length avs = 7%nat ->
    @shaped F dsA csA -> @shaped F dsB csB -> @shaped F dsC csC ->
    cok (kOf' k0 avs aA csA aB csB aC csC).
  Proof.
    intros avs aA csA aB csB aC csC h7 hA hB hC.
    destruct Hk0 as (h1 & h2 & h3 & h4 & h5 & h6 & _ & h8 & h9).
    unfold coins_ok. cbn [kOf' kfB kpB ksB kfS kpS1 ksS1 kmask kpS2 ksS2].
    repeat split; try assumption.
    - exact (proj1 h1). - exact (proj2 h1). - exact (proj1 h2). - exact (proj2 h2). - exact (proj1 h3). - exact (proj2 h3).
    - exact (proj1 h4). - exact (proj2 h4). - exact (proj1 h5). - exact (proj2 h5). - exact (proj1 h6). - exact (proj2 h6).
    - exact (km_len n1 ell k0 avs aA aB aC csA csB csC h7 hA hB hC).
    - exact (proj1 h8). - exact (proj2 h8). - exact (proj1 h9). - exact (proj2 h9).
  Qed.

  Local Notation coinsK := (fun k => coinsMix n1 ell lo1 lo2 kB kS pplain a b cin cout sig wr we1 we2 k T).

  Lemma coins_eq : forall k, coinsK k = coinsK k0.
  Proof.
    intro k. cbv beta. unfold coinsMix, O3L, datasS. rewrite !length_map. reflexivity.
  Qed.

  (* the layer, its coins and its view *)
  Local Notation RL1 := (@RL Fq2 lf2 specsJ dsA (map dgB (seq 0 n1)) dsC).
  Local Notation simLJ := (simLx cin ru rv al be kA rhoA rhoB rhoC rA ry rz).
  Local Notation VwLJ := (VwLx n1 ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA rhoA rhoB rhoC rA ry tz kC rz).

  (* the opening, given the layer coins (honest) or the layer view (simulated) *)
  Definition hon2 (x : @rand F) y := honMix n1 ell lo1 lo2 omB omS pplain a b cin cout sig wr we1 we2 (kOf k0 x) T y.
  Definition f2 (x : @rand F) y := oviewMix n1 ell lo1 lo2 omB omS pplain a b cin cout sig wr we1 we2 (kOf k0 x) T y.
  Definition sim2 (v : @view F) w :=
    @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omBK omSK JBn JSn
      (LsB n1 ell lo1 lo2 pplain a b sig k0 T) (LsS n1 ell lo1 lo2 pplain a b sig k0 T) (cvV (simLJ v))
      (shJB n1 ell lo1 lo2 pplain a b sig k0 T) (shJS n1 ell lo1 lo2 pplain a b sig k0 T)
      (shpB n1 ell lo1 T) (shpS n1 ell lo1 lo2 T) (GhB n1 ell lo1 T) (GhS ell lo2 T) w.

  Lemma open_parts_at : forall x, In x RL1 -> forall cv, cv = cvT n1 ell pplain a b cin cout sig wr we1 we2 (kOf k0 x) T ->
    NoDup (coinsK k0)
    /\ (forall y, In y (coinsK k0) -> In (f2 x y) (coinsK k0))
    /\ (forall y y', In y (coinsK k0) -> In y' (coinsK k0) -> f2 x y = f2 x y' -> y = y')
    /\ (forall w, In w (coinsK k0) -> exists y, In y (coinsK k0) /\ f2 x y = w)
    /\ (forall y, In y (coinsK k0) ->
          hon2 x y = @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omBK omSK JBn JSn
                       (LsB n1 ell lo1 lo2 pplain a b sig k0 T) (LsS n1 ell lo1 lo2 pplain a b sig k0 T) cv
                       (shJB n1 ell lo1 lo2 pplain a b sig k0 T) (shJS n1 ell lo1 lo2 pplain a b sig k0 T)
                       (shpB n1 ell lo1 T) (shpS n1 ell lo1 lo2 T) (GhB n1 ell lo1 T) (GhS ell lo2 T) (f2 x y)).
  Proof.
    intros x hx cv ecv.
    pose proof (proj1 (RL_In lf2 lf2_all specsJ dsA (map dgB (seq 0 n1)) dsC x) hx) as hsh.
    destruct x as [avs [[aA csA] [[aB csB] [aC csC]]]]. destruct hsh as (h0 & hA & hB & hC). cbn [fst snd] in h0, hA, hB, hC.
    assert (h7 : length avs = 7%nat) by (rewrite h0; reflexivity).
    pose proof (kOf_ok avs aA csA aB csB aC csC h7 hA hB hC) as hk.
    pose proof (mix_open_parts n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2
                  (kOf k0 (avs, (aA, csA, (aB, csB, (aC, csC))))) T Hp Hw hk Hs Hu Hv HrA Hry Hrz Hkp HnB HnS
                  HomB0 HomS0 HJBnd HJSnd HJBlt HJSlt HJBlen HJSlen cv ecv) as hp.
    rewrite (coins_eq (kOf k0 (avs, (aA, csA, (aB, csB, (aC, csC)))))) in hp.
    exact hp.
  Qed.

  (* Theorem 5.3 for the shuffle proof (sumcheck layer and opening): the honest transcripts over all
     coins of the prover are a permutation of the simulated transcripts over all coins of the simulator *)
  Theorem mix_zk :
    Permutation (map (fun p => (honLJ (fst p), hon2 (fst p) (snd p))) (list_prod RL1 (coinsK k0)))
                (map (fun v => (simLJ (fst v), sim2 (fst v) (snd v))) (list_prod RL1 (coinsK k0))).
  Proof.
    destruct (mix_layer_parts n1 ell pplain a b cin cout sig wr we1 we2 sigma ru rv al be tc kA rhoA rhoB rhoC rA ry tz kC rz
                Hval Hw Hs Hu Hv Htc HkA HrA Hry Hrz Hnz Hgood HrhoA HrhoB HrhoC) as (n1L & i1 & j1 & s1 & e1).
    assert (hcv : forall x, In x RL1 -> cvT n1 ell pplain a b cin cout sig wr we1 we2 (kOf k0 x) T = cvV (simLJ (VwLJ x))).
    { intros x hx. rewrite <-(e1 x hx).
      pose proof (proj1 (RL_In lf2 lf2_all specsJ dsA (map dgB (seq 0 n1)) dsC x) hx) as hsh.
      destruct x as [avs [[aA csA] [[aB csB] [aC csC]]]]. destruct hsh as (h0 & hA & hB & hC). cbn [fst snd] in h0, hA, hB, hC.
      assert (h7 : length avs = 7%nat) by (rewrite h0; reflexivity).
      exact (cv_honest avs aA csA aB csB aC csC h7 hA hB hC). }
    apply (zk_join VwLJ honLJ simLJ RL1 RL1 f2 hon2 sim2 (coinsK k0) (coinsK k0)).
    - exact n1L.
    - exact n1L.
    - exact (proj1 (mix_open_parts n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2
                      k0 T Hp Hw Hk0 Hs Hu Hv HrA Hry Hrz Hkp HnB HnS HomB0 HomS0 HJBnd HJSnd HJBlt HJSlt HJBlen HJSlen
                      _ eq_refl)).
    - exact (proj1 (mix_open_parts n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2
                      k0 T Hp Hw Hk0 Hs Hu Hv HrA Hry Hrz Hkp HnB HnS HomB0 HomS0 HJBnd HJSnd HJBlt HJSlt HJBlen HJSlen
                      _ eq_refl)).
    - exact i1.
    - exact j1.
    - exact s1.
    - exact e1.
    - intros x y hx hy. exact (proj1 (proj2 (open_parts_at x hx (cvV (simLJ (VwLJ x))) (eq_sym (hcv x hx)))) y hy).
    - intros x y y' hx hy hy' e. exact (proj1 (proj2 (proj2 (open_parts_at x hx (cvV (simLJ (VwLJ x))) (eq_sym (hcv x hx))))) y y' hy hy' e).
    - intros x w hx hw. exact (proj1 (proj2 (proj2 (proj2 (open_parts_at x hx (cvV (simLJ (VwLJ x))) (eq_sym (hcv x hx)))))) w hw).
    - intros x y hx hy. unfold sim2. exact (proj2 (proj2 (proj2 (proj2 (open_parts_at x hx (cvV (simLJ (VwLJ x))) (eq_sym (hcv x hx)))))) y hy).
  Qed.

End Join.
