(* The extracted prover against the model (zero knowledge for the running
   code, step 3): the sumcheck messages of a prover run.

   For a run of the extracted prover (ptrans, ExecProve.v), the messages of
   sumchecks A, B and C, as field elements, are the values at the nodes
   0, 2, .., d of the model's honest masked messages hmsg (ZkSumcheck.v)
   for the summands fA, fB, fC and the interpolants pfA, pfB, pfC of
   ZkLayer.v, with the prover's mask (kmask) and challenges:

     msgsA, msgsB, msgsC.

   Ingredients: sc_msgs_hmsg (ExecZkSC.v), SfullA/B/C (ExecZkTables.v),
   HpfA/B/C (ZkLayer.v). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field String.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckMask MaskedExt MixSummands LayoutLemmas Interp RowLayout ZkBlocks ZkSumcheck ZkMix.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecVerify ExecProveBase ExecFold ExecFront ExecProve ExecBack ExecBackD ZkLayer ExecZkSC ExecZkTables.
Import ListNotations.

Local Notation F := Fq2.
Local Notation hmsg2 := (@hmsg Fq2 fzero fone fadd fmul).
Local Notation eval2 := (@eval Fq2 fzero fadd fmul).
Local Notation nF := (@nF Fq2 fzero fone fadd).
Local Notation p2F := (@p2 Fq2 fone fadd fmul).
Local Notation WF := (@W Fq2 fzero fone fadd fmul).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).

Section Msgs.

  Variables n1 ell lo1 lo2 : nat.
  Variables (nB nqB nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable k : coins.
  Variable sigma : list nat.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation stmtx := (stmt_ok n1 ell a b cin).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).
  Local Notation ptransx := (ptrans n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k get_F get_I).
  Local Notation gAx := (gA ell k).
  Local Notation gBx := (ExecProve.gB n1 ell k).
  Local Notation gCx := (gC n1 ell k).
  Local Notation avs := (map to_F (kmask k)).
  Local Notation validx := (valid n1 ell pplain a b cin cout sig wr we1 we2 sigma).
  Local Notation cok := (coins_ok n1 ell lo1 lo2 nB nqB nS nqS k).

  Theorem msgsA : stmtx -> wshape -> forall P T, ptransx P T ->
    forall i, (i < ell)%nat ->
      map to_F (nth i (tmA T) []) =
      map (fun c => eval2 (hmsg2 ell (pfA ell pplain a b cin cout sig wr we1 we2 (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)
                                         (ttc T) (tkA T) avs)
                                 (to_F (nth 0 (trhoA T) xzero)) (to_F (fst gAx)) (csF (snd gAx)) (map to_F (trA T)) i) (nF c))
          (spoints (nth i (dA ell) 0%nat)).
  Proof.
    intros hs hw P T hT i hi.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    pose proof hw as (hsig & hcout & _).
    destruct hT as (_ & hdr & hnz & _ & _ & (c0 & c1 & eA) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & dab & dtc & dkA & drhoA & _).
    assert (dtcl : List.length (ttc T) = ell) by (destruct dtc as (? & ? & h); exact (proj1 (get_F_shape _ _ _ _ _ h))).
    set (al := ExecProve.alT T) in *. set (be := ExecProve.beT T) in *.
    assert (hcsl : List.length (snd gAx) = ell).
    { unfold gA. cbn [snd]. destruct (cuts_shape (dA ell) (tl (skipn 7 (kmask k)))) as [h1 _].
      rewrite dA_len in h1. exact h1. }
    assert (hpl : List.length (trA T) = ell)
      by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eA); cbn; apply dA_len).
    pose proof (sc_msgs_hmsg (fun c nm => get_F c nm 1) "A"%string (tmaskA k be) (termsA (tkA T)) (fst gAx) (snd gAx)
             (nth 0 (trhoA T) xzero) (dA ell) (tablesA ell pplain a b cin cout sig wr we1 we2 (tru T) (trv T) al be (ttc T))
             c0 (tmA T) (trA T) (tfinA T) c1
             (fA ell pplain a b cin cout sig wr we1 we2 (tru T) (trv T) al be (ttc T) (tkA T) avs)
             (pfA ell pplain a b cin cout sig wr we1 we2 (tru T) (trv T) al be (ttc T) (tkA T) avs)) as hM.
    rewrite !dA_len in hM. apply hM; clear hM.
    - intro e. pose proof (f_equal (@List.length nat) e) as e'. rewrite dA_len in e'. cbn in e'. lia.
    - exact hcsl.
    - reflexivity.
    - discriminate.
    - unfold tablesA, uP, uhP. repeat constructor.
      + rewrite xeq_table_length, dtcl. reflexivity.
      + rewrite length_map. apply hP_length.
      + apply hP_length.
      + rewrite length_map. apply (hhP_length n1 ell cout sig wr we1 we2 _ _ al be hw).
      + apply (hhP_length n1 ell cout sig wr we1 we2 _ _ al be hw).
    - exact eA.
    - intros x hx. apply SfullA; assumption.
    - intros j X hj. apply HpfA; assumption.
    - exact hi.
  Qed.

  Theorem msgsB : stmtx -> wshape -> forall P T, ptransx P T ->
    forall i, (i < n1)%nat ->
      map to_F (nth i (tmB T) []) =
      map (fun c => eval2 (hmsg2 n1 (pfB n1 ell pplain a b wr we1 we2 (tru T) (trv T) (trA T) avs)
                                 (to_F (nth 0 (trhoB T) xzero)) (to_F (fst gBx)) (csF (snd gBx)) (map to_F (try T)) i) (nF c))
          (spoints (nth i (dB n1) 0%nat)).
  Proof.
    intros hs hw P T hT i hi.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    destruct hT as (_ & hdr & hnz & _ & _ & (c0A & c1A & eA) & (c0 & finB & c1 & eB) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & _).
    assert (drul : List.length (tru T) = N) by (destruct dru as (? & ? & h); exact (proj1 (get_F_shape _ _ _ _ _ h))).
    assert (drvl : List.length (trv T) = N) by (destruct drv as (? & ? & h); exact (proj1 (get_F_shape _ _ _ _ _ h))).
    assert (hrA : List.length (trA T) = ell)
      by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eA); cbn; apply dA_len).
    assert (hcsl : List.length (snd gBx) = n1).
    { unfold ExecProve.gB. cbn [snd]. destruct (cuts_shape (dB n1) (tl (skipn (8 + list_sum (dA ell)) (kmask k)))) as [h1 _].
      rewrite dB_len in h1. exact h1. }
    assert (hpl : List.length (try T) = n1)
      by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB); cbn; apply dB_len).
    assert (hN : nF N <> fzero).
    { apply (Fq2_char_upto (N + tau)); [lia |]. split; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | lia]. }
    pose proof (sc_msgs_hmsg (fun c nm => get_F c nm 1) "B"%string (repeat None 7) termsB (fst gBx) (snd gBx)
             (nth 0 (trhoB T) xzero) (dB n1) (tablesB n1 pplain a b wr we1 we2 k (tru T) (trv T) (trA T))
             c0 (tmB T) (try T) finB c1
             (fB n1 ell pplain a b wr we1 we2 (tru T) (trv T) (trA T) avs)
             (pfB n1 ell pplain a b wr we1 we2 (tru T) (trv T) (trA T) avs)) as hM.
    rewrite !dB_len in hM. apply hM; clear hM.
    - intro e. pose proof (f_equal (@List.length nat) e) as e'. rewrite dB_len in e'. cbn in e'. lia.
    - exact hcsl.
    - reflexivity.
    - unfold tablesB, rpP. discriminate.
    - pose proof (rpP_lengths n1 pplain a b (tru T) (trv T) ha hb hn1 drul drvl) as hrp.
      unfold tablesB, WpP, Wpol. cbn [map]. apply Forall_app. split; [exact hrp |].
      repeat constructor.
      + apply (WpP_length n1 ell cout sig wr we1 we2); [exact hw | cbn; tauto | exact hrA].
      + apply (WpP_length n1 ell cout sig wr we1 we2); [exact hw | cbn; tauto | exact hrA].
      + apply (WpP_length n1 ell cout sig wr we1 we2); [exact hw | cbn; tauto | exact hrA].
      + apply repeat_length.
    - exact eB.
    - intros y hy. apply (SfullB n1 ell pplain a b cout sig wr we1 we2 (tru T) (trv T) (trA T) k hw hrA hN y hy).
    - intros j X hj. apply HpfB; assumption.
    - exact hi.
  Qed.

  Theorem msgsC : stmtx -> wshape -> forall P T, ptransx P T ->
    forall i, (i < m)%nat ->
      map to_F (nth i (tmC T) []) =
      map (fun c => eval2 (hmsg2 m (pfC n1 ell wr we1 we2 (ttz T) (tkC T) avs)
                                 (to_F (nth 0 (trhoC T) xzero)) (to_F (fst gCx)) (csF (snd gCx)) (map to_F (trz T)) i) (nF c))
          (spoints (nth i (dC n1 ell) 0%nat)).
  Proof.
    intros hs hw P T hT i hi.
    destruct hT as (_ & hdr & _ & _ & _ & _ & _ & (c0 & c1 & eC) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (_ & _ & _ & _ & _ & _ & _ & dtz & _).
    assert (dtzl : List.length (ttz T) = m) by (destruct dtz as (? & ? & h); exact (proj1 (get_F_shape _ _ _ _ _ h))).
    assert (hcsl : List.length (snd gCx) = m).
    { unfold gC. cbn [snd].
      destruct (cuts_shape (dC n1 ell) (tl (skipn (9 + list_sum (dA ell) + list_sum (dB n1)) (kmask k)))) as [h1 _].
      rewrite dC_len in h1. exact h1. }
    assert (hpl : List.length (trz T) = m)
      by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eC); cbn; apply dC_len).
    pose proof (sc_msgs_hmsg (fun c nm => get_F c nm 1) "C"%string (tmaskC k) (termsC (tkC T)) (fst gCx) (snd gCx)
             (nth 0 (trhoC T) xzero) (dC n1 ell) (tablesC wr we1 we2 (ttz T))
             c0 (tmC T) (trz T) (tfinC T) c1
             (fC n1 ell wr we1 we2 (ttz T) (tkC T) avs)
             (pfC n1 ell wr we1 we2 (ttz T) (tkC T) avs)) as hM.
    rewrite !dC_len in hM. apply hM; clear hM.
    - intro e. pose proof (f_equal (@List.length nat) e) as e'. rewrite dC_len in e'. cbn in e'. lia.
    - exact hcsl.
    - reflexivity.
    - discriminate.
    - unfold tablesC, Wk, Wpol. cbn [map]. repeat constructor.
      + rewrite xeq_table_length, dtzl. reflexivity.
      + rewrite length_map. apply (Wk_length n1 ell cout sig wr we1 we2 hw). cbn; tauto.
      + rewrite length_map. apply (Wk_length n1 ell cout sig wr we1 we2 hw). cbn; tauto.
      + rewrite length_map. apply (Wk_length n1 ell cout sig wr we1 we2 hw). cbn; tauto.
    - exact eC.
    - intros x hx. apply SfullC; assumption.
    - intros j X hj. apply HpfC; assumption.
    - exact hi.
  Qed.

  (* the G values: the first component of the model's honT for each sumcheck *)
  Local Notation Gof := (fun (g : xf * list (list xf)) => fadd (fmul (p2F (List.length (csF (snd g)))) (to_F (fst g))) (WF (csF (snd g)))).

  Theorem G_run : stmtx ->
    map to_F (GP n1 ell k) = [Gof gAx; Gof gBx; Gof gCx].
  Proof.
    intros hs. pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    assert (hne : forall ds off, ds <> [] -> snd (mask_of ds (skipn off (kmask k))) <> []).
    { intros ds off hd e. destruct (cuts_shape ds (tl (skipn off (kmask k)))) as [h1 _].
      unfold mask_of in e. cbn [snd] in e. rewrite e in h1. destruct ds; [contradiction | discriminate]. }
    assert (hA : snd gAx <> []) by (apply hne; intro e; pose proof (dA_len ell) as h; rewrite e in h; cbn in h; lia).
    assert (hB : snd gBx <> []) by (apply hne; intro e; pose proof (dB_len n1) as h; rewrite e in h; cbn in h; lia).
    assert (hC : snd gCx <> []) by (apply hne; intro e; pose proof (dC_len n1 ell) as h; rewrite e in h; cbn in h; lia).
    unfold GP. cbn [map]. rewrite !to_F_mtotal by assumption.
    unfold csF. rewrite <-!(length_map (map to_F)).
    rewrite !(@mask_tsum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). reflexivity.
  Qed.

  Local Notation specsJ := (fun T => specsL n1 ell pplain a b cin cout sig wr we1 we2 (tru T) (trv T)
                                     (ExecProve.alT T) (ExecProve.beT T) (trA T) (trz T)).

  (* the masked evaluations sent after sumchecks A and C are the model's evs *)
  Theorem evals_run : stmtx -> wshape -> cok -> validx -> forall P T, ptransx P T ->
    map to_F (evAT sig k T ++ evCT T) = @evs Fq2 fzero fone fadd fmul fsub (specsJ T) avs.
  Proof.
    intros hs hw hk hv P T hT.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    destruct (scA n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k sigma hs hw hk hv P T hT)
      as (clA & eA & vA & lrA & mA & finA).
    destruct (scC n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k sigma hs hw hk hv P T hT)
      as (clC & eC & vC & lrz & mC & finC).
    assert (hkm : (7 <= List.length (kmask k))%nat)
      by (destruct hk as (_ & _ & _ & _ & _ & _ & h & _); rewrite h; unfold n_mask; lia).
    unfold evAT, evAP, evCT, evCP. cbn [map app].
    rewrite (finA 1%nat), (finA 3%nat), (finA 2%nat), (finC 1%nat), (finC 2%nat), (finC 3%nat) by lia.
    unfold maskv, tmaskA, tmaskC, a_w. cbn [nth map].
    unfold specsL, ev. unfold s_valP.
    unfold tablesA, tablesC. cbn [nth].
    rewrite !to_F_add, !to_F_mul, !to_F_zval.
    assert (hl : forall (tbl : list xf) (r : list xf) M, List.length r = M -> List.length tbl = (2 ^ M)%nat ->
                   to_F (xmle tbl r) = mle2 M (tabOf (map to_F tbl)) (map to_F r))
      by (intros tbl r M hr ht; subst M; apply to_F_mle; exact ht).
    rewrite !(hl _ _ ell lrA) by (first [unfold uP; rewrite length_map; apply hP_length
                                        | unfold uhP; rewrite length_map; apply (hhP_length n1 ell cout sig wr we1 we2 _ _ _ _ hw)
                                        | apply hP_length
                                        | unfold sigZ; rewrite !length_map; exact (proj1 hw)]).
    unfold Wk, Wpol. cbn [map nth].
    rewrite !(hl _ _ m lrz) by (rewrite length_map; apply (Wk_length n1 ell cout sig wr we1 we2 hw); cbn; tauto).
    unfold a_u, a_uh, a_sig, a_h.
    remember (kmask k) as km eqn:ekm.
    do 7 (destruct km as [| ? km]; [cbn in hkm; lia |]).
    cbn [evs map nth fst snd]. unfold MaskedExt.mstar, TU, TUh, TS, TH, TW, Wk, Wpol, sigZ. cbn [map nth].
    reflexivity.
  Qed.

End Msgs.
