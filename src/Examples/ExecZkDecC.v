(* The extracted decryption prover against the zero-knowledge model: the coins (the counterpart
   of ExecZkCoins.v for the shuffle).

   The prover's coins (dcoins: rows of integers, salts, the mask table) and the model's coins
   (the layer: avs and the two sumcheck masks; the opening: pads pB, pS, slot masks mB, mS,
   proximity masks qB, qS) correspond one to one, for fixed salts:

     dcoins_onto   every coin record with the prover's shapes and entries in [0, q) is
                   dkz k (kmOf x) y for the decoded model coins (x, y), which are shaped
                   (ddecode_shaped);
     dcoins_back   decoding dkz k0 (kmOf x) y gives (x, y) back, for shaped model coins.

   With xdec_prove_refines (ExecZkDecM.v), a run with uniform coins of the prover's shape is a
   run of the model with uniform model coins. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots Counting LogDer Mle CubeIndex Sumcheck SumcheckMask MaskedExt ZkBlocks ZkSumcheck
  ZkTranscript ZeroTest.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecVerify ExecProveBase
  ExecFold ExecSerial ExecProve ExecDec ExecDecProve ExecDecComplete ZkOpenMix ZkMixJoin ZkDecJoin ExecZkCoins
  ExecZkDecO ExecZkDecM.
Import ListNotations.

Local Notation F := Fq2.

Lemma eight : forall {A : Type} (l : list A) d, length l = 8%nat ->
  l = [nth 0 l d; nth 1 l d; nth 2 l d; nth 3 l d; nth 4 l d; nth 5 l d; nth 6 l d; nth 7 l d].
Proof.
  intros A l d h. destruct l as [| x0 [| x1 [| x2 [| x3 [| x4 [| x5 [| x6 [| x7 [| ? ?]]]]]]]]]; cbn in h; try lia; reflexivity.
Qed.

Lemma skipn_eight : forall {A : Type} (l : list A) n d, length l = (n + 8)%nat ->
  skipn n l = [nth n l d; nth (n + 1) l d; nth (n + 2) l d; nth (n + 3) l d; nth (n + 4) l d; nth (n + 5) l d;
               nth (n + 6) l d; nth (n + 7) l d].
Proof.
  intros A l n d h. rewrite (eight (skipn n l) d) by (rewrite length_skipn; lia).
  rewrite !nth_skipn. repeat f_equal; lia.
Qed.

Lemma split_rowD : forall C (f p : list Z), length f = C -> firstn C (f ++ p) = f /\ skipn C (f ++ p) = p.
Proof.
  intros C f p hf. subst C. split.
  - rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all.
  - rewrite skipn_app, Nat.sub_diag, skipn_O, skipn_all. reflexivity.
Qed.

Definition drowsRed (rows : list (list Z)) : Prop := Forall (Forall zred) rows.

Lemma drows_back : forall rows, drowsRed rows -> map (map Zof) (map (map zq_of) rows) = rows.
Proof.
  intros rows h. rewrite map_map. rewrite <-(map_id rows) at 2. apply map_ext_in. intros r hr.
  unfold drowsRed in h. rewrite Forall_forall in h. apply map_Zof_zq, h, hr.
Qed.

Lemma dred_firstn : forall n rows, drowsRed rows -> drowsRed (firstn n rows).
Proof.
  intros n rows h. unfold drowsRed in *. rewrite Forall_forall in *. intros r hr. apply h.
  rewrite <-(firstn_skipn n rows). apply in_or_app. left. exact hr.
Qed.

Lemma drows_of : forall cnt len rows, drows_ok cnt len rows -> drowsRed rows ->
  forall j, (j < cnt)%nat -> length (nth j rows []) = len /\ Forall zred (nth j rows []).
Proof.
  intros cnt len rows [hl hf] hr j hj. rewrite Forall_forall in hf. unfold drowsRed in hr. rewrite Forall_forall in hr.
  assert (hin : In (nth j rows []) rows) by (apply nth_In; lia). split; [apply hf, hin | apply hr, hin].
Qed.

Lemma dcoins_eta : forall c : dcoins, c = mk_dcoins (dfB c) (dpB c) (dsB c) (dmask c) (dfS c) (dpS c) (dsS c).
Proof. intros []. reflexivity. Qed.

Lemma prefix_maskD : forall ds (l : list xf), (1 + list_sum ds <= length l)%nat ->
  fst (mask_ofD ds l) :: List.concat (snd (mask_ofD ds l)) = firstn (1 + list_sum ds) l
  /\ Forall2 (fun d x => length x = d) ds (snd (mask_ofD ds l)).
Proof. intros ds l hl. exact (prefix_mask ds l hl). Qed.

Section DCoinsDec.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat).

  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation dG := (dGX n1 ell base).
  Local Notation dT := (dTX n1).

  Definition dcoins_red (k : dcoins) : Prop :=
    drowsRed (dfB k) /\ drowsRed (dpB k) /\ drowsRed (dfS k) /\ drowsRed (dpS k) /\ Forall reduced (dmask k).

  Variable k : dcoins.

  Definition rBd (j : nat) : list Z := nth j (dfB k) [] ++ nth (kd * rw + j) (dpB k) [].
  Definition rSd (j : nat) : list Z := nth j (dfS k) [] ++ nth (3 + j) (dpS k) [].

  Definition avsDd : list F := firstn (kd + 2) (map to_F (dmask k)).
  Definition aGDd : F := to_F (fst (gGD n1 ell kd base k)).
  Definition csGDd : list (list F) := csF (snd (gGD n1 ell kd base k)).
  Definition aTDd : F := to_F (fst (gTD n1 ell kd base k)).
  Definition csTDd : list (list F) := csF (snd (gTD n1 ell kd base k)).
  Definition xDd : rand2 := (avsDd, ((aGDd, csGDd), (aTDd, csTDd))).
  Definition pBDd : list (list Zq) := map (map zq_of) (firstn (kd * rw) (dpB k)).
  Definition pSDd : list (list Zq) := map (map zq_of) (firstn 3 (dpS k)).
  Definition mBDd : list (list F) := [mkF (rBd 0) (rBd 1); mkF (rBd 2) (rBd 3)].
  Definition qBDd : list F := mkF (rBd 4) (rBd 5).
  Definition mSDd : list (list F) := [mkF (rSd 0) (rSd 1); mkF (rSd 2) (rSd 3); mkF (rSd 4) (rSd 5)].
  Definition qSDd : list F := mkF (rSd 6) (rSd 7).

  Hypothesis Hp : dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS.
  Hypothesis Hk : dcok n1 ell lo1 lo2 kd base nB nqB nS nqS k.
  Hypothesis Hr : dcoins_red k.

  (* the mask table is the concatenation of the decoded layer coins *)
  Lemma dmask_decode : map of_F (kmOf xDd) = dmask k.
  Proof.
    destruct Hk as (_ & _ & _ & hlm & _). destruct Hr as (_ & _ & _ & _ & hred).
    unfold n_maskD in hlm.
    unfold kmOf, xDd, avsDd, aGDd, csGDd, aTDd, csTDd. cbn [fst snd].
    rewrite <-(map_of_F_to_F (dmask k) hred) at 2. f_equal.
    unfold gGD, gTD.
    set (km := dmask k) in *.
    destruct (prefix_maskD dG (skipn (kd + 2) km)) as [eG _]; [rewrite length_skipn; lia |].
    destruct (prefix_maskD dT (skipn (kd + 3 + list_sum dG) km)) as [eT _]; [rewrite length_skipn; lia |].
    destruct (mask_ofD dG (skipn (kd + 2) km)) as [x0 cx]. destruct (mask_ofD dT _) as [y0 cy].
    cbn [fst snd] in eG, eT |- *.
    unfold csF. rewrite <-!to_F_concat.
    change (to_F x0 :: map to_F (List.concat cx)) with (map to_F (x0 :: List.concat cx)).
    change (to_F y0 :: map to_F (List.concat cy)) with (map to_F (y0 :: List.concat cy)).
    rewrite eG, eT, firstn_map, <-!map_app. f_equal.
    assert (e1 : firstn (1 + list_sum dT) (skipn (kd + 3 + list_sum dG) km) = skipn (kd + 3 + list_sum dG) km)
      by (apply firstn_all2; rewrite length_skipn; lia).
    assert (e2 : firstn (1 + list_sum dG) (skipn (kd + 2) km) ++ skipn (kd + 3 + list_sum dG) km = skipn (kd + 2) km).
    { rewrite <-(firstn_skipn (1 + list_sum dG) (skipn (kd + 2) km)) at 2. rewrite skipn_skipn. do 2 f_equal. lia. }
    rewrite e1, e2. apply firstn_skipn.
  Qed.

  (* every coin record of the prover's shape with entries in [0, q) comes from model coins *)
  Theorem dcoins_onto : k = dkz lo1 lo2 k (kmOf xDd) pBDd pSDd mBDd qBDd mSDd qSDd.
  Proof.
    pose proof Hk as (hfB & hpB & _ & _ & hfS & hpS & _).
    pose proof Hr as (rfB & rpB & rfS & rpS & _).
    assert (fB : forall j, (j < 6)%nat -> length (nth j (dfB k) []) = C1 /\ Forall zred (nth j (dfB k) []))
      by (intros j hj; apply (drows_of 6 C1); assumption).
    assert (pBj : forall j, (j < SO)%nat -> length (nth j (dpB k) []) = nqB /\ Forall zred (nth j (dpB k) []))
      by (intros j hj; apply (drows_of SO nqB); assumption).
    assert (fS : forall j, (j < 8)%nat -> length (nth j (dfS k) []) = C2 /\ Forall zred (nth j (dfS k) []))
      by (intros j hj; apply (drows_of 8 C2); assumption).
    assert (pSj : forall j, (j < 11)%nat -> length (nth j (dpS k) []) = nqS /\ Forall zred (nth j (dpS k) []))
      by (intros j hj; apply (drows_of 11 nqS); assumption).
    assert (lrB : forall j, (j < 6)%nat -> length (rBd j) = (C1 + nqB)%nat /\ Forall zred (rBd j)).
    { intros j hj. unfold rBd. destruct (fB j hj) as [l1 r1]. destruct (pBj (kd * rw + j)%nat ltac:(unfold SOX; lia)) as [l2 r2].
      rewrite length_app, l1, l2. split; [reflexivity | apply Forall_app; split; assumption]. }
    assert (lrS : forall j, (j < 8)%nat -> length (rSd j) = (C2 + nqS)%nat /\ Forall zred (rSd j)).
    { intros j hj. unfold rSd. destruct (fS j hj) as [l1 r1]. destruct (pSj (3 + j)%nat ltac:(lia)) as [l2 r2].
      rewrite length_app, l1, l2. split; [reflexivity | apply Forall_app; split; assumption]. }
    assert (reB : forall j, (j < 3)%nat -> reZ (mkF (rBd (2 * j)) (rBd (2 * j + 1))) = rBd (2 * j)
                                       /\ imZ (mkF (rBd (2 * j)) (rBd (2 * j + 1))) = rBd (2 * j + 1)).
    { intros j hj. destruct (lrB (2 * j)%nat ltac:(lia)) as [l0 r0]. destruct (lrB (2 * j + 1)%nat ltac:(lia)) as [l1 r1].
      split; [apply reZ_mkF | apply imZ_mkF]; first [rewrite l0, l1; reflexivity | assumption]. }
    assert (reS : forall j, (j < 4)%nat -> reZ (mkF (rSd (2 * j)) (rSd (2 * j + 1))) = rSd (2 * j)
                                       /\ imZ (mkF (rSd (2 * j)) (rSd (2 * j + 1))) = rSd (2 * j + 1)).
    { intros j hj. destruct (lrS (2 * j)%nat ltac:(lia)) as [l0 r0]. destruct (lrS (2 * j + 1)%nat ltac:(lia)) as [l1 r1].
      split; [apply reZ_mkF | apply imZ_mkF]; first [rewrite l0, l1; reflexivity | assumption]. }
    destruct (reB 0%nat ltac:(lia)) as [b0 b1]. destruct (reB 1%nat ltac:(lia)) as [b2 b3].
    destruct (reB 2%nat ltac:(lia)) as [b4 b5].
    destruct (reS 0%nat ltac:(lia)) as [s0 s1]. destruct (reS 1%nat ltac:(lia)) as [s2 s3].
    destruct (reS 2%nat ltac:(lia)) as [s4 s5]. destruct (reS 3%nat ltac:(lia)) as [s6 s7].
    cbn [Nat.mul Nat.add] in b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, s4, s5, s6, s7.
    rewrite (dcoins_eta k) at 1. unfold dkz, LBd, LSd, mBDd, qBDd, mSDd, qSDd. cbn [nth dfB dpB dsB dmask dfS dpS dsS].
    rewrite b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, s4, s5, s6, s7.
    f_equal.
    - (* dfB *)
      rewrite (ExecZkCoins.six (dfB k) []) at 1 by (exact (proj1 hfB)). cbn [map].
      unfold rBd. rewrite !(fun j h => proj1 (split_rowD C1 _ _ (proj1 (fB j h)))) by lia. reflexivity.
    - (* dpB *)
      unfold pBDd. rewrite drows_back by (apply dred_firstn; exact rpB). cbn [map].
      unfold rBd. rewrite !(fun j h => proj2 (split_rowD C1 _ _ (proj1 (fB j h)))) by lia.
      rewrite <-(firstn_skipn (kd * rw) (dpB k)) at 1. f_equal.
      rewrite (ExecZkCoins.skipn_six (dpB k) (kd * rw) []) by (rewrite (proj1 hpB); unfold SOX; lia).
      rewrite !Nat.add_0_r. reflexivity.
    - symmetry. apply dmask_decode.
    - (* dfS *)
      rewrite (eight (dfS k) []) at 1 by (exact (proj1 hfS)). cbn [map].
      unfold rSd. rewrite !(fun j h => proj1 (split_rowD C2 _ _ (proj1 (fS j h)))) by lia. reflexivity.
    - (* dpS *)
      unfold pSDd. rewrite drows_back by (apply dred_firstn; exact rpS). cbn [map].
      unfold rSd. rewrite !(fun j h => proj2 (split_rowD C2 _ _ (proj1 (fS j h)))) by lia.
      rewrite <-(firstn_skipn 3 (dpS k)) at 1. f_equal.
      rewrite (skipn_eight (dpS k) 3 []) by (rewrite (proj1 hpS); reflexivity). reflexivity.
  Qed.

  (* the decoded coins are in the model's ranges *)
  Theorem ddecode_shaped :
    length avsDd = (kd + 2)%nat /\ @shaped F dG csGDd /\ @shaped F dT csTDd
    /\ shapedD n1 ell lo1 kd kB nqB kS nqS pBDd pSDd mBDd qBDd mSDd qSDd.
  Proof.
    pose proof Hk as (hfB & hpB & _ & hlm & hfS & hpS & _).
    pose proof Hp as (hkB & hkS & _).
    unfold n_maskD in hlm.
    assert (lrB : forall j, (j < 6)%nat -> length (rBd j) = kB).
    { intros j hj. unfold rBd. rewrite length_app, (proj1 (drows_of 6 C1 _ hfB (proj1 Hr) j hj)).
      rewrite (proj1 (drows_of SO nqB _ hpB (proj1 (proj2 Hr)) (kd * rw + j) ltac:(unfold SOX; lia))). lia. }
    assert (lrS : forall j, (j < 8)%nat -> length (rSd j) = kS).
    { intros j hj. unfold rSd. rewrite length_app, (proj1 (drows_of 8 C2 _ hfS (proj1 (proj2 (proj2 Hr))) j hj)).
      rewrite (proj1 (drows_of 11 nqS _ hpS (proj1 (proj2 (proj2 (proj2 Hr)))) (3 + j) ltac:(lia))). lia. }
    assert (lmk : forall r0 r1, length r0 = length r1 -> length (mkF r0 r1) = length r0)
      by (intro r0; induction r0 as [| x r0 ih]; intros r1 h; destruct r1 as [| y r1]; cbn in h |- *; try lia;
          unfold mkF in *; cbn [map combine length]; rewrite ih; lia).
    split; [unfold avsDd; rewrite length_firstn, length_map; lia |].
    split; [| split].
    - unfold csGDd, gGD. apply Forall2_csF.
      apply (proj2 (prefix_maskD dG (skipn (kd + 2) (dmask k)) ltac:(rewrite length_skipn; lia))).
    - unfold csTDd, gTD. apply Forall2_csF.
      apply (proj2 (prefix_maskD dT (skipn (kd + 3 + list_sum dG) (dmask k)) ltac:(rewrite length_skipn; lia))).
    - unfold shapedD, pBDd, pSDd, mBDd, qBDd, mSDd, qSDd.
      destruct hpB as [hpB1 hpB2]. destruct hpS as [hpS1 hpS2].
      rewrite Forall_forall in hpB2, hpS2.
      split; [rewrite length_map, length_firstn, hpB1; unfold SOX; lia |].
      split; [apply Forall_forall; intros r hr; apply in_map_iff in hr; destruct hr as (r0 & <- & hr0);
              rewrite length_map; apply hpB2; rewrite <-(firstn_skipn (kd * rw) (dpB k)); apply in_or_app; left; exact hr0 |].
      split; [rewrite length_map, length_firstn, hpS1; reflexivity |].
      split; [apply Forall_forall; intros r hr; apply in_map_iff in hr; destruct hr as (r0 & <- & hr0);
              rewrite length_map; apply hpS2; rewrite <-(firstn_skipn 3 (dpS k)); apply in_or_app; left; exact hr0 |].
      split; [reflexivity |].
      split; [repeat constructor; rewrite lmk by (rewrite !lrB by lia; reflexivity); apply lrB; lia |].
      split; [rewrite lmk by (rewrite !lrB by lia; reflexivity); apply lrB; lia |].
      split; [reflexivity |].
      split; [repeat constructor; rewrite lmk by (rewrite !lrS by lia; reflexivity); apply lrS; lia |].
      rewrite lmk by (rewrite !lrS by lia; reflexivity); apply lrS; lia.
  Qed.

End DCoinsDec.

Section DBack.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat).
  Variable k0 : dcoins.

  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation dG := (dGX n1 ell base).
  Local Notation dT := (dTX n1).

  Variables (avs : list F) (aG aT : F) (csG csT : list (list F)).
  Variables (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F).
  Hypothesis Hp : dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS.
  Hypothesis Havs : length avs = (kd + 2)%nat.
  Hypothesis HcG : @shaped F dG csG.
  Hypothesis HcT : @shaped F dT csT.
  Hypothesis Hsh : shapedD n1 ell lo1 kd kB nqB kS nqS pB pS mB qB mS qS.

  Local Notation xL := (avs, ((aG, csG), (aT, csT))).
  Local Notation kc := (dkz lo1 lo2 k0 (kmOf xL) pB pS mB qB mS qS).

  (* decoding the coins built from model coins gives the model coins back *)
  Theorem dcoins_back :
    xDd n1 ell kd base kc = xL
    /\ pBDd n1 ell lo1 kd kc = pB /\ pSDd kc = pS
    /\ mBDd n1 ell lo1 kd kc = mB /\ qBDd n1 ell lo1 kd kc = qB /\ mSDd kc = mS /\ qSDd kc = qS.
  Proof.
    pose proof Hsh as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    pose proof Hp as (hkB & hkS & _).
    assert (gG_e : gGD n1 ell kd base kc = (of_F aG, map (map of_F) csG))
      by exact (gG_kc n1 ell lo1 lo2 kd base k0 avs aG aT csG csT pB pS mB qB mS qS Havs HcG).
    assert (gT_e : gTD n1 ell kd base kc = (of_F aT, map (map of_F) csT))
      by exact (gT_kc n1 ell lo1 lo2 kd base k0 avs aG aT csG csT pB pS mB qB mS qS Havs HcG HcT).
    split; [| split; [| split]].
    - unfold xDd, avsDd, aGDd, csGDd, aTDd, csTDd. rewrite gG_e, gT_e. cbn [fst snd].
      rewrite !to_F_of_F, !csF_of_F. cbn [dkz dmask]. rewrite map_to_F_of_F. unfold kmOf. cbn [fst snd].
      rewrite firstn_app, Havs, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia. reflexivity.
    - unfold pBDd. cbn [dkz dpB]. rewrite firstn_app, length_map, h1, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite length_map; lia). rewrite map_map.
      rewrite <-(map_id pB) at 2. apply map_ext. apply map_zq_Zof.
    - unfold pSDd. cbn [dkz dpS]. rewrite firstn_app, length_map, h3, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite length_map; lia). rewrite map_map.
      rewrite <-(map_id pS) at 2. apply map_ext. apply map_zq_Zof.
    - destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
      destruct mS as [| m3 [| m4 [| m5 [| ? ?]]]]; cbn in h8; try lia.
      unfold mBDd, qBDd, mSDd, qSDd, rBd, rSd. cbn [dkz dfB dpB dfS dpS LBd LSd map nth].
      rewrite !(app_nth2 (map (map Zof) pB)) by (rewrite length_map; lia).
      rewrite !length_map, h1.
      rewrite !(app_nth2 (map (map Zof) pS)) by (rewrite length_map; lia).
      rewrite !length_map, h3.
      replace (kd * rw + 0 - kd * rw)%nat with 0%nat by lia. replace (kd * rw + 1 - kd * rw)%nat with 1%nat by lia.
      replace (kd * rw + 2 - kd * rw)%nat with 2%nat by lia. replace (kd * rw + 3 - kd * rw)%nat with 3%nat by lia.
      replace (kd * rw + 4 - kd * rw)%nat with 4%nat by lia. replace (kd * rw + 5 - kd * rw)%nat with 5%nat by lia.
      cbn [Nat.add Nat.sub nth]. rewrite !firstn_skipn, !mkF_reZ.
      split; [reflexivity |]. split; [reflexivity |]. split; reflexivity.
  Qed.

End DBack.
