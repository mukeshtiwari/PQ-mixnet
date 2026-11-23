(* The extracted prover against the model (zero knowledge for the running
   code, step 5): the coins.

   The prover's coins (ExecProve.coins: rows of integers, salts, the mask
   table) and the model's coins (the layer: avs and three sumcheck masks;
   the opening: pads pB, pS, slot masks mB, mS, proximity masks qB, qS)
   correspond one to one, for fixed salts:

     coins_onto   every coin record with the prover's shapes and entries in
                  [0, q) is kz (kOf' k x) y for the decoded model coins
                  (x, y) = decode k, which are shaped;
     coins_back   decode (kz (kOf' k0 x) y) = (x, y) for shaped model coins.

   With xmix_prove_refines (ExecZkMain.v), a run with uniform coins of the
   prover's shape is a run of the model with uniform model coins. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Utility Require Import Zpstar.
From Crypto Require Import Counting LogDer Mle CubeIndex Sumcheck SumcheckMask MaskedExt MixSummands ZkBlocks ZkSumcheck.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecVerify ExecProveBase ExecFold ExecSerial ExecProve ExecBack ExecBackD ZkOpenMix ZkMixJoin.
Import ListNotations.

Local Notation F := Fq2.

(* ---------------------------------------------------------------------- *)
(* integers in [0, q) and field elements *)

Lemma Zof_zq_of : forall z, zred z -> Zof (zq_of z) = z.
Proof. intros z hz. unfold Zof, zq_of. cbn. apply Z.mod_small. exact hz. Qed.

Lemma map_Zof_zq : forall r, Forall zred r -> map Zof (map zq_of r) = r.
Proof.
  intros r h. rewrite map_map. rewrite <-(map_id r) at 2. apply map_ext_in. intros z hz.
  rewrite Forall_forall in h. apply Zof_zq_of, h, hz.
Qed.

Lemma of_F_to_F : forall x, reduced x -> of_F (to_F x) = x.
Proof.
  intros [x1 x2] [h1 h2]. cbn [fst snd] in h1, h2. unfold of_F, to_F. cbn [fst snd]. rewrite !Zof_zq_of by (unfold zred; lia). reflexivity.
Qed.

Lemma map_of_F_to_F : forall l, Forall reduced l -> map of_F (map to_F l) = l.
Proof.
  intros l h. rewrite map_map. rewrite <-(map_id l) at 2. apply map_ext_in. intros x hx.
  rewrite Forall_forall in h. apply of_F_to_F, h, hx.
Qed.

Lemma map_zq_Zof : forall (r : list Zq), map zq_of (map Zof r) = r.
Proof. intro r. rewrite map_map. rewrite <-(map_id r) at 2. apply map_ext. apply zq_of_Zof. Qed.

(* a row of GF(q^2) from its two coordinate rows *)
Definition mkF (r0 r1 : list Z) : list F := combine (map zq_of r0) (map zq_of r1).

Lemma reZ_mkF : forall r0 r1, length r0 = length r1 -> Forall zred r0 -> reZ (mkF r0 r1) = r0.
Proof.
  induction r0 as [| x r0 ih]; intros r1 hl h; destruct r1 as [| y r1]; cbn in hl; try lia; [reflexivity |].
  apply Forall_cons_iff in h. destruct h as [hx h].
  unfold reZ, mkF in *. cbn [map combine fst]. rewrite Zof_zq_of by exact hx. f_equal. apply ih; [lia | exact h].
Qed.

Lemma imZ_mkF : forall r0 r1, length r0 = length r1 -> Forall zred r1 -> imZ (mkF r0 r1) = r1.
Proof.
  induction r0 as [| x r0 ih]; intros r1 hl h; destruct r1 as [| y r1]; cbn in hl; try lia; [reflexivity |].
  apply Forall_cons_iff in h. destruct h as [hy h].
  unfold imZ, mkF in *. cbn [map combine snd]. rewrite Zof_zq_of by exact hy. f_equal. apply ih; [lia | exact h].
Qed.

Lemma mkF_reZ : forall m : list F, mkF (reZ m) (imZ m) = m.
Proof.
  induction m as [| [x y] m ih]; [reflexivity |]. unfold mkF, reZ, imZ in *. cbn [map combine fst snd].
  rewrite !zq_of_Zof, ih. reflexivity.
Qed.

(* lists of six *)
Lemma six : forall {A : Type} (l : list A) d, length l = 6%nat ->
  l = [nth 0 l d; nth 1 l d; nth 2 l d; nth 3 l d; nth 4 l d; nth 5 l d].
Proof. intros A l d h. destruct l as [| x0 [| x1 [| x2 [| x3 [| x4 [| x5 [| ? ?]]]]]]]; cbn in h; try lia; reflexivity. Qed.

Lemma skipn_six : forall {A : Type} (l : list A) n d, length l = (n + 6)%nat ->
  skipn n l = [nth n l d; nth (n + 1) l d; nth (n + 2) l d; nth (n + 3) l d; nth (n + 4) l d; nth (n + 5) l d].
Proof.
  intros A l n d h. rewrite (six (skipn n l) d) by (rewrite length_skipn; lia).
  rewrite !nth_skipn. repeat f_equal; lia.
Qed.

(* cuts with enough input: the pieces have the given lengths and concatenate to a prefix *)
Lemma cuts_exact : forall {A : Type} (ds : list nat) (l : list A), (list_sum ds <= length l)%nat ->
  Forall2 (fun d x => length x = d) ds (fst (cuts ds l)) /\ List.concat (fst (cuts ds l)) = firstn (list_sum ds) l.
Proof.
  intros A ds; induction ds as [| d ds ih]; intros l hl; [split; [constructor | reflexivity] |].
  change (list_sum (d :: ds)) with (d + list_sum ds)%nat in *. cbn [cuts cut] in *. destruct (ih (skipn d l)) as [h1 h2]; [rewrite length_skipn; lia |].
  destruct (cuts ds (skipn d l)) as [xs s2] eqn:e. cbn [fst] in *. split.
  - constructor; [rewrite length_firstn; lia | exact h1].
  - cbn [List.concat]. rewrite h2. rewrite <-(firstn_skipn d l) at 3. rewrite firstn_app, length_firstn.
    replace (Nat.min d (length l)) with d by lia. rewrite firstn_firstn. replace (Nat.min (d + list_sum ds) d) with d by lia.
    f_equal. f_equal. lia.
Qed.

Lemma prefix_mask : forall ds (l : list xf), (1 + list_sum ds <= length l)%nat ->
  fst (mask_of ds l) :: List.concat (snd (mask_of ds l)) = firstn (1 + list_sum ds) l
  /\ Forall2 (fun d x => length x = d) ds (snd (mask_of ds l)).
Proof.
  intros ds l hl. destruct l as [| x l]; [cbn in hl; lia |].
  unfold mask_of. cbn [fst snd nth tl]. destruct (cuts_exact ds l) as [h1 h2]; [cbn in hl; lia |].
  split; [rewrite h2; reflexivity | exact h1].
Qed.

Lemma Forall2_csF : forall ds (cs : list (list xf)), Forall2 (fun d x => length x = d) ds cs ->
  Forall2 (fun d x => length x = d) ds (csF cs).
Proof.
  intros ds cs h. unfold csF. induction h as [| d x ds cs hx h ih]; constructor; [rewrite length_map; exact hx | exact ih].
Qed.

Lemma to_F_mflat : forall a0 (cs : list (list xf)), map to_F (a0 :: List.concat cs) = mflat (to_F a0, csF cs).
Proof. intros a0 cs. unfold mflat, csF. cbn [map fst snd]. rewrite to_F_concat. reflexivity. Qed.

Section Coins.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat).

  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation dsA := (map (MixSummands.degA ell) (seq 0 ell)).
  Local Notation dsB := (map (fun _ : nat => 2%nat) (seq 0 n1)).
  Local Notation dsC := (map (MixSummands.degC m) (seq 0 m)).
  Local Notation pok := (params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS).
  Local Notation cok := (coins_ok n1 ell lo1 lo2 nB nqB nS nqS).
  Local Notation shZ := (shapedZ n1 ell lo1 lo2 kB nqB kS nqS).

  Definition rowsRed (rows : list (list Z)) : Prop := Forall (Forall zred) rows.
  Definition coins_red (k : coins) : Prop :=
    rowsRed (kfB k) /\ rowsRed (kpB k) /\ rowsRed (kfS k) /\ rowsRed (kpS1 k) /\ rowsRed (kpS2 k)
    /\ Forall reduced (kmask k).

  (* ---------------------------------------------------------------- *)
  (* decoding *)

  Variable k : coins.

  Definition rB (j : nat) : list Z := nth j (kfB k) [] ++ nth (3 * rw + j) (kpB k) [].
  Definition rS (j : nat) : list Z := nth j (kfS k) [] ++ nth (rs + j) (kpS1 k) [].

  Definition avsD : list F := firstn 7 (map to_F (kmask k)).
  Definition aAD : F := to_F (fst (ExecProve.gA ell k)).
  Definition csAD : list (list F) := csF (snd (ExecProve.gA ell k)).
  Definition aBD : F := to_F (fst (ExecProve.gB n1 ell k)).
  Definition csBD : list (list F) := csF (snd (ExecProve.gB n1 ell k)).
  Definition aCD : F := to_F (fst (ExecProve.gC n1 ell k)).
  Definition csCD : list (list F) := csF (snd (ExecProve.gC n1 ell k)).
  Definition pBD : list (list Zq) := map (map zq_of) (firstn (3 * rw) (kpB k)).
  Definition pSD : list (list Zq) := map (map zq_of) (firstn rs (kpS1 k) ++ kpS2 k).
  Definition mBD : list (list F) := [mkF (rB 0) (rB 1); mkF (rB 2) (rB 3)].
  Definition qBD : list F := mkF (rB 4) (rB 5).
  Definition mSD : list (list F) := [mkF (rS 0) (rS 1); mkF (rS 2) (rS 3)].
  Definition qSD : list F := mkF (rS 4) (rS 5).

  Hypothesis Hp : pok.
  Hypothesis Hk : cok k.
  Hypothesis Hr : coins_red k.

  Lemma n_mask_eq : n_mask n1 ell = (7 + (1 + list_sum (dA ell)) + (1 + list_sum (ExecProve.dB n1)) + (1 + list_sum (dC n1 ell)))%nat.
  Proof. reflexivity. Qed.

  (* the mask table is the concatenation of the decoded layer coins *)
  Lemma kmask_decode : kmaskOf' avsD aAD csAD aBD csBD aCD csCD = kmask k.
  Proof.
    destruct Hk as (_ & _ & _ & _ & _ & _ & hlm & _). destruct Hr as (_ & _ & _ & _ & _ & hred).
    set (km := kmask k) in *. rewrite n_mask_eq in hlm.
    unfold kmaskOf', avsD, aAD, csAD, aBD, csBD, aCD, csCD.
    fold km. rewrite <-(map_of_F_to_F km hred) at 2. f_equal.
    unfold ExecProve.gA, ExecProve.gB, ExecProve.gC. fold km.
    destruct (prefix_mask (dA ell) (skipn 7 km)) as [eA _]; [rewrite length_skipn; lia |].
    destruct (prefix_mask (ExecProve.dB n1) (skipn (8 + list_sum (dA ell)) km)) as [eB _]; [rewrite length_skipn; lia |].
    destruct (prefix_mask (dC n1 ell) (skipn (9 + list_sum (dA ell) + list_sum (ExecProve.dB n1)) km)) as [eC _];
      [rewrite length_skipn; lia |].
    destruct (mask_of (dA ell) (skipn 7 km)) as [x0 cx]. destruct (mask_of (ExecProve.dB n1) _) as [y0 cy].
    destruct (mask_of (dC n1 ell) _) as [z0 cz]. cbn [fst snd] in eA, eB, eC |- *.
    unfold csF. rewrite <-!to_F_concat.
    change (to_F x0 :: map to_F (concat cx)) with (map to_F (x0 :: concat cx)).
    change (to_F y0 :: map to_F (concat cy)) with (map to_F (y0 :: concat cy)).
    change (to_F z0 :: map to_F (concat cz)) with (map to_F (z0 :: concat cz)).
    rewrite eA, eB, eC, <-!map_app, firstn_map. f_equal.
    rewrite <-map_app. f_equal.
    rewrite <-(firstn_skipn 7 km) at 5. f_equal.
    rewrite <-(firstn_skipn (1 + list_sum (dA ell)) (skipn 7 km)) at 2. f_equal.
    rewrite skipn_skipn. replace (1 + list_sum (dA ell) + 7)%nat with (8 + list_sum (dA ell))%nat by lia.
    rewrite <-(firstn_skipn (1 + list_sum (ExecProve.dB n1)) (skipn (8 + list_sum (dA ell)) km)) at 2. f_equal.
    rewrite skipn_skipn. replace (1 + list_sum (ExecProve.dB n1) + (8 + list_sum (dA ell)))%nat
      with (9 + list_sum (dA ell) + list_sum (ExecProve.dB n1))%nat by lia.
    apply firstn_all2. rewrite length_skipn. lia.
  Qed.

  Lemma rows_of : forall cnt len rows, rows_ok cnt len rows -> rowsRed rows ->
    forall j, (j < cnt)%nat -> length (nth j rows []) = len /\ Forall zred (nth j rows []).
  Proof.
    intros cnt len rows [hl hf] hr j hj. rewrite Forall_forall in hf. unfold rowsRed in hr. rewrite Forall_forall in hr.
    assert (hin : In (nth j rows []) rows) by (apply nth_In; lia). split; [apply hf, hin | apply hr, hin].
  Qed.

  Lemma rows_back : forall rows, rowsRed rows -> map (map Zof) (map (map zq_of) rows) = rows.
  Proof.
    intros rows h. rewrite map_map. rewrite <-(map_id rows) at 2. apply map_ext_in. intros r hr.
    unfold rowsRed in h. rewrite Forall_forall in h. apply map_Zof_zq, h, hr.
  Qed.

  Lemma red_firstn : forall n rows, rowsRed rows -> rowsRed (firstn n rows).
  Proof.
    intros n rows h. unfold rowsRed in *. rewrite Forall_forall in *. intros r hr. apply h.
    rewrite <-(firstn_skipn n rows). apply in_or_app. left. exact hr.
  Qed.

  Lemma coins_eta : forall c : coins,
    c = mk_coins (kfB c) (kpB c) (ksB c) (kfS c) (kpS1 c) (ksS1 c) (kmask c) (kpS2 c) (ksS2 c).
  Proof. intros []. reflexivity. Qed.

  (* a full mask row: its first C entries and its pad *)
  Lemma split_row : forall C (f p : list Z), length f = C -> firstn C (f ++ p) = f /\ skipn C (f ++ p) = p.
  Proof.
    intros C f p hf. subst C. split.
    - rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all.
    - rewrite skipn_app, Nat.sub_diag, skipn_O, skipn_all. reflexivity.
  Qed.

  (* every coin record of the prover's shape with entries in [0, q) comes from model coins *)
  Theorem coins_onto : k = kz ell lo1 lo2 (kOf' k avsD aAD csAD aBD csBD aCD csCD) pBD pSD mBD qBD mSD qSD.
  Proof.
    pose proof Hk as (hfB & hpB & _ & hfS & hpS1 & _ & _ & hpS2 & _).
    pose proof Hr as (rfB & rpB & rfS & rpS1 & rpS2 & _).
    assert (fB : forall j, (j < 6)%nat -> length (nth j (kfB k) []) = C1 /\ Forall zred (nth j (kfB k) []))
      by (intros j hj; apply (rows_of 6 C1); assumption).
    assert (pBj : forall j, (j < 3 * rw + 6)%nat -> length (nth j (kpB k) []) = nqB /\ Forall zred (nth j (kpB k) []))
      by (intros j hj; apply (rows_of (3 * rw + 6) nqB); assumption).
    assert (fS : forall j, (j < 6)%nat -> length (nth j (kfS k) []) = C2 /\ Forall zred (nth j (kfS k) []))
      by (intros j hj; apply (rows_of 6 C2); assumption).
    assert (pSj : forall j, (j < rs + 6)%nat -> length (nth j (kpS1 k) []) = nqS /\ Forall zred (nth j (kpS1 k) []))
      by (intros j hj; apply (rows_of (rs + 6) nqS); assumption).
    assert (lrB : forall j, (j < 6)%nat -> length (rB j) = (C1 + nqB)%nat /\ Forall zred (rB j)).
    { intros j hj. unfold rB. destruct (fB j hj) as [l1 r1]. destruct (pBj (3 * rw + j)%nat ltac:(lia)) as [l2 r2].
      rewrite length_app, l1, l2. split; [reflexivity | apply Forall_app; split; assumption]. }
    assert (lrS : forall j, (j < 6)%nat -> length (rS j) = (C2 + nqS)%nat /\ Forall zred (rS j)).
    { intros j hj. unfold rS. destruct (fS j hj) as [l1 r1]. destruct (pSj (rs + j)%nat ltac:(lia)) as [l2 r2].
      rewrite length_app, l1, l2. split; [reflexivity | apply Forall_app; split; assumption]. }
    assert (reB : forall j, (j < 3)%nat -> reZ (mkF (rB (2 * j)) (rB (2 * j + 1))) = rB (2 * j)
                                       /\ imZ (mkF (rB (2 * j)) (rB (2 * j + 1))) = rB (2 * j + 1)).
    { intros j hj. destruct (lrB (2 * j)%nat ltac:(lia)) as [l0 r0]. destruct (lrB (2 * j + 1)%nat ltac:(lia)) as [l1 r1].
      split; [apply reZ_mkF | apply imZ_mkF]; first [rewrite l0, l1; reflexivity | assumption]. }
    assert (reS : forall j, (j < 3)%nat -> reZ (mkF (rS (2 * j)) (rS (2 * j + 1))) = rS (2 * j)
                                       /\ imZ (mkF (rS (2 * j)) (rS (2 * j + 1))) = rS (2 * j + 1)).
    { intros j hj. destruct (lrS (2 * j)%nat ltac:(lia)) as [l0 r0]. destruct (lrS (2 * j + 1)%nat ltac:(lia)) as [l1 r1].
      split; [apply reZ_mkF | apply imZ_mkF]; first [rewrite l0, l1; reflexivity | assumption]. }
    destruct (reB 0%nat ltac:(lia)) as [b0 b1]. destruct (reB 1%nat ltac:(lia)) as [b2 b3].
    destruct (reB 2%nat ltac:(lia)) as [b4 b5].
    destruct (reS 0%nat ltac:(lia)) as [s0 s1]. destruct (reS 1%nat ltac:(lia)) as [s2 s3].
    destruct (reS 2%nat ltac:(lia)) as [s4 s5].
    cbn [Nat.mul Nat.add] in b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, s4, s5.
    rewrite (coins_eta k) at 1. unfold kz, mBD, qBD, mSD, qSD. cbn [nth kOf' kfB kpB ksB kfS kpS1 ksS1 kmask kpS2 ksS2].
    rewrite b0, b1, b2, b3, b4, b5, s0, s1, s2, s3, s4, s5.
    f_equal.
    - (* kfB *)
      rewrite (six (kfB k) []) at 1 by (exact (proj1 hfB)). cbn [map].
      unfold rB. rewrite !(fun j h => proj1 (split_row C1 _ _ (proj1 (fB j h)))) by lia. reflexivity.
    - (* kpB *)
      unfold pBD. rewrite rows_back by (apply red_firstn; exact rpB). cbn [map].
      unfold rB. rewrite !(fun j h => proj2 (split_row C1 _ _ (proj1 (fB j h)))) by lia.
      rewrite <-(firstn_skipn (3 * rw) (kpB k)) at 1. f_equal.
      rewrite (skipn_six (kpB k) (3 * rw) []) by exact (proj1 hpB). rewrite !Nat.add_0_r. reflexivity.
    - (* kfS *)
      rewrite (six (kfS k) []) at 1 by (exact (proj1 hfS)). cbn [map].
      unfold rS. rewrite !(fun j h => proj1 (split_row C2 _ _ (proj1 (fS j h)))) by lia. reflexivity.
    - (* kpS1 *)
      unfold pSD. rewrite map_app, firstn_app, length_map, length_firstn.
      replace (rs - Nat.min rs (length (kpS1 k)))%nat with 0%nat by (rewrite (proj1 hpS1); lia).
      rewrite firstn_O, app_nil_r, firstn_map, firstn_firstn, Nat.min_id.
      rewrite rows_back by (apply red_firstn; exact rpS1). cbn [map].
      unfold rS. rewrite !(fun j h => proj2 (split_row C2 _ _ (proj1 (fS j h)))) by lia.
      rewrite <-(firstn_skipn rs (kpS1 k)) at 1. f_equal.
      rewrite (skipn_six (kpS1 k) rs []) by exact (proj1 hpS1). rewrite !Nat.add_0_r. reflexivity.
    - symmetry. apply kmask_decode.
    - (* kpS2 *)
      unfold pSD. rewrite map_app, skipn_app, length_map, length_firstn.
      replace (rs - Nat.min rs (length (kpS1 k)))%nat with 0%nat by (rewrite (proj1 hpS1); lia).
      rewrite skipn_O, skipn_all2 by (rewrite length_map, length_firstn; lia). cbn [app].
      symmetry. apply rows_back. exact rpS2.
  Qed.

  (* the decoded coins are in the model's ranges *)
  Theorem decode_shaped :
    length avsD = 7%nat /\ @shaped F dsA csAD /\ @shaped F dsB csBD /\ @shaped F dsC csCD
    /\ shZ pBD pSD mBD qBD mSD qSD.
  Proof.
    pose proof Hk as (hfB & hpB & _ & hfS & hpS1 & _ & hlm & hpS2 & _).
    pose proof Hp as (hkB & hkS & _).
    rewrite n_mask_eq in hlm.
    assert (lrB : forall j, (j < 6)%nat -> length (rB j) = kB).
    { intros j hj. unfold rB. rewrite length_app, (proj1 (rows_of 6 C1 _ hfB (proj1 Hr) j hj)).
      rewrite (proj1 (rows_of (3 * rw + 6) nqB _ hpB (proj1 (proj2 Hr)) (3 * rw + j) ltac:(lia))). lia. }
    assert (lrS : forall j, (j < 6)%nat -> length (rS j) = kS).
    { intros j hj. unfold rS. rewrite length_app, (proj1 (rows_of 6 C2 _ hfS (proj1 (proj2 (proj2 Hr))) j hj)).
      rewrite (proj1 (rows_of (rs + 6) nqS _ hpS1 (proj1 (proj2 (proj2 (proj2 Hr)))) (rs + j) ltac:(lia))). lia. }
    assert (lmk : forall r0 r1, length r0 = length r1 -> length (mkF r0 r1) = length r0)
      by (intro r0; induction r0 as [| x r0 ih]; intros r1 h; destruct r1 as [| y r1]; cbn in h |- *; try lia;
          unfold mkF in *; cbn [map combine length]; rewrite ih; lia).
    split; [unfold avsD; rewrite length_firstn, length_map; lia |].
    split; [| split; [| split]].
    - unfold csAD, ExecProve.gA. rewrite <-(ZkMixJoin.dA_eq ell). apply Forall2_csF.
      apply (proj2 (prefix_mask (dA ell) (skipn 7 (kmask k)) ltac:(rewrite length_skipn; lia))).
    - unfold csBD, ExecProve.gB. rewrite <-(ZkMixJoin.dB_eq n1). apply Forall2_csF.
      apply (proj2 (prefix_mask (ExecProve.dB n1) (skipn (8 + list_sum (dA ell)) (kmask k)) ltac:(rewrite length_skipn; lia))).
    - unfold csCD, ExecProve.gC. rewrite <-(ZkMixJoin.dC_eq n1 ell). apply Forall2_csF.
      apply (proj2 (prefix_mask (dC n1 ell) (skipn (9 + list_sum (dA ell) + list_sum (ExecProve.dB n1)) (kmask k))
                      ltac:(rewrite length_skipn; lia))).
    - unfold shapedZ, pBD, pSD, mBD, qBD, mSD, qSD.
      destruct hpB as [hpB1 hpB2]. destruct hpS1 as [hpS11 hpS12]. destruct hpS2 as [hpS21 hpS22].
      rewrite Forall_forall in hpB2, hpS12, hpS22.
      split; [rewrite length_map, length_firstn; lia |].
      split; [apply Forall_forall; intros r hr; apply in_map_iff in hr; destruct hr as (r0 & <- & hr0);
              rewrite length_map; apply hpB2; rewrite <-(firstn_skipn (3 * rw) (kpB k)); apply in_or_app; left; exact hr0 |].
      split; [rewrite length_map, length_app, length_firstn; lia |].
      split; [apply Forall_forall; intros r hr; apply in_map_iff in hr; destruct hr as (r0 & <- & hr0);
              rewrite length_map; apply in_app_or in hr0; destruct hr0 as [hr0 | hr0];
              [apply hpS12; rewrite <-(firstn_skipn rs (kpS1 k)); apply in_or_app; left; exact hr0 | apply hpS22, hr0] |].
      split; [reflexivity |].
      split; [repeat constructor; rewrite lmk by (rewrite !lrB by lia; reflexivity); apply lrB; lia |].
      split; [rewrite lmk by (rewrite !lrB by lia; reflexivity); apply lrB; lia |].
      split; [reflexivity |].
      split; [repeat constructor; rewrite lmk by (rewrite !lrS by lia; reflexivity); apply lrS; lia |].
      rewrite lmk by (rewrite !lrS by lia; reflexivity); apply lrS; lia.
  Qed.

End Coins.

Section Back.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat).
  Variable k0 : coins.

  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation dsA := (map (MixSummands.degA ell) (seq 0 ell)).
  Local Notation dsB := (map (fun _ : nat => 2%nat) (seq 0 n1)).
  Local Notation dsC := (map (MixSummands.degC m) (seq 0 m)).

  Variables (avs : list F) (aA aB aC : F) (csA csB csC : list (list F)).
  Variables (pB pS : list (list Zq)) (mB mS : list (list F)) (qB qS : list F).
  Hypothesis Hp : params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS.
  Hypothesis Havs : length avs = 7%nat.
  Hypothesis HcA : @shaped F dsA csA.
  Hypothesis HcB : @shaped F dsB csB.
  Hypothesis HcC : @shaped F dsC csC.
  Hypothesis Hsh : shapedZ n1 ell lo1 lo2 kB nqB kS nqS pB pS mB qB mS qS.

  Local Notation kx := (kOf' k0 avs aA csA aB csB aC csC).
  Local Notation kc := (kz ell lo1 lo2 kx pB pS mB qB mS qS).

  (* decoding the coins built from model coins gives the model coins back *)
  Theorem coins_back :
    avsD kc = avs
    /\ (aAD ell kc, csAD ell kc) = (aA, csA) /\ (aBD n1 ell kc, csBD n1 ell kc) = (aB, csB)
    /\ (aCD n1 ell kc, csCD n1 ell kc) = (aC, csC)
    /\ pBD n1 ell lo1 kc = pB /\ pSD ell lo2 kc = pS
    /\ mBD n1 ell lo1 kc = mB /\ qBD n1 ell lo1 kc = qB /\ mSD ell lo2 kc = mS /\ qSD ell lo2 kc = qS.
  Proof.
    pose proof Hsh as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    pose proof Hp as (hkB & hkS & _).
    assert (hkm : kmask kc = kmask kx) by reflexivity.
    assert (gA_e : ExecProve.gA ell kc = (of_F aA, map (map of_F) csA))
      by exact (gA_km ell k0 avs aA aB aC csA csB csC Havs HcA).
    assert (gB_e : ExecProve.gB n1 ell kc = (of_F aB, map (map of_F) csB))
      by exact (gB_km n1 ell k0 avs aA aB aC csA csB csC Havs HcA HcB).
    assert (gC_e : ExecProve.gC n1 ell kc = (of_F aC, map (map of_F) csC))
      by exact (gC_km n1 ell k0 avs aA aB aC csA csB csC Havs HcA HcB HcC).
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - unfold avsD. rewrite hkm. cbn [kOf' kmask]. unfold kmaskOf'. rewrite map_to_F_of_F.
      rewrite firstn_app, Havs, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia.
    - unfold aAD, csAD. rewrite gA_e. cbn [fst snd]. rewrite to_F_of_F, csF_of_F. reflexivity.
    - unfold aBD, csBD. rewrite gB_e. cbn [fst snd]. rewrite to_F_of_F, csF_of_F. reflexivity.
    - unfold aCD, csCD. rewrite gC_e. cbn [fst snd]. rewrite to_F_of_F, csF_of_F. reflexivity.
    - unfold pBD. cbn [kz kpB]. rewrite firstn_app, length_map, h1, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite length_map; lia). rewrite map_map.
      rewrite <-(map_id pB) at 2. apply map_ext. apply map_zq_Zof.
    - unfold pSD. cbn [kz kpS1 kpS2]. rewrite firstn_app, length_map, length_firstn.
      replace (rs - Nat.min rs (length pS))%nat with 0%nat by lia. rewrite firstn_O, app_nil_r.
      rewrite firstn_all2 by (rewrite length_map, length_firstn; lia).
      rewrite <-map_app, map_map, firstn_skipn. rewrite <-(map_id pS) at 2. apply map_ext. apply map_zq_Zof.
    - (* the slot masks, the proximity masks *)
      assert (hm : forall i, (i < 2)%nat -> length (nth i mB []) = kB)
        by (intros i hi; rewrite Forall_forall in h6; apply h6, nth_In; lia).
      assert (hmS : forall i, (i < 2)%nat -> length (nth i mS []) = kS)
        by (intros i hi; rewrite Forall_forall in h9; apply h9, nth_In; lia).
      assert (lre : forall (r : list F), length (reZ r) = length r) by (intro r; unfold reZ; apply length_map).
      assert (lim : forall (r : list F), length (imZ r) = length r) by (intro r; unfold imZ; apply length_map).
      assert (fs : forall C (L : list Z), (C <= length L)%nat -> firstn C L ++ skipn C L = L) by (intros; apply firstn_skipn).
      destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
      destruct mS as [| m3 [| m4 [| ? ?]]]; cbn in h8; try lia.
      unfold mBD, qBD, mSD, qSD, rB, rS. cbn [kz kfB kpB kfS kpS1 map nth].
      rewrite !(app_nth2 (map (map Zof) pB)) by (rewrite length_map; lia).
      rewrite !length_map, h1.
      rewrite !(app_nth2 (map (map Zof) (firstn rs pS))) by (rewrite length_map, length_firstn; lia).
      rewrite !length_map, !length_firstn. replace (Nat.min rs (length pS)) with rs by lia.
      replace (3 * rw + 0 - 3 * rw)%nat with 0%nat by lia. replace (3 * rw + 1 - 3 * rw)%nat with 1%nat by lia.
      replace (3 * rw + 2 - 3 * rw)%nat with 2%nat by lia. replace (3 * rw + 3 - 3 * rw)%nat with 3%nat by lia.
      replace (3 * rw + 4 - 3 * rw)%nat with 4%nat by lia. replace (3 * rw + 5 - 3 * rw)%nat with 5%nat by lia.
      replace (rs + 0 - rs)%nat with 0%nat by lia. replace (rs + 1 - rs)%nat with 1%nat by lia.
      replace (rs + 2 - rs)%nat with 2%nat by lia. replace (rs + 3 - rs)%nat with 3%nat by lia.
      replace (rs + 4 - rs)%nat with 4%nat by lia. replace (rs + 5 - rs)%nat with 5%nat by lia.
      cbn [nth]. rewrite !firstn_skipn, !mkF_reZ. split; [reflexivity |]. split; [reflexivity |]. split; reflexivity.
  Qed.

End Back.
