(* The extracted decryption prover against the zero-knowledge model: the opening
   (the counterpart of ExecZkOpen.v for the shuffle).

   The prover's coins are built from the model's coins (dkz): the mask table is the
   model's layer coins kmOf x; the random F-rows and their pads are the real and
   imaginary parts of the model's slot masks mB (2), mS (3) and proximity masks qB, qS;
   the pads of the data rows are the model's pads pB, pS. Then:

     PFD_mB, PFD_mS     the mask rows of the committed matrices are the model's masks;
     rowB_PFD, rowS_PFD the data rows (with their pads) are the model's rows;
     msD_mask           the mask part of slot vector v is the model's mask m_v;

   and the slot vectors, the proximity vectors, mu and the opened columns are those
   of the model's honest opening honDO (ZkDecOpen.v). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks ZkSumcheck ZkOpen ZkTranscript
  ZkOpenTranscript ZkJoin SlotKinds Opening OpenClaims RowLayout DecLayout.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecVerify
  ExecProveBase ExecRows ExecDec ExecDecProve ExecDecComplete ZkOpenMix ZkMixJoin ZkDecOpen ZkDecJoin ExecZkDecL.
From Examples Require ExecZkOpen ExecBackO.
Import ListNotations.

Add Field fieldF2zdo : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation padd := (@LogDer.padd Fq2 fadd).
Local Notation pscale := (@LogDer.pscale Fq2 fmul).
Local Notation msumF := (@msum Fq2 fadd fmul).

Section DCoins.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat).
  Variable k0 : dcoins.

  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation SO := (SOX n1 ell lo1 kd).

  (* the six random rows of the big matrix and the eight of the small one, before the split into data part and pad *)
  Definition LBd (mB : list (list F)) (qB : list F) : list (list Z) :=
    [reZ (nth 0 mB []); imZ (nth 0 mB []); reZ (nth 1 mB []); imZ (nth 1 mB []); reZ qB; imZ qB].
  Definition LSd (mS : list (list F)) (qS : list F) : list (list Z) :=
    [reZ (nth 0 mS []); imZ (nth 0 mS []); reZ (nth 1 mS []); imZ (nth 1 mS []);
     reZ (nth 2 mS []); imZ (nth 2 mS []); reZ qS; imZ qS].

  (* the prover's coins from the model's: the mask table km (layer), the pads, the masks (opening);
     the salts are those of k0 *)
  Definition dkz (km : list F) (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F)
    : dcoins :=
    mk_dcoins (map (firstn C1) (LBd mB qB)) (map (map Zof) pB ++ map (skipn C1) (LBd mB qB)) (dsB k0)
              (map of_F km)
              (map (firstn C2) (LSd mS qS)) (map (map Zof) pS ++ map (skipn C2) (LSd mS qS)) (dsS k0).

  Definition shapedD (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F) : Prop :=
    length pB = (kd * rw)%nat /\ Forall (fun p => length p = nqB) pB
    /\ length pS = 3%nat /\ Forall (fun p => length p = nqS) pS
    /\ length mB = 2%nat /\ Forall (fun m => length m = kB) mB /\ length qB = kB
    /\ length mS = 3%nat /\ Forall (fun m => length m = kS) mS /\ length qS = kS.

  Lemma dkz_ok : dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS -> dcok n1 ell lo1 lo2 kd base nB nqB nS nqS k0 ->
    forall km pB pS mB qB mS qS, length km = n_maskD n1 ell kd base -> shapedD pB pS mB qB mS qS ->
    dcok n1 ell lo1 lo2 kd base nB nqB nS nqS (dkz km pB pS mB qB mS qS).
  Proof.
    intros hp hk km pB pS mB qB mS qS hkm (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    destruct hp as (hkB & hkS & _). destruct hk as (_ & _ & hsB & _ & _ & _ & hsS).
    rewrite Forall_forall in h2, h4, h6, h9.
    assert (hmB : forall i, (i < 2)%nat -> @length (Zq * Zq) (nth i mB []) = kB) by (intros i hi; apply h6, nth_In; lia).
    assert (hmS : forall i, (i < 3)%nat -> @length (Zq * Zq) (nth i mS []) = kS) by (intros i hi; apply h9, nth_In; lia).
    assert (f7 : @length (Zq * Zq) qB = kB) by exact h7.
    assert (f10 : @length (Zq * Zq) qS = kS) by exact h10.
    assert (hLB : Forall (fun r => length r = kB) (LBd mB qB)).
    { unfold LBd, reZ, imZ. repeat constructor; rewrite length_map; first [apply hmB; lia | exact f7]. }
    assert (hLS : Forall (fun r => length r = kS) (LSd mS qS)).
    { unfold LSd, reZ, imZ. repeat constructor; rewrite length_map; first [apply hmS; lia | exact f10]. }
    rewrite Forall_forall in hLB, hLS.
    unfold dcok, dkz, drows_ok. cbn [dfB dpB dsB dmask dfS dpS dsS].
    split; [split; [reflexivity |] |].
    { apply Forall_map, Forall_forall. intros r hr. rewrite length_firstn, (hLB r hr). lia. }
    split; [split |].
    { rewrite length_app, !length_map, h1. unfold LBd. cbn [length]. unfold SOX. lia. }
    { apply Forall_app. split.
      - apply Forall_map, Forall_forall. intros p hpin. rewrite length_map. apply h2, hpin.
      - apply Forall_map, Forall_forall. intros r hr. rewrite length_skipn, (hLB r hr). lia. }
    split; [exact hsB |]. split; [rewrite length_map; exact hkm |].
    split; [split; [reflexivity |] |].
    { apply Forall_map, Forall_forall. intros r hr. rewrite length_firstn, (hLS r hr). lia. }
    split; [split |].
    { rewrite length_app, !length_map, h3. reflexivity. }
    { apply Forall_app. split.
      - apply Forall_map, Forall_forall. intros p hpin. rewrite length_map. apply h4, hpin.
      - apply Forall_map, Forall_forall. intros r hr. rewrite length_skipn, (hLS r hr). lia. }
    exact hsS.
  Qed.

End DCoins.

Lemma padrow_app : forall C (r p : list Z), padrow C r p = padrow C r [] ++ p.
Proof. intros C r p. unfold padrow. rewrite app_nil_r, app_assoc. reflexivity. Qed.

Lemma map_emb_Zof : forall p : list Zq, map to_F (map bx (map Zof p)) = map emb p.
Proof. intro p. rewrite !map_map. apply map_ext. apply emb_bx_Zof. Qed.

Lemma map_to_F_zm : forall l : list Z, map to_F (map bx (map zm l)) = map to_F (map bx l).
Proof. intro l. rewrite !map_map. apply map_ext. apply to_F_bx_zm. Qed.

Section DOpenZ.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k0 : dcoins.
  Variable km : list F.
  Variables (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F).

  Local Notation N := (2 ^ n1)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation kc := (dkz lo1 lo2 k0 km pB pS mB qB mS qS).
  Local Notation PFk := (PFD lo1 lo2 kd base nB nS omB omS off s e E kc).

  Hypothesis Hp : dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS.
  Hypothesis Hk0 : dcok n1 ell lo1 lo2 kd base nB nqB nS nqS k0.
  Hypothesis Hw : dwshape n1 ell s e E.
  Hypothesis Hkm : List.length km = n_maskD n1 ell kd base.
  Hypothesis Hsh : shapedD n1 ell lo1 kd kB nqB kS nqS pB pS mB qB mS qS.

  Lemma Hkc : dcok n1 ell lo1 lo2 kd base nB nqB nS nqS kc.
  Proof. exact (dkz_ok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS k0 Hp Hk0 km pB pS mB qB mS qS Hkm Hsh). Qed.

  (* the model's small data rows: s, e and the mask table *)
  Definition dSk (j : nat) : list Zq :=
    if Nat.eqb j 0 then sRowZ lo2 s else if Nat.eqb j 1 then eRowZ lo2 e else mrowZ lo2 km.

  Lemma LBd_len : forall j, (j < 6)%nat -> List.length (nth j (LBd mB qB) []) = kB.
  Proof.
    intros j hj. pose proof Hsh as (_ & _ & _ & _ & h5 & h6 & h7 & _). rewrite Forall_forall in h6.
    assert (hm : forall i, (i < 2)%nat -> @List.length (Zq * Zq) (nth i mB []) = kB) by (intros i hi; apply h6, nth_In; lia).
    assert (f7 : @List.length (Zq * Zq) qB = kB) by exact h7.
    unfold LBd, reZ, imZ. destruct j as [| [| [| [| [| [| j]]]]]]; try lia; cbn [nth]; rewrite length_map;
      first [apply hm; lia | exact f7].
  Qed.

  Lemma LSd_len : forall j, (j < 8)%nat -> List.length (nth j (LSd mS qS) []) = kS.
  Proof.
    intros j hj. pose proof Hsh as (_ & _ & _ & _ & _ & _ & _ & h8 & h9 & h10). rewrite Forall_forall in h9.
    assert (hm : forall i, (i < 3)%nat -> @List.length (Zq * Zq) (nth i mS []) = kS) by (intros i hi; apply h9, nth_In; lia).
    assert (f10 : @List.length (Zq * Zq) qS = kS) by exact h10.
    unfold LSd, reZ, imZ. destruct j as [| [| [| [| [| [| [| [| j]]]]]]]]; try lia; cbn [nth]; rewrite length_map;
      first [apply hm; lia | exact f10].
  Qed.

  (* the mask rows of the big matrix *)
  Lemma PFD_mB : forall j, (j < 6)%nat -> PFk (kd * rw + j) = map to_F (map bx (nth j (LBd mB qB) [])).
  Proof.
    intros j hj. pose proof Hkc as hkc. pose proof Hsh as (h1 & _).
    pose proof Hp as (hkB & _).
    destruct (msgsBD_shape n1 ell lo1 lo2 kd base nB nqB nS nqS off s e E kc hkc Hw) as [hlB _].
    unfold PFD. rewrite AMD_eq, app_nth1 by (rewrite hlB; unfold SOX; lia).
    pose proof (digrows_len n1 ell lo1 kd base off s e E Hw) as hdl.
    unfold msgsBD. rewrite ExecBackO.nth_msgs.
    2: { cbn [dkz dfB dpB]. rewrite !length_app, hdl, !length_map, h1. reflexivity. }
    2: { cbn [dkz dfB]. rewrite length_app, hdl, length_map. cbn. lia. }
    cbn [dkz dfB dpB].
    rewrite app_nth2 by (rewrite hdl; lia). rewrite hdl. replace (kd * rw + j - kd * rw)%nat with j by lia.
    rewrite app_nth2 by (rewrite length_map, h1; lia). rewrite length_map, h1.
    replace (kd * rw + j - kd * rw)%nat with j by lia.
    rewrite (nth_indep (map (firstn C1) (LBd mB qB)) [] (firstn C1 [])) by (rewrite length_map; cbn; lia).
    rewrite (nth_indep (map (skipn C1) (LBd mB qB)) [] (skipn C1 [])) by (rewrite length_map; cbn; lia).
    rewrite !map_nth. apply ExecZkOpen.padrow_full. rewrite LBd_len by exact hj. lia.
  Qed.

  (* the mask rows of the small matrix *)
  Lemma PFD_mS : forall j, (j < 8)%nat -> PFk (SO + 3 + j) = map to_F (map bx (nth j (LSd mS qS) [])).
  Proof.
    intros j hj. pose proof Hkc as hkc. pose proof Hsh as (_ & _ & h3 & _).
    pose proof Hp as (_ & hkS & _).
    destruct (msgsBD_shape n1 ell lo1 lo2 kd base nB nqB nS nqS off s e E kc hkc Hw) as [hlB _].
    unfold PFD. rewrite AMD_eq, app_nth2 by (rewrite hlB; lia). rewrite hlB.
    replace (SO + 3 + j - SO)%nat with (3 + j)%nat by lia.
    unfold msgsSD. rewrite ExecBackO.nth_msgs.
    2: { cbn [dkz dfS dpS]. rewrite !length_app, !length_map, h3. reflexivity. }
    2: { cbn [dkz dfS]. rewrite length_app, length_map. cbn. lia. }
    cbn [dkz dfS dpS].
    rewrite app_nth2 by (cbn; lia). cbn [List.length]. replace (3 + j - 3)%nat with j by lia.
    rewrite app_nth2 by (rewrite length_map, h3; lia). rewrite length_map, h3.
    replace (3 + j - 3)%nat with j by lia.
    rewrite (nth_indep (map (firstn C2) (LSd mS qS)) [] (firstn C2 [])) by (rewrite length_map; cbn; lia).
    rewrite (nth_indep (map (skipn C2) (LSd mS qS)) [] (skipn C2 [])) by (rewrite length_map; cbn; lia).
    rewrite !map_nth. apply ExecZkOpen.padrow_full. rewrite LSd_len by exact hj. lia.
  Qed.

  (* the data rows of the big matrix, with their pads *)
  Lemma PFD_dataB : forall i, (i < kd * rw)%nat -> PFk i = rowB n1 ell lo1 kd (dBr lo1 kd base off E) pB i.
  Proof.
    intros i hi. pose proof Hkc as hkc. pose proof Hsh as (h1 & _).
    destruct (msgsBD_shape n1 ell lo1 lo2 kd base nB nqB nS nqS off s e E kc hkc Hw) as [hlB _].
    pose proof (digrows_len n1 ell lo1 kd base off s e E Hw) as hdl.
    unfold PFD. rewrite AMD_eq, app_nth1 by (rewrite hlB; unfold SOX; lia).
    unfold msgsBD. rewrite ExecBackO.nth_msgs.
    2: { cbn [dkz dfB dpB]. rewrite !length_app, hdl, !length_map, h1. reflexivity. }
    2: { cbn [dkz dfB]. rewrite length_app, hdl, length_map. cbn. lia. }
    cbn [dkz dfB dpB].
    rewrite app_nth1 by (rewrite hdl; exact hi).
    rewrite app_nth1 by (rewrite length_map, h1; exact hi).
    rewrite (nth_indep (map (map Zof) pB) [] (map Zof [])) by (rewrite length_map, h1; exact hi).
    rewrite map_nth. rewrite padrow_app, !map_app, map_emb_Zof.
    unfold rowB, ZkDecOpen.datasB. rewrite nth_map_seq0 by exact hi. rewrite map_app. f_equal.
    unfold dBr, digrows. rewrite map_emb_zq. reflexivity.
  Qed.

  (* the data rows of the small matrix: s, e, the mask table *)
  Lemma PFD_dataS : forall j, (j < 3)%nat -> PFk (SO + j) = rowS n1 ell lo1 kd dSk pS (SO + j).
  Proof.
    intros j hj. pose proof Hkc as hkc. pose proof Hsh as (_ & _ & h3 & _).
    rewrite (PFD_small n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS off s e E kc hkc Hw j hj).
    cbn [dkz dpS]. rewrite app_nth1 by (rewrite length_map, h3; exact hj).
    rewrite (nth_indep (map (map Zof) pS) [] (map Zof [])) by (rewrite length_map, h3; exact hj).
    rewrite map_nth. rewrite padrow_app, !map_app, map_emb_Zof.
    unfold rowS, ZkDecOpen.datasS. replace (SO + j - (kd * rwD n1 ell lo1 + 6))%nat with j by (unfold SOX, rwX; lia).
    rewrite nth_map_seq0 by exact hj. rewrite map_app. f_equal.
    unfold dSk. destruct j as [| [| [| j]]]; try lia; cbn [Nat.eqb nth].
    - unfold sRowZ. rewrite map_emb_zq. reflexivity.
    - unfold eRowZ. rewrite map_emb_zq. reflexivity.
    - cbn [dkz]. unfold mask_rowD, mrowZ, padrow. cbn [dmask].
      rewrite app_nil_r, !map_app, map_to_F_zm.
      change (dmask kc) with (map of_F km).
      change (flat_map (fun x : Z * Z => [fst x; snd x]) (map of_F km)) with (mrow (map of_F km)).
      rewrite mrow_length, length_map. f_equal.
      + clear. induction km as [| z l ih]; [reflexivity |]. unfold mrow in ih |- *. unfold flatZ in ih |- *.
        cbn [map flat_map app]. rewrite ih. cbn [of_F fst snd]. rewrite !emb_bx_Zof. reflexivity.
      + rewrite !map_repeat. f_equal. rewrite emb_bx, zq_of_0. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the slot vectors *)

  Local Notation bBk := (btBD lo1 kd base nB omB off E kc).
  Local Notation bSk := (btSD lo2 nS omS s e kc).

  Lemma msD_mask : forall v, (1 <= v <= 5)%nat ->
    map to_F (msD n1 ell lo1 kd bBk bSk v) = nth (v - 1) (mB ++ mS) [].
  Proof.
    intros v hv. pose proof Hsh as (_ & _ & _ & _ & h5 & _ & _ & h8 & _).
    assert (eB : forall j, (j < 6)%nat -> PFk (kd * rw + j) = map to_F (map bx (nth j (LBd mB qB) [])))
      by (intros j hj; apply PFD_mB; exact hj).
    assert (eS : forall j, (j < 8)%nat -> PFk (SO + 3 + j) = map to_F (map bx (nth j (LSd mS qS) [])))
      by (intros j hj; apply PFD_mS; exact hj).
    pose proof (eB 0%nat ltac:(lia)) as b0. rewrite Nat.add_0_r in b0.
    pose proof (eS 0%nat ltac:(lia)) as s0. rewrite Nat.add_0_r in s0.
    assert (s1 : PFk (SO + 4) = map to_F (map bx (nth 1 (LSd mS qS) []))) by (rewrite <-(eS 1%nat) by lia; f_equal; lia).
    assert (s2 : PFk (SO + 5) = map to_F (map bx (nth 2 (LSd mS qS) []))) by (rewrite <-(eS 2%nat) by lia; f_equal; lia).
    assert (s3 : PFk (SO + 6) = map to_F (map bx (nth 3 (LSd mS qS) []))) by (rewrite <-(eS 3%nat) by lia; f_equal; lia).
    assert (s4 : PFk (SO + 7) = map to_F (map bx (nth 4 (LSd mS qS) []))) by (rewrite <-(eS 4%nat) by lia; f_equal; lia).
    assert (s5 : PFk (SO + 8) = map to_F (map bx (nth 5 (LSd mS qS) []))) by (rewrite <-(eS 5%nat) by lia; f_equal; lia).
    unfold msD. rewrite combD_msum. cbv beta in eB, b0, s0, s1, s2, s3, s4, s5.
    destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
    destruct mS as [| m3 [| m4 [| m5 [| ? ?]]]]; cbn in h8; try lia.
    destruct v as [| [| [| [| [| [| v]]]]]]; try lia; cbn [mcbX map pairF fst snd msum].
    - rewrite b0, (eB 1%nat) by lia. unfold LBd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list.
    - rewrite (eB 2%nat), (eB 3%nat) by lia. unfold LBd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list.
    - rewrite s0, s1. unfold LSd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list.
    - rewrite s2, s3. unfold LSd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list.
    - rewrite s4, s5. unfold LSd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the claims of a run, at its challenges T *)

  Variable T : dtrace.
  Hypothesis Hth : List.length (dt_th T) = ell.
  Hypothesis Hth1 : List.length (dt_th1 T) = n1.
  Hypothesis Hth2 : List.length (dt_th2 T) = n1.
  Hypothesis Hrz : List.length (dt_rz T) = m.
  Hypothesis Hrt : List.length (dt_rt T) = n1.
  Hypothesis Hkp : List.length (dt_kp T) = (kd + 6)%nat.
  Hypothesis Hlo1 : (lo1 <= m)%nat.

  Local Notation aFx := (map to_F (aDX a)).
  Local Notation ppFx := (to_F (bx pplain)).
  Local Notation usFx := (fun i => map to_F (nth i (usX us) [])).
  Local Notation ptDx := (map to_F (dt_th1 T ++ dt_th T)).
  Local Notation th2x := (map to_F (dt_th2 T)).
  Local Notation rzx := (map to_F (dt_rz T)).
  Local Notation rtx := (map to_F (dt_rt T)).
  Local Notation kpx := (map to_F (dt_kp T)).
  Local Notation ccx := (to_F (nth 0 (dt_cl T) xzero)).
  Local Notation cbDT := (cbD n1 ell lo1 kd base aFx ppFx usFx (dGX n1 ell base) (dTX n1) ptDx th2x rzx rtx kpx).
  Local Notation dBk := (dBr lo1 kd base off E).

  Lemma usD_run : forall v,
    map to_F (usD n1 ell lo1 kd base pplain a us bBk bSk (f1T T) v) = msumF PFk (cbDT v).
  Proof.
    intro v. unfold usD. rewrite combD_msum, to_F_cbk.
    unfold clsPD. cbn [dkp f1T front0].
    rewrite (clsF_T n1 ell lo1 kd base pplain a us T Hth Hth1 Hth2 Hrz Hrt). reflexivity.
  Qed.

  Lemma cb_rows : forall v iw, In iw (cbDT v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < kd * rw)%nat) /\ ((v = 3 \/ v = 4 \/ v = 5)%nat -> (SO <= fst iw < SO + 3)%nat).
  Proof.
    intros v iw h.
    exact (cbD_rows n1 ell lo1 kd base aFx ppFx usFx (dGX n1 ell base) (dTX n1) ptDx th2x rzx rtx
             ltac:(rewrite length_map, length_app; lia) ltac:(rewrite length_map; exact Hth2)
             ltac:(rewrite length_map; exact Hrz) ltac:(rewrite length_map; exact Hrt)
             (dGX_len n1 ell base) (dTX_len n1) Hlo1
             kpx ltac:(rewrite length_map; exact Hkp) v iw h).
  Qed.

  Local Notation vecTk := (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E kc T).

  (* slot vector v: the model's mask m_v plus c times the combination of the model's rows *)
  Lemma vec_run : forall v, (1 <= v <= 5)%nat ->
    map to_F (vecTk v)
    = padd (nth (v - 1) (mB ++ mS) [])
           (pscale ccx (msumF (if Nat.leb v 2 then rowB n1 ell lo1 kd dBk pB else rowS n1 ell lo1 kd dSk pS) (cbDT v))).
  Proof.
    intros v hv. unfold vecT, vecD. rewrite to_F_padd, to_F_pscale, msD_mask by exact hv. rewrite usD_run.
    f_equal. cbn [dc f1T front0]. f_equal. apply msum_ext. intros iw hiw.
    destruct (cb_rows v iw hiw) as [h12 h345].
    destruct (Nat.leb_spec v 2) as [hv2 | hv2].
    - apply PFD_dataB. apply h12. lia.
    - destruct (h345 ltac:(lia)) as [hlo hhi].
      replace (fst iw) with (SO + (fst iw - SO))%nat by lia. apply PFD_dataS. lia.
  Qed.

  Local Notation LkT := (LkD n1 ell lo1 kd base aFx ppFx usFx (dGX n1 ell base) (dTX n1) ptDx th2x rzx rtx kpx).

  Lemma LD_run : forall v, map to_F (LD n1 ell lo1 kd base pplain a us (f1T T) v) = LkT v.
  Proof.
    intro v. unfold LD. rewrite to_F_Lk. unfold clsPD. cbn [dkp f1T front0].
    rewrite (clsF_T n1 ell lo1 kd base pplain a us T Hth Hth1 Hth2 Hrz Hrt).
    unfold LkD. apply ExecBackO.Lk_ext. intro v'. apply (LtX_T n1 ell lo1 T Hth Hth1 Hrz).
  Qed.

  (* mu: the first component of the model's honest opening *)
  Lemma mu_run :
    to_F (muD n1 ell lo1 kd base pplain a us bBk bSk (f0T T))
    = fadd (@LogDer.fsum Fq2 fzero fadd (zipw (@LogDer.dot Fq2 fzero fadd fmul) mB [LkT 1; LkT 2]))
           (@LogDer.fsum Fq2 fzero fadd (zipw (@LogDer.dot Fq2 fzero fadd fmul) mS [LkT 3; LkT 4; LkT 5])).
  Proof.
    pose proof Hsh as (_ & _ & _ & _ & h5 & _ & _ & h8 & _).
    assert (hL : forall v, map to_F (LD n1 ell lo1 kd base pplain a us (f0T T) v) = LkT v)
      by (intro v; rewrite <-LD_run; reflexivity).
    assert (hm : forall v, (1 <= v <= 5)%nat -> map to_F (msD n1 ell lo1 kd bBk bSk v) = nth (v - 1) (mB ++ mS) [])
      by (intros v hv; apply msD_mask; exact hv).
    unfold muD. rewrite to_F_fsum. cbn [map]. rewrite !to_F_dot, !hL, !hm by lia.
    destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
    destruct mS as [| m3 [| m4 [| m5 [| ? ?]]]]; cbn in h8; try lia.
    cbn [zipw LogDer.fsum nth app Nat.sub]. ring.
  Qed.

  Local Notation gBx := (map to_F (dt_gB T)).
  Local Notation gSx := (map to_F (dt_gS T)).
  Hypothesis HgB : List.length (dt_gB T) = (kd * rw + 6)%nat.
  Hypothesis HgS : List.length (dt_gS T) = 11%nat.

  (* the proximity vector of the big matrix: proximity mask, gamma-combination of the data rows, mask rows *)
  Lemma pvB_run :
    map to_F (pvBD n1 ell lo1 kd bBk bSk (f1T T))
    = padd qB (padd (tpB n1 ell lo1 kd dBk gBx pB) (GB n1 ell lo1 kd gBx mB)).
  Proof.
    assert (eB : forall j, (j < 6)%nat -> PFk (kd * rw + j) = map to_F (map bx (nth j (LBd mB qB) [])))
      by (intros j hj; apply PFD_mB; exact hj).
    unfold pvBD. rewrite to_F_padd, !combD_msum. f_equal.
    { cbn [map msum pairF fst snd]. rewrite (eB 4%nat), (eB 5%nat) by lia. unfold LBd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list. }
    cbn [dgB f1T front0].
    rewrite ExecZkOpen.map_pairF_combine. unfold rwsBX. rewrite seq_app.
    rewrite ExecZkOpen.combine_split by (rewrite length_map, length_firstn, !length_seq, HgB; lia).
    rewrite ExecZkOpen.msum_app. rewrite length_seq. f_equal.
    - unfold tpB, cbPB. rewrite <-firstn_map, firstn_firstn.
      replace (Nat.min (kd * rw) (kd * rw + 4)) with (kd * rw)%nat by lia.
      apply msum_ext. intros iw hiw. destruct iw as [i w]. cbn [fst].
      apply in_combine_l, in_seq in hiw. apply PFD_dataB. unfold rwX, rwD in *. lia.
    - rewrite <-firstn_map, (ExecZkOpen.skipn_firstn4 (kd * rw) (map to_F (dt_gB T)) fzero) by (rewrite length_map; lia).
      assert (es : seq (0 + kd * rw) 4 = [kd * rw + 0; kd * rw + 1; kd * rw + 2; kd * rw + 3]%nat)
        by (cbn [seq]; f_equal; [lia | f_equal; [lia | f_equal; [lia | f_equal; lia]]]).
      rewrite es. cbn [combine msum fst snd].
      rewrite (eB 0%nat), (eB 1%nat), (eB 2%nat), (eB 3%nat) by lia. unfold LBd. cbn [nth].
      rewrite !ExecZkOpen.reZ_F, !ExecZkOpen.imZ_F, ExecZkOpen.padd_nil.
      unfold GB, Gm, gBi. rewrite Nat.add_0_r, !ExecZkOpen.padd_assoc. reflexivity.
  Qed.

  (* the proximity vector of the small matrix *)
  Lemma pvS_run :
    map to_F (pvSD n1 ell lo1 kd bBk bSk (f1T T))
    = padd qS (padd (tpS n1 ell lo1 kd dSk gSx pS) (GS gSx mS)).
  Proof.
    assert (eS : forall j, (j < 8)%nat -> PFk (SO + 3 + j) = map to_F (map bx (nth j (LSd mS qS) [])))
      by (intros j hj; apply PFD_mS; exact hj).
    unfold pvSD. rewrite to_F_padd, !combD_msum. f_equal.
    { cbn [map msum pairF fst snd].
      replace (SO + 9)%nat with (SO + 3 + 6)%nat by lia. replace (SO + 10)%nat with (SO + 3 + 7)%nat by lia.
      rewrite (eS 6%nat), (eS 7%nat) by lia. unfold LSd. cbn [nth].
      rewrite ExecZkOpen.reZ_F, ExecZkOpen.imZ_F, to_F_one, to_F_tg, ExecZkOpen.padd_nil. apply ExecZkOpen.re_im_list. }
    cbn [dgS f1T front0].
    rewrite ExecZkOpen.map_pairF_combine. unfold rwsSX.
    replace (seq 0 9) with (seq 0 3 ++ seq 3 6) by reflexivity. rewrite map_app.
    rewrite ExecZkOpen.combine_split by (rewrite !length_map, length_firstn, !length_seq, HgS; reflexivity).
    rewrite ExecZkOpen.msum_app. rewrite length_map, length_seq. f_equal.
    - unfold tpS, cbPS. rewrite <-firstn_map, firstn_firstn. cbn [Nat.min].
      apply msum_ext. intros iw hiw. destruct iw as [i w]. cbn [fst].
      apply in_combine_l, in_map_iff in hiw. destruct hiw as (j & <- & hj). apply in_seq in hj.
      apply (PFD_dataS j). lia.
    - assert (hl : List.length (map to_F (dt_gS T)) = 11%nat) by (rewrite length_map; exact HgS).
      rewrite <-firstn_map.
      remember (map to_F (dt_gS T)) as g eqn:eg.
      destruct g as [| g0 [| g1 [| g2 [| g3 [| g4 [| g5 [| g6 [| g7 [| g8 [| g9 [| g10 [| ? ?]]]]]]]]]]]]; cbn in hl; try lia.
      cbn [firstn skipn seq map combine msum fst snd].
      assert (hS : forall j i, (j < 8)%nat -> i = (SO + 3 + j)%nat -> PFk i = map to_F (map bx (nth j (LSd mS qS) [])))
        by (intros j i hj ->; apply eS; exact hj).
      rewrite (hS 0%nat (SO + 3)%nat), (hS 1%nat (SO + 4)%nat), (hS 2%nat (SO + 5)%nat), (hS 3%nat (SO + 6)%nat),
              (hS 4%nat (SO + 7)%nat), (hS 5%nat (SO + 8)%nat) by lia.
      unfold LSd. cbn [nth].
      rewrite !ExecZkOpen.reZ_F, !ExecZkOpen.imZ_F, ExecZkOpen.padd_nil.
      unfold GS, G3, Gm, gSi. cbn [nth Nat.add]. rewrite !ExecZkOpen.padd_assoc. reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the opened columns *)

  Local Notation omBK := (zq_of omB).
  Local Notation omSK := (zq_of omS).
  Local Notation JBn := (map Z.to_nat (dt_JB T)).
  Local Notation JSn := (map Z.to_nat (dt_JS T)).
  Local Notation encB := (@encJ Fq2 fzero fone fadd fmul (emb omBK) JBn).
  Local Notation encS := (@encJ Fq2 fzero fone fadd fmul (emb omSK) JSn).
  Local Notation openedK := (@opened Zq qzero qone qadd qmul).
  Local Notation XeT := (fun i j => to_F (dXe (dfmk n1 ell lo1 kd
                          (dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E kc T) T) i j)).

  Hypothesis HJBlt : forall j, In j JBn -> (j < nB)%nat.
  Hypothesis HJSlt : forall j, In j JSn -> (j < nS)%nat.

  Lemma XeB_at : forall i j, In j JBn -> (i < SO)%nat -> XeT i j = @eval Fq2 fzero fadd fmul (PFk i) (@pw Fq2 fone fmul (emb omBK) j).
  Proof.
    intros i j hj hi. cbv beta.
    rewrite (XeBD n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS pplain off a us s e E kc Hkc Hw T i j hj (HJBlt j hj) hi).
    rewrite emb_bx. reflexivity.
  Qed.

  Lemma XeS_at : forall i j, In j JSn -> (SO <= i < SO + 11)%nat ->
    XeT i j = @eval Fq2 fzero fadd fmul (PFk i) (@pw Fq2 fone fmul (emb omSK) j).
  Proof.
    intros i j hj hi. cbv beta.
    rewrite (XeSD n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS omB omS pplain off a us s e E kc Hp Hkc Hw T i j hj (HJSlt j hj) hi).
    rewrite emb_bx. reflexivity.
  Qed.

  (* a data row of the big matrix, at the opened columns: the model's opened entries *)
  Theorem colsB_data : forall i, (i < kd * rw)%nat ->
    map (XeT i) JBn = map emb (openedK omBK (nth i (ZkDecOpen.datasB n1 ell lo1 kd dBk) []) (nth i pB []) JBn).
  Proof.
    intros i hi. unfold ReedSolomon.opened. rewrite (map_map _ emb). apply map_ext_in. intros j hj.
    rewrite XeB_at by (first [exact hj | unfold SOX; lia]).
    rewrite PFD_dataB by exact hi. unfold rowB. apply ExecZkOpen.peval_emb_rs.
  Qed.

  (* the mask rows of the big matrix, at the opened columns: the model's encoded masks *)
  Theorem colsB_mask : forall j', (j' < 6)%nat ->
    map (XeT (kd * rw + j')) JBn
    = nth j' [map re (encB (nth 0 mB [])); map im (encB (nth 0 mB [])); map re (encB (nth 1 mB []));
              map im (encB (nth 1 mB [])); map re (encB qB); map im (encB qB)] [].
  Proof.
    intros j' hj'.
    transitivity (map (fun j => @eval Fq2 fzero fadd fmul (map to_F (map bx (nth j' (LBd mB qB) [])))
                                  (@pw Fq2 fone fmul (emb omBK) j)) JBn).
    { apply map_ext_in. intros j hj. rewrite XeB_at by (first [exact hj | unfold SOX; lia]).
      rewrite PFD_mB by exact hj'. reflexivity. }
    unfold ZkOpenTranscript.encJ.
    destruct j' as [| [| [| [| [| [| j']]]]]]; try lia; unfold LBd; cbn [nth];
      rewrite ?ExecZkOpen.reZ_F, ?ExecZkOpen.imZ_F, ?(map_map _ re), ?(map_map _ im); apply map_ext; intro j;
      first [apply ExecZkOpen.peval_re | apply ExecZkOpen.peval_im].
  Qed.

  (* a data row of the small matrix (row SO + j0), at the opened columns *)
  Theorem colsS_data : forall j0, (j0 < 3)%nat ->
    map (XeT (SO + j0)) JSn = map emb (openedK omSK (nth j0 (ZkDecOpen.datasS dSk) []) (nth j0 pS []) JSn).
  Proof.
    intros j0 hj0. unfold ReedSolomon.opened. rewrite (map_map _ emb). apply map_ext_in. intros j hj.
    rewrite XeS_at by (first [exact hj | lia]).
    rewrite PFD_dataS by exact hj0. unfold rowS.
    replace (SO + j0 - (kd * rwD n1 ell lo1 + 6))%nat with j0 by (unfold SOX, rwX; lia).
    apply ExecZkOpen.peval_emb_rs.
  Qed.

  (* the mask rows of the small matrix, at the opened columns *)
  Theorem colsS_mask : forall j', (j' < 8)%nat ->
    map (XeT (SO + 3 + j')) JSn
    = nth j' [map re (encS (nth 0 mS [])); map im (encS (nth 0 mS [])); map re (encS (nth 1 mS []));
              map im (encS (nth 1 mS [])); map re (encS (nth 2 mS [])); map im (encS (nth 2 mS []));
              map re (encS qS); map im (encS qS)] [].
  Proof.
    intros j' hj'.
    transitivity (map (fun j => @eval Fq2 fzero fadd fmul (map to_F (map bx (nth j' (LSd mS qS) [])))
                                  (@pw Fq2 fone fmul (emb omSK) j)) JSn).
    { apply map_ext_in. intros j hj. rewrite XeS_at by (first [exact hj | lia]).
      rewrite PFD_mS by exact hj'. reflexivity. }
    unfold ZkOpenTranscript.encJ.
    destruct j' as [| [| [| [| [| [| [| [| j']]]]]]]]; try lia; unfold LSd; cbn [nth];
      rewrite ?ExecZkOpen.reZ_F, ?ExecZkOpen.imZ_F, ?(map_map _ re), ?(map_map _ im); apply map_ext; intro j;
      first [apply ExecZkOpen.peval_re | apply ExecZkOpen.peval_im].
  Qed.

End DOpenZ.
