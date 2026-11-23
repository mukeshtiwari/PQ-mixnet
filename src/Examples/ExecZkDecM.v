(* The extracted decryption prover against the zero-knowledge model: one theorem for a
   whole prover run (the counterpart of ExecZkMain.v for the shuffle).

   For the prover's coins built from the model's coins,

     kc = dkz k0 (kmOf x) pB pS mB qB mS qS,

   (the layer coins x = (avs, (aG, csG), (aT, csT)): the masked-evaluation coefficients and
   the two sumcheck masks; the opening coins: pads, slot masks, proximity masks; the salts
   come from k0), every run of the extracted decryption prover (dptrans) returns a proof
   whose field elements are the model's honest transcript at the run's challenges T:

     layer    the masked evaluations, the G values and the sumcheck messages (as values at
              the nodes 0, 2, .., d) are those of honDL (ZkDecLayer.v);
     opening  mu, the slot vectors, the proximity vectors and the opened column entries are
              those of hon2D (ZkDecJoin.v).

   xdec_prove_refines. The model's honest transcripts are, over all coins, a permutation of
   the simulated ones (ZkDecJoin.v: dec_zk), at fixed challenges. Hashes, salts and Merkle
   paths are not modelled. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckMask MaskedExt RowLayout
  SlotKinds ZeroTest DecSound DecLayout ZkSumcheck ZkTranscript ZkDecLayer ZkOpen ZkOpenTranscript ZkJoin Opening
  OpenClaims ReedSolomon.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecDerive ExecVerify
  ExecProveBase ExecFold ExecRows ExecFront ExecDec ExecDecProve ExecDecComplete ZkOpenMix ZkMixJoin ZkDecOpen ZkDecJoin
  ExecZkSC ExecZkDecL ExecZkDecO.
From Examples Require ExecZkMain ExecZkOpen.
From Crypto Require ZkMix.
Import ListNotations.

Add Field fieldF2zdm : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation nF := (@nF Fq2 fzero fone fadd).
Local Notation evalF := (@PolyRoots.eval Fq2 fzero fadd fmul).
Local Notation encM := ExecZkMain.encM.

Lemma dGX_eq : forall n1 ell base, dGX n1 ell base = map (degZ (n1 + ell) base) (seq 0 (n1 + ell)).
Proof. intros n1 ell base. unfold dGX, degZ. apply map_ext. intro i. destruct (Nat.eqb (S i) (n1 + ell)); lia. Qed.

Lemma dTX_eq : forall n1, dTX n1 = map (degZ n1 3) (seq 0 n1).
Proof. intro n1. unfold dTX, degZ. apply map_ext. intro i. destruct (Nat.eqb (S i) n1); reflexivity. Qed.

Lemma msgs_listD : forall (ms : list (list xf)) (ds : list nat) (hm : list (list F)),
  List.length ms = List.length ds -> List.length hm = List.length ds ->
  (forall i, (i < List.length ds)%nat ->
     map to_F (nth i ms []) = map (fun c => evalF (nth i hm []) (nF c)) (spoints (nth i ds 0%nat))) ->
  map (map to_F) ms = encM ds hm.
Proof.
  intros ms ds hm hl1 hl2 h. apply nth_ext with (d := []) (d' := []).
  - rewrite length_map, hl1. unfold ExecZkMain.encM. rewrite zipw_length by (symmetry; exact hl2). reflexivity.
  - intros i hi. rewrite length_map, hl1 in hi.
    unfold ExecZkMain.encM. rewrite (nth_zipw _ ds hm i 0%nat [] []) by (first [exact hi | symmetry; exact hl2]).
    rewrite <-h by exact hi.
    rewrite (nth_indep _ [] (map to_F [])) by (rewrite length_map; lia). apply map_nth.
Qed.

Lemma mask_ofD_flat : forall ds a0 (cs : list (list F)) rest, @shaped F ds cs ->
  mask_ofD ds (map of_F ((a0 :: List.concat cs) ++ rest)) = (of_F a0, map (map of_F) cs).
Proof.
  intros ds a0 cs rest h. unfold mask_ofD. cbn [app map nth tl].
  rewrite map_app, concat_map. rewrite cuts_concat; [reflexivity |].
  unfold shaped in h. clear -h. induction h as [| d l ds cs hl h ih]; constructor; [| exact ih].
  rewrite length_map. exact hl.
Qed.

(* the model's round interpolants read only the first kd + 2 mask coefficients *)
Lemma pfG_app : forall n1 ell base (dts : list (list F -> F)) tz kG avs rest pre,
  (List.length dts <= List.length avs)%nat ->
  @pfG Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dts tz kG (avs ++ rest) pre
  = @pfG Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dts tz kG avs pre.
Proof.
  intros n1 ell base dts tz kG avs rest pre h. unfold pfG, fG.
  rewrite firstn_app. replace (List.length dts - List.length avs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

Lemma pfT_app : forall n1 (dts : list (list F -> F)) stab etab tt kT avs rest pre,
  List.length avs = (List.length dts + 2)%nat ->
  @pfT Fq2 fzero fone fadd fmul fsub fopp finv n1 dts stab etab tt kT (avs ++ rest) pre
  = @pfT Fq2 fzero fone fadd fmul fsub fopp finv n1 dts stab etab tt kT avs pre.
Proof.
  intros n1 dts stab etab tt kT avs rest pre h. unfold pfT. f_equal.
  unfold rvals. apply map_ext. intro i. unfold Sumcheck.rnd. f_equal. apply map_ext. intro bq.
  unfold fT, gZ. rewrite skipn_app. replace (List.length dts - List.length avs)%nat with 0%nat by lia. rewrite skipn_O.
  assert (hl : List.length (skipn (List.length dts) avs) = 2%nat) by (rewrite length_skipn; lia).
  destruct (skipn (List.length dts) avs) as [| a0 [| a1 [| ? ?]]]; cbn in hl; try lia.
  f_equal. f_equal. destruct kT as [| k0 [| k1 [| k2 kT']]]; reflexivity.
Qed.

Section Main.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k0 : dcoins.
  Variables (avs : list F) (aG aT : F) (csG csT : list (list F)).
  Variables (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F).

  Local Notation N := (2 ^ n1)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation dG := (dGX n1 ell base).
  Local Notation dT := (dTX n1).

  Hypothesis Hp : dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS.
  Hypothesis Hk0 : dcok n1 ell lo1 lo2 kd base nB nqB nS nqS k0.
  Hypothesis Hw : dwshape n1 ell s e E.
  Hypothesis Hn1 : (1 <= n1)%nat.
  Hypothesis HbaseQ : (Z.of_nat (Nat.max (2 * base + 2) 8) < Q)%Z.
  Hypothesis Hdmax : (2 * base + 1 <= DMAX)%nat.
  Hypothesis Hlo1 : (lo1 <= m)%nat.
  Hypothesis Hts : ternZ s.
  Hypothesis Hte : ternZ e.
  Hypothesis Havs : List.length avs = (kd + 2)%nat.
  Hypothesis HcG : @shaped F dG csG.
  Hypothesis HcT : @shaped F dT csT.
  Hypothesis Hsh : shapedD n1 ell lo1 kd kB nqB kS nqS pB pS mB qB mS qS.

  Local Notation xL := (avs, ((aG, csG), (aT, csT))).
  Local Notation km := (kmOf xL).
  Local Notation kc := (dkz lo1 lo2 k0 km pB pS mB qB mS qS).
  Local Notation restL := ((aG :: List.concat csG) ++ (aT :: List.concat csT)).

  Lemma km_lenD : List.length km = n_maskD n1 ell kd base.
  Proof using Havs HcG HcT.
    clear -Havs HcG HcT.
    unfold kmOf. cbn [fst snd]. rewrite !length_app. cbn [List.length].
    rewrite (concat_length_shaped _ _ HcG), (concat_length_shaped _ _ HcT), Havs. unfold n_maskD. lia.
  Qed.

  Lemma Hkc : dcok n1 ell lo1 lo2 kd base nB nqB nS nqS kc.
  Proof. exact (dkz_ok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS k0 Hp Hk0 km pB pS mB qB mS qS km_lenD Hsh). Qed.

  Lemma avs_kc : map to_F (dmask kc) = avs ++ restL.
  Proof. cbn [dkz dmask]. rewrite map_to_F_of_F. reflexivity. Qed.

  Lemma gG_kc : gGD n1 ell kd base kc = (of_F aG, map (map of_F) csG).
  Proof using Havs HcG.
    clear -Havs HcG.
    unfold gGD. cbn [dkz dmask]. unfold kmOf. cbn [fst snd].
    rewrite skipn_map, <-Havs, skipn_app, Nat.sub_diag, skipn_all, skipn_O. cbn [app].
    apply mask_ofD_flat. exact HcG.
  Qed.

  Lemma gT_kc : gTD n1 ell kd base kc = (of_F aT, map (map of_F) csT).
  Proof using Havs HcG HcT.
    clear -Havs HcG HcT.
    unfold gTD. cbn [dkz dmask]. unfold kmOf. cbn [fst snd].
    rewrite app_assoc, skipn_map.
    assert (hl : List.length (avs ++ aG :: List.concat csG) = (kd + 3 + list_sum dG)%nat)
      by (rewrite length_app; cbn [List.length]; rewrite (concat_length_shaped _ _ HcG), Havs; lia).
    rewrite <-hl, skipn_app, Nat.sub_diag, skipn_all, skipn_O. cbn [app].
    rewrite <-(app_nil_r (aT :: List.concat csT)). apply mask_ofD_flat. exact HcT.
  Qed.

  Local Notation dptransx := (dptrans n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS tag pplain off a b us ts s e E kc).

  (* the lengths of the challenges of a run *)
  Lemma T_shapeD : forall P T, dptransx P T ->
    List.length (dt_th T) = ell /\ List.length (dt_th1 T) = n1 /\ List.length (dt_th2 T) = n1
    /\ List.length (dt_tz T) = m /\ List.length (dt_kG T) = kd /\ List.length (dt_rhoG T) = 1%nat
    /\ List.length (dt_tt T) = n1 /\ List.length (dt_kT T) = 2%nat /\ List.length (dt_rhoT T) = 1%nat
    /\ List.length (dt_rz T) = m /\ List.length (dt_rt T) = n1 /\ List.length (dt_kp T) = (kd + 6)%nat
    /\ List.length (dt_gB T) = (kd * rw + 6)%nat /\ List.length (dt_gS T) = 11%nat
    /\ (forall j, In j (map Z.to_nat (dt_JB T)) -> (j < nB)%nat)
    /\ (forall j, In j (map Z.to_nat (dt_JS T)) -> (j < nS)%nat).
  Proof.
    intros P T hT.
    destruct hT as (_ & hdr & _ & _ & (c0G & c1G & eG) & (c0T & c1T & eT) & _).
    unfold ddrawn in hdr. cbv zeta in hdr.
    destruct hdr as (dth & dth1 & dth2 & dtz & dkG & drG & dtt & dkT & drT & dkp & _ & dgB & dgS & dJB & dJS).
    assert (gl : forall nm n x, (exists c c', get_F c (sb nm) n = Some (x, c')) -> List.length x = n)
      by (intros nm n x (c & c' & h); exact (proj1 (get_F_shape _ _ _ _ _ h))).
    pose proof Hp as (_ & _ & hnB & _ & hnS & _).
    split; [exact (gl _ _ _ dth) |]. split; [exact (gl _ _ _ dth1) |]. split; [exact (gl _ _ _ dth2) |].
    split; [exact (gl _ _ _ dtz) |]. split; [exact (gl _ _ _ dkG) |]. split; [exact (gl _ _ _ drG) |].
    split; [exact (gl _ _ _ dtt) |]. split; [exact (gl _ _ _ dkT) |]. split; [exact (gl _ _ _ drT) |].
    split; [rewrite (ExecZkSC.sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eG); cbn; apply dGX_len |].
    split; [rewrite (ExecZkSC.sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eT); cbn; apply dTX_len |].
    split; [exact (gl _ _ _ dkp) |]. split; [exact (gl _ _ _ dgB) |]. split; [exact (gl _ _ _ dgS) |].
    split; apply Forall_forall.
    - exact (drawn_indices _ _ _ _ _ hnB dJB).
    - exact (drawn_indices _ _ _ _ _ hnS dJS).
  Qed.

  Local Notation dtsWx := (dtsW n1 ell lo1 lo2 kd base off s e E).
  Local Notation stabWx := (stabW n1 ell lo1 lo2 kd base off s e E).
  Local Notation etabWx := (etabW n1 ell lo1 lo2 kd base off s e E).
  Local Notation VL := (fun T => @honDL Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dtsWx stabWx etabWx
                                   (map to_F (dt_tz T)) (map to_F (dt_kG T)) (map to_F (dt_rz T))
                                   (map to_F (dt_tt T)) (map to_F (dt_kT T)) (map to_F (dt_rt T))
                                   (to_F (nth 0 (dt_rhoG T) xzero)) (to_F (nth 0 (dt_rhoT T) xzero)) xL).

  Lemma dtsW_len : List.length dtsWx = kd.
  Proof. unfold dtsW, dtsT. rewrite length_map, length_seq. reflexivity. Qed.

  (* the layer: masked evaluations, G values, sumcheck messages *)
  Theorem layer_refinesD : forall P T, dptransx P T ->
    map to_F (pzG P ++ pzT P) = fst (VL T)
    /\ map to_F (pG P) = [fst (fst (snd (VL T))); fst (snd (snd (VL T)))]
    /\ map (map to_F) (pmG P) = encM dG (snd (fst (snd (VL T))))
    /\ map (map to_F) (pmT P) = encM dT (snd (snd (snd (VL T)))).
  Proof.
    intros P T hT.
    destruct (T_shapeD P T hT) as (hth & hth1 & hth2 & htz & hkG & hrG & htt & hkT & hrT & hrz & hrt & _).
    pose proof hT as (eP & _ & _ & _ & (c0G & c1G & eG) & (c0T & c1T & eT) & _).
    pose proof Hkc as hkc.
    pose proof (evals_runD n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS off s e E kc Hp hkc Hw Hn1 HbaseQ Hdmax
                  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hts Hte htz hkG hrG htt hkT hrT eG eT) as hev.
    pose proof (G_runD n1 ell kd base kc Hn1 HbaseQ) as hG.
    pose proof (fun i => msgsG_run n1 ell lo1 lo2 kd base nB nqB nS nqS off s e E kc hkc Hw Hn1 HbaseQ
                           _ _ _ _ _ _ _ _ htz hkG eG i) as hmG.
    pose proof (fun i => msgsT_run n1 ell lo1 lo2 kd base nB nqB nS nqS off s e E kc hkc Hw Hn1 HbaseQ
                           _ _ _ _ _ _ _ _ htt hkT eT i) as hmT.
    pose proof (ExecZkSC.sc_loop_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eG) as [_ lG].
    pose proof (ExecZkSC.sc_loop_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eT) as [_ lT].
    rewrite avs_kc in hev, hmG, hmT. rewrite gG_kc in hG, hmG. rewrite gT_kc in hG, hmT.
    cbn [fst snd] in hG, hmG, hmT. rewrite !to_F_of_F, !csF_of_F in hG. rewrite !to_F_of_F, !csF_of_F in hmG. rewrite !to_F_of_F, !csF_of_F in hmT.
    rewrite eP. cbn [pzG pzT pG pmG pmT dparts_of].
    unfold honDL, honL2, honT. cbn [fst snd].
    split; [| split; [| split]].
    - rewrite hev. apply ExecZkMain.evs_app. unfold specsD. rewrite length_app, length_map, dtsW_len, Havs. reflexivity.
    - exact hG.
    - apply msgs_listD.
      + exact lG.
      + unfold ZkSumcheck.hmsgs. rewrite length_map, length_seq. symmetry. apply dGX_len.
      + intros i hi. rewrite dGX_len in hi. rewrite ExecZkMain.hmsgs_nth by exact hi. rewrite hmG by exact hi.
        apply map_ext. intro c. f_equal. unfold hmsg. rewrite pfG_app by (rewrite dtsW_len, Havs; lia). reflexivity.
    - apply msgs_listD.
      + exact lT.
      + unfold ZkSumcheck.hmsgs. rewrite length_map, length_seq. symmetry. apply dTX_len.
      + intros i hi. rewrite dTX_len in hi. rewrite ExecZkMain.hmsgs_nth by exact hi. rewrite hmT by exact hi.
        apply map_ext. intro c. f_equal. unfold hmsg. rewrite pfT_app by (rewrite dtsW_len, Havs; lia). reflexivity.
  Qed.

  Local Notation yO := (pB, pS, ((mB, qB), (mS, qS))).
  Local Notation hon2Dx := (fun T => hon2D n1 ell lo1 lo2 kd base (zq_of omB) (zq_of omS) (dBr lo1 kd base off E)
                                       (sRowZ lo2 s) (eRowZ lo2 e) (map to_F (aDX a)) (to_F (bx pplain))
                                       (fun i => map to_F (nth i (usX us) []))
                                       (map to_F (dt_th T)) (map to_F (dt_th1 T)) (map to_F (dt_th2 T))
                                       (map to_F (dt_rz T)) (map to_F (dt_rt T)) (map to_F (dt_kp T))
                                       (to_F (nth 0 (dt_cl T) xzero)) (map to_F (dt_gB T)) (map to_F (dt_gS T))
                                       (dt_JB T) (dt_JS T) xL).
  Local Notation XeP := (fun P T i j => to_F (dXe (dfmk n1 ell lo1 kd P T) i j)).
  Local Notation JBn := (fun T => map Z.to_nat (dt_JB T)).
  Local Notation JSn := (fun T => map Z.to_nat (dt_JS T)).

  (* the opening: mu, slot vectors, proximity vectors, opened columns *)
  Theorem open_refinesD : forall P T, dptransx P T ->
    match hon2Dx T yO with
    | (mu, ((vB, pvB0), (vS, pvS0)), (ysB, ysS), ((eB, eqB), (eS, eqS))) =>
        to_F (pmu P) = mu
        /\ [map to_F (pvS1 P); map to_F (pvS2 P)] = vB
        /\ [map to_F (pvSs P); map to_F (pvSe P); map to_F (pvSm P)] = vS
        /\ map to_F (ppvB P) = pvB0 /\ map to_F (ppvS P) = pvS0
        /\ (forall i, (i < kd * rw)%nat -> map (XeP P T i) (JBn T) = map emb (nth i ysB []))
        /\ (forall j', (j' < 6)%nat -> map (XeP P T (kd * rw + j')) (JBn T)
              = nth j' [map re (nth 0 eB []); map im (nth 0 eB []); map re (nth 1 eB []); map im (nth 1 eB []);
                        map re eqB; map im eqB] [])
        /\ (forall j0, (j0 < 3)%nat -> map (XeP P T (SO + j0)) (JSn T) = map emb (nth j0 ysS []))
        /\ (forall j', (j' < 8)%nat -> map (XeP P T (SO + 3 + j')) (JSn T)
              = nth j' [map re (nth 0 eS []); map im (nth 0 eS []); map re (nth 1 eS []); map im (nth 1 eS []);
                        map re (nth 2 eS []); map im (nth 2 eS []); map re eqS; map im eqS] [])
    end.
  Proof.
    intros P T hT.
    destruct (T_shapeD P T hT) as (hth & hth1 & hth2 & htz & hkG & hrG & htt & hkT & hrT & hrz & hrt & hkp & hgB & hgS & hJB & hJS).
    pose proof hT as (eP & _).
    pose proof km_lenD as hkm.
    unfold hon2D, honDO, ZkJoin.honO3. cbv beta iota.
    rewrite eP. cbn [pmu pvS1 pvS2 pvSs pvSe pvSm ppvB ppvS dparts_of].
    rewrite <-dGX_eq, <-dTX_eq, <-map_app.
    change (dSx lo2 (sRowZ lo2 s) (eRowZ lo2 e) xL) with (dSk lo2 s e km).
    assert (hv : forall v, (1 <= v <= 5)%nat -> _)
      by (intros v hv; exact (vec_run n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS omB omS pplain off a us s e E k0 km
                                pB pS mB qB mS qS Hp Hk0 Hw hkm Hsh T hth hth1 hth2 hrz hrt hkp Hlo1 v hv)).
    pose proof Hsh as (h1 & _ & h3 & _ & h5 & _ & _ & h8 & _).
    split; [unfold LsB, LsS; apply (mu_run n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS); assumption |].
    split; [rewrite (hv 1%nat), (hv 2%nat) by lia; destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia;
            unfold tfunB; reflexivity |].
    split; [rewrite (hv 3%nat), (hv 4%nat), (hv 5%nat) by lia; destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia;
            destruct mS as [| m3 [| m4 [| m5 [| ? ?]]]]; cbn in h8; try lia; unfold tfunS; reflexivity |].
    split; [apply (pvB_run n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS); assumption |].
    split; [apply (pvS_run n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS); assumption |].
    split; [| split; [| split]].
    - intros i hi. rewrite (nth_zipw _ (datasB n1 ell lo1 kd (dBr lo1 kd base off E)) pB i [] [] []).
      + apply (colsB_data n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS); assumption.
      + unfold ZkDecOpen.datasB. rewrite length_map, length_seq. exact hi.
      + unfold ZkDecOpen.datasB. rewrite length_map, length_seq, h1. reflexivity.
    - intros j' hj'. rewrite (colsB_mask n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS) by assumption.
      destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia. reflexivity.
    - intros j0 hj0. rewrite (nth_zipw _ (datasS (dSk lo2 s e km)) pS j0 [] [] []).
      + apply (colsS_data n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS); assumption.
      + exact hj0.
      + rewrite h3. reflexivity.
    - intros j' hj'. rewrite (colsS_mask n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS) by assumption.
      destruct mS as [| m3 [| m4 [| m5 [| ? ?]]]]; cbn in h8; try lia. reflexivity.
  Qed.

  (* a whole run: every field element of the decryption proof is the model's honest transcript
     at the run's challenges *)
  Theorem xdec_prove_refines : forall P T, dptransx P T ->
    (map to_F (pzG P ++ pzT P) = fst (VL T)
     /\ map to_F (pG P) = [fst (fst (snd (VL T))); fst (snd (snd (VL T)))]
     /\ map (map to_F) (pmG P) = encM dG (snd (fst (snd (VL T))))
     /\ map (map to_F) (pmT P) = encM dT (snd (snd (snd (VL T)))))
    /\ match hon2Dx T yO with
       | (mu, ((vB, pvB0), (vS, pvS0)), (ysB, ysS), ((eB, eqB), (eS, eqS))) =>
           to_F (pmu P) = mu
           /\ [map to_F (pvS1 P); map to_F (pvS2 P)] = vB
           /\ [map to_F (pvSs P); map to_F (pvSe P); map to_F (pvSm P)] = vS
           /\ map to_F (ppvB P) = pvB0 /\ map to_F (ppvS P) = pvS0
           /\ (forall i, (i < kd * rw)%nat -> map (XeP P T i) (JBn T) = map emb (nth i ysB []))
           /\ (forall j', (j' < 6)%nat -> map (XeP P T (kd * rw + j')) (JBn T)
                 = nth j' [map re (nth 0 eB []); map im (nth 0 eB []); map re (nth 1 eB []); map im (nth 1 eB []);
                           map re eqB; map im eqB] [])
           /\ (forall j0, (j0 < 3)%nat -> map (XeP P T (SO + j0)) (JSn T) = map emb (nth j0 ysS []))
           /\ (forall j', (j' < 8)%nat -> map (XeP P T (SO + 3 + j')) (JSn T)
                 = nth j' [map re (nth 0 eS []); map im (nth 0 eS []); map re (nth 1 eS []); map im (nth 1 eS []);
                           map re (nth 2 eS []); map im (nth 2 eS []); map re eqS; map im eqS] [])
       end.
  Proof. intros P T hT. split; [exact (layer_refinesD P T hT) | exact (open_refinesD P T hT)]. Qed.

End Main.
