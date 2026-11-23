(* The extracted prover against the model (zero knowledge for the running
   code, step 6): one theorem for a whole prover run.

   For the prover's coins built from the model's coins,

     kc = kz (kOf' k0 avs aA csA aB csB aC csC) pB pS mB qB mS qS,

   (the layer coins: the masked-evaluation coefficients avs and the three
   sumcheck masks; the opening coins: pads, slot masks, proximity masks;
   the salts come from k0), every run of the extracted prover (ptrans)
   returns a proof whose field elements are the model's honest transcript
   at the run's challenges T:

     layer    the masked evaluations, the G values and the sumcheck
              messages (as values at the nodes 0, 2, .., d) are those of
              honLx (ZkLayer.v);
     opening  mu, the slot vectors, the proximity vectors and the opened
              column entries are those of honMix (ZkOpenMix.v).

   xmix_prove_refines. The model's honest transcripts are, over all coins,
   a permutation of the simulated ones (ZkMixJoin.v: mix_zk), at fixed
   challenges. Hashes, salts and Merkle paths are not modelled. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Utility Require Import Zpstar.
From Crypto Require Import Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckMask MaskedExt MixSummands LayoutLemmas Interp RowLayout ZkBlocks ZkSumcheck ZkMix ZkTranscript ZkOpen ZkOpenTranscript ZkJoin ReedSolomon Opening.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecVerify ExecProveBase ExecFold ExecFront ExecProve ExecBack ExecBackD ExecBackO ZkLayer ZkOpenMix ZkMixJoin ExecZkSC ExecZkTables ExecZkMsgs ExecZkOpen.
Import ListNotations.

Local Notation F := Fq2.

(* the messages as values at the nodes *)
Definition encM (ds : list nat) (hm : list (list F)) : list (list F) :=
  zipw (fun d p => map (fun c => @eval Fq2 fzero fadd fmul p (@nF Fq2 fzero fone fadd c)) (spoints d)) ds hm.

Lemma evs_app : forall (specs : list (@evspec Fq2)) avs rest, length avs = length specs ->
  @evs Fq2 fzero fone fadd fmul fsub specs (avs ++ rest) = @evs Fq2 fzero fone fadd fmul fsub specs avs.
Proof.
  induction specs as [| s specs ih]; intros avs rest h; destruct avs as [| x avs]; cbn in h; try lia; [reflexivity |].
  cbn [app evs]. rewrite ih by lia. reflexivity.
Qed.

Lemma nth7 : forall (avs rest : list F) i, length avs = 7%nat -> (i < 7)%nat -> nth i (avs ++ rest) fzero = nth i avs fzero.
Proof. intros avs rest i h hi. apply app_nth1. lia. Qed.

Section Main.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable sigma : list nat.
  Variable k0 : coins.

  Local Notation m := (n1 + ell)%nat.

  (* the model summands only read the first seven mask coefficients *)
  Lemma pf_app : forall avs rest, length avs = 7%nat ->
    forall ru rv al be tc kA rA tz kC,
      pfA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA (avs ++ rest)
      = pfA ell pplain a b cin cout sig wr we1 we2 ru rv al be tc kA avs
    /\ pfB n1 ell pplain a b wr we1 we2 ru rv rA (avs ++ rest) = pfB n1 ell pplain a b wr we1 we2 ru rv rA avs
    /\ pfC n1 ell wr we1 we2 tz kC (avs ++ rest) = pfC n1 ell wr we1 we2 tz kC avs.
  Proof.
    intros avs rest h7 ru rv al be tc kA rA tz kC.
    destruct avs as [| x0 [| x1 [| x2 [| x3 [| x4 [| x5 [| x6 [| ? ?]]]]]]]]; cbn in h7; try lia.
    cbn [app]. unfold pfA, pfB, pfC, fA, fB, fC, cBv. cbn [nth]. split; [| split]; reflexivity.
  Qed.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation SO := (SOE n1 ell lo1).
  Local Notation dsA := (map (MixSummands.degA ell) (seq 0 ell)).
  Local Notation dsB := (map (fun _ : nat => 2%nat) (seq 0 n1)).
  Local Notation dsC := (map (MixSummands.degC m) (seq 0 m)).

  Variables (avs : list F) (aA aB aC : F) (csA csB csC : list (list F)).
  Variables (pB pS : list (list Zq)) (mB mS : list (list F)) (qB qS : list F).

  Hypothesis Hval : valid n1 ell pplain a b cin cout sig wr we1 we2 sigma.
  Hypothesis Hw : witness_shape n1 ell cout sig wr we1 we2.
  Hypothesis Hs : stmt_ok n1 ell a b cin.
  Hypothesis Hp : params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS.
  Hypothesis Hk0 : coins_ok n1 ell lo1 lo2 nB nqB nS nqS k0.
  Hypothesis Havs : length avs = 7%nat.
  Hypothesis HcA : @shaped F dsA csA.
  Hypothesis HcB : @shaped F dsB csB.
  Hypothesis HcC : @shaped F dsC csC.
  Hypothesis Hsh : shapedZ n1 ell lo1 lo2 kB nqB kS nqS pB pS mB qB mS qS.

  Local Notation kx := (kOf' k0 avs aA csA aB csB aC csC).
  Local Notation kc := (kz ell lo1 lo2 kx pB pS mB qB mS qS).

  Lemma cok_kx : coins_ok n1 ell lo1 lo2 nB nqB nS nqS kx.
  Proof.
    destruct Hk0 as (h1 & h2 & h3 & h4 & h5 & h6 & _ & h8 & h9).
    unfold coins_ok. cbn [kOf' kfB kpB ksB kfS kpS1 ksS1 kmask kpS2 ksS2].
    exact (conj h1 (conj h2 (conj h3 (conj h4 (conj h5 (conj h6
             (conj (km_len n1 ell k0 avs aA aB aC csA csB csC Havs HcA HcB HcC) (conj h8 h9)))))))).
  Qed.

  Lemma cok_kc : coins_ok n1 ell lo1 lo2 nB nqB nS nqS kc.
  Proof. exact (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS kx Hp cok_kx pB pS mB qB mS qS Hsh). Qed.

  Local Notation restF := (mflat (aA, csA) ++ mflat (aB, csB) ++ mflat (aC, csC)).

  Lemma km_kc : map to_F (kmask kc) = avs ++ restF.
  Proof. cbn [kz kOf' kmask]. unfold kmaskOf'. apply map_to_F_of_F. Qed.

  Local Notation ptransx := (ptrans n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 kc get_F get_I).

  (* the lengths of the challenges of a run *)
  Lemma T_shape : forall P T, ptransx P T ->
    length (tru T) = N /\ length (trv T) = N /\ length (trA T) = ell /\ length (try T) = n1
    /\ length (trz T) = m /\ length (tkp T) = 9%nat /\ length (tgB T) = (3 * rw + 6)%nat
    /\ length (tgS T) = (rs + 6 + (4 * rs + 1))%nat
    /\ (forall j, In j (map Z.to_nat (tJB T)) -> (j < nB)%nat)
    /\ (forall j, In j (map Z.to_nat (tJS T)) -> (j < nS)%nat).
  Proof.
    intros P T hT.
    destruct hT as (_ & hdr & _ & _ & _ & (c0A & c1A & eA) & (c0B & fB0 & c1B & eB) & (c0C & c1C & eC) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & _ & _ & _ & _ & _ & _ & _ & _ & dkp & _ & dgB & dgS & dJB & dJS).
    assert (gl : forall nm n x, (exists c c', get_F c (sb nm) n = Some (x, c')) -> length x = n)
      by (intros nm n x (c & c' & h); exact (proj1 (get_F_shape _ _ _ _ _ h))).
    pose proof Hp as (_ & _ & hnB & _ & hnS & _).
    split; [exact (gl _ _ _ dru) |]. split; [exact (gl _ _ _ drv) |].
    split; [rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eA); cbn; apply ExecBackD.dA_len |].
    split; [rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB); cbn; apply ExecBackD.dB_len |].
    split; [rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eC); cbn; apply ExecBackD.dC_len |].
    split; [exact (gl _ _ _ dkp) |]. split; [exact (gl _ _ _ dgB) |]. split; [exact (gl _ _ _ dgS) |].
    split; apply Forall_forall.
    - exact (drawn_indices _ _ _ _ _ hnB dJB).
    - exact (drawn_indices _ _ _ _ _ hnS dJS).
  Qed.

  Local Notation xL := (avs, ((aA, csA), ((aB, csB), (aC, csC)))).
  Local Notation VL := (fun T => honLx n1 ell pplain a b cin cout sig wr we1 we2 (tru T) (trv T)
                                   (ExecProve.alT T) (ExecProve.beT T) (ttc T) (tkA T)
                                   (nth 0 (trhoA T) xzero) (nth 0 (trhoB T) xzero) (nth 0 (trhoC T) xzero)
                                   (trA T) (try T) (ttz T) (tkC T) (trz T) xL).

  Lemma hmsgs_nth : forall mm pf rho a0 cs rs i, (i < mm)%nat ->
    nth i (@hmsgs Fq2 fzero fone fadd fmul mm pf rho a0 cs rs) [] = @hmsg Fq2 fzero fone fadd fmul mm pf rho a0 cs rs i.
  Proof.
    intros mm pf rho a0 cs rs i hi. unfold ZkSumcheck.hmsgs.
    rewrite (nth_indep _ [] (@hmsg Fq2 fzero fone fadd fmul mm pf rho a0 cs rs 0)) by (rewrite length_map, length_seq; exact hi).
    rewrite map_nth, seq_nth by exact hi. reflexivity.
  Qed.

  Lemma encM_nth : forall ds hm i, (i < length ds)%nat -> length hm = length ds ->
    nth i (encM ds hm) [] = map (fun c => @eval Fq2 fzero fadd fmul (nth i hm []) (@nF Fq2 fzero fone fadd c)) (spoints (nth i ds 0%nat)).
  Proof. intros ds hm i hi hl. unfold encM. rewrite (nth_zipw _ ds hm i 0%nat [] []) by (first [exact hi | symmetry; exact hl]). reflexivity. Qed.

  Lemma msgs_list : forall (ms : list (list xf)) (ds : list nat) (hm : list (list F)),
    length ms = length ds -> length hm = length ds ->
    (forall i, (i < length ds)%nat ->
       map to_F (nth i ms []) = map (fun c => @eval Fq2 fzero fadd fmul (nth i hm []) (@nF Fq2 fzero fone fadd c)) (spoints (nth i ds 0%nat))) ->
    map (map to_F) ms = encM ds hm.
  Proof.
    intros ms ds hm hl1 hl2 h. apply nth_ext with (d := []) (d' := []).
    - rewrite length_map, hl1. unfold encM. rewrite zipw_length by (symmetry; exact hl2). reflexivity.
    - intros i hi. rewrite length_map, hl1 in hi.
      rewrite encM_nth by assumption. rewrite <-h by exact hi.
      rewrite (nth_indep _ [] (map to_F [])) by (rewrite length_map; lia). apply map_nth.
  Qed.

  (* the layer: masked evaluations, G values, sumcheck messages *)
  Theorem layer_refines : forall P T, ptransx P T ->
    map to_F (qevA P ++ qevC P) = fst (VL T)
    /\ map to_F (qG P) = [fst (fst (snd (VL T))); fst (fst (snd (snd (VL T)))); fst (snd (snd (snd (VL T))))]
    /\ map (map to_F) (qmA P) = encM (dA ell) (snd (fst (snd (VL T))))
    /\ map (map to_F) (qmB P) = encM (ExecProve.dB n1) (snd (fst (snd (snd (VL T)))))
    /\ map (map to_F) (qmC P) = encM (dC n1 ell) (snd (snd (snd (snd (VL T))))).
  Proof.
    intros P T hT.
    pose proof (evals_run n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 kc sigma
                  Hs Hw cok_kc Hval P T hT) as hev.
    pose proof (G_run n1 ell a b cin kc Hs) as hG.
    pose proof (fun i => msgsA n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 kc Hs Hw P T hT i) as hA.
    pose proof (fun i => msgsB n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 kc Hs Hw P T hT i) as hB.
    pose proof (fun i => msgsC n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 kc Hs Hw P T hT i) as hC.
    pose proof hT as (eP & _ & _ & _ & _ & (c0A & c1A & eA) & (c0B & fB0 & c1B & eB) & (c0C & c1C & eC) & _).
    pose proof (sc_loop_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eA) as [_ lA].
    pose proof (sc_loop_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eB) as [_ lB].
    pose proof (sc_loop_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eC) as [_ lC].
    (* the mask of the coins *)
    assert (gA_e : ExecProve.gA ell kc = (of_F aA, map (map of_F) csA))
      by exact (gA_km ell k0 avs aA aB aC csA csB csC Havs HcA).
    assert (gB_e : ExecProve.gB n1 ell kc = (of_F aB, map (map of_F) csB))
      by exact (gB_km n1 ell k0 avs aA aB aC csA csB csC Havs HcA HcB).
    assert (gC_e : ExecProve.gC n1 ell kc = (of_F aC, map (map of_F) csC))
      by exact (gC_km n1 ell k0 avs aA aB aC csA csB csC Havs HcA HcB HcC).
    rewrite km_kc in hev, hA, hB, hC.
    rewrite gA_e in hA, hG. rewrite gB_e in hB, hG. rewrite gC_e in hC, hG.
    cbn [fst snd] in hA, hB, hC, hG. rewrite !to_F_of_F, !csF_of_F in hA, hB, hC, hG.
    destruct (pf_app avs restF Havs (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)
                (ttc T) (tkA T) (trA T) (ttz T) (tkC T)) as (pA & pB' & pC).
    rewrite pA in hA. rewrite pB' in hB. rewrite pC in hC.
    rewrite eP. cbn [qevA qevC qG qmA qmB qmC parts_of].
    unfold honLx, honL, honT. cbn [fst snd].
    split; [| split; [| split; [| split]]].
    - rewrite hev. apply evs_app. rewrite Havs. reflexivity.
    - rewrite hG, !csF_of_F, !to_F_of_F. reflexivity.
    - apply msgs_list.
      + exact lA.
      + unfold ZkSumcheck.hmsgs. rewrite length_map, length_seq. symmetry. apply ExecBackD.dA_len.
      + intros i hi. rewrite ExecBackD.dA_len in hi. rewrite hmsgs_nth by exact hi. apply hA, hi.
    - apply msgs_list.
      + exact lB.
      + unfold ZkSumcheck.hmsgs. rewrite length_map, length_seq. symmetry. apply ExecBackD.dB_len.
      + intros i hi. rewrite ExecBackD.dB_len in hi. rewrite hmsgs_nth by exact hi. apply hB, hi.
    - apply msgs_list.
      + exact lC.
      + unfold ZkSumcheck.hmsgs. rewrite length_map, length_seq. symmetry. apply ExecBackD.dC_len.
      + intros i hi. rewrite ExecBackD.dC_len in hi. rewrite hmsgs_nth by exact hi. apply hC, hi.
  Qed.

  Local Notation xO := (pB, pS, ((mB, qB), (mS, qS))).
  Local Notation omBK := (zq_of omB).
  Local Notation omSK := (zq_of omS).
  Local Notation JBn := (fun T => map Z.to_nat (tJB T)).
  Local Notation JSn := (fun T => map Z.to_nat (tJS T)).
  Local Notation Xe := (fun P T i j => to_F (fXe (fT n1 ell lo1 lo2 P T) i j)).

  (* the opening: mu, slot vectors, proximity vectors, opened columns *)
  Theorem open_refines : forall P T, ptransx P T ->
    match honMix n1 ell lo1 lo2 omB omS pplain a b cin cout sig wr we1 we2 kx T xO with
    | (mu, ((vB, pvB0), (vS, pvS0)), (ysB, ysS), ((eB, eqB), (eS, eqS))) =>
        to_F (qmu P) = mu
        /\ [map to_F (qv1 P); map to_F (qv2 P)] = vB /\ [map to_F (qv3 P); map to_F (qv4 P)] = vS
        /\ map to_F (qpvB P) = pvB0 /\ map to_F (qpvS P) = pvS0
        /\ (forall i, (i < 3 * rw)%nat -> map (Xe P T i) (JBn T) = map emb (nth i ysB []))
        /\ (forall j', (j' < 6)%nat -> map (Xe P T (3 * rw + j')) (JBn T)
              = nth j' [map re (nth 0 eB []); map im (nth 0 eB []); map re (nth 1 eB []); map im (nth 1 eB []);
                        map re eqB; map im eqB] [])
        /\ (forall j0, (j0 < rs + (4 * rs + 1))%nat -> map (Xe P T (sx n1 ell lo1 lo2 j0)) (JSn T) = map emb (nth j0 ysS []))
        /\ (forall j', (j' < 6)%nat -> map (Xe P T (SO + rs + j')) (JSn T)
              = nth j' [map re (nth 0 eS []); map im (nth 0 eS []); map re (nth 1 eS []); map im (nth 1 eS []);
                        map re eqS; map im eqS] [])
    end.
  Proof.
    intros P T hT.
    destruct (T_shape P T hT) as (Hu & Hv & HrA & Hry & Hrz & Hkp & HgB & HgS & HJBlt & HJSlt).
    pose proof hT as (eP & _).
    assert (eP' : P = parts_of n1 ell lo1 lo2 pplain a b sig kc (btB lo1 nB omB wr we1 we2 kc) (btS1 lo2 nS omS sig kc)
                        (b2x ell lo2 nS omS pplain a b cin cout sig wr we1 we2 kc T) T) by (rewrite eP; reflexivity).
    pose proof cok_kx as hkx.
    pose proof (vecs_run n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hs Hu Hv HrA Hry Hrz Hkp pB pS mB qB mS qS Hsh) as hvec.
    pose proof (mu_run n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp pB pS mB qB mS qS Hsh) as hmu.
    pose proof (pvB_run n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp HgB pB pS mB qB mS qS Hsh) as hpB.
    pose proof (pvS_run n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp HgB HgS pB pS mB qB mS qS Hsh) as hpS.
    pose proof (colsB_data n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp HgB HgS HJBlt pB pS mB qB mS qS Hsh) as hcBd.
    pose proof (colsB_mask n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp HgB HgS HJBlt pB pS mB qB mS qS Hsh) as hcBm.
    pose proof (colsS_data n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp HgB HgS HJSlt pB pS mB qB mS qS Hsh) as hcSd.
    pose proof (colsS_mask n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kx T
                  Hp Hw hkx Hu Hv HrA Hry Hrz Hkp HgB HgS HJSlt pB pS mB qB mS qS Hsh) as hcSm.
    pose proof Hsh as (h1 & _ & h3 & _ & h5 & _ & _ & h8 & _).
    rewrite eP'. clear eP eP'.
    unfold honMix, ZkJoin.honO3. cbv beta iota.
    destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
    destruct mS as [| m3 [| m4 [| ? ?]]]; cbn in h8; try lia.
    unfold tfunB, tfunS in hvec. cbn [map zipw app] in hvec.
    injection hvec as e1 e2 e3 e4.
    cbn [qmu qv1 qv2 qv3 qv4 qpvB qpvS parts_of].
    split; [exact hmu |]. split; [unfold tfunB; cbn [zipw]; rewrite e1, e2; reflexivity |].
    split; [unfold tfunS; cbn [zipw]; rewrite e3, e4; reflexivity |].
    split; [exact hpB |]. split; [exact hpS |].
    split; [| split; [| split]].
    - intros i hi. rewrite (hcBd i hi).
      rewrite (nth_zipw _ (datasB n1 ell lo1 wr we1 we2) pB i [] [] []); [reflexivity | |].
      + unfold datasB. rewrite length_map, length_seq. exact hi.
      + unfold datasB. rewrite length_map, length_seq. symmetry. exact h1.
    - intros j' hj'. rewrite (hcBm j' hj'). reflexivity.
    - intros j0 hj0. rewrite (hcSd j0 hj0).
      rewrite (nth_zipw _ (datasS ell lo2 pplain a b cin cout sig wr we1 we2 kx T) pS j0 [] [] []); [reflexivity | |].
      + unfold datasS. rewrite length_map, length_seq. exact hj0.
      + unfold datasS. rewrite length_map, length_seq. symmetry. exact h3.
    - intros j' hj'. rewrite (hcSm j' hj'). reflexivity.
  Qed.

  (* a whole run: every field element of the proof is the model's honest transcript at the run's challenges *)
  Theorem xmix_prove_refines : forall P T, ptransx P T ->
    (map to_F (qevA P ++ qevC P) = fst (VL T)
     /\ map to_F (qG P) = [fst (fst (snd (VL T))); fst (fst (snd (snd (VL T)))); fst (snd (snd (snd (VL T))))]
     /\ map (map to_F) (qmA P) = encM (dA ell) (snd (fst (snd (VL T))))
     /\ map (map to_F) (qmB P) = encM (ExecProve.dB n1) (snd (fst (snd (snd (VL T)))))
     /\ map (map to_F) (qmC P) = encM (dC n1 ell) (snd (snd (snd (snd (VL T))))))
    /\ match honMix n1 ell lo1 lo2 omB omS pplain a b cin cout sig wr we1 we2 kx T xO with
       | (mu, ((vB, pvB0), (vS, pvS0)), (ysB, ysS), ((eB, eqB), (eS, eqS))) =>
           to_F (qmu P) = mu
           /\ [map to_F (qv1 P); map to_F (qv2 P)] = vB /\ [map to_F (qv3 P); map to_F (qv4 P)] = vS
           /\ map to_F (qpvB P) = pvB0 /\ map to_F (qpvS P) = pvS0
           /\ (forall i, (i < 3 * rw)%nat -> map (Xe P T i) (JBn T) = map emb (nth i ysB []))
           /\ (forall j', (j' < 6)%nat -> map (Xe P T (3 * rw + j')) (JBn T)
                 = nth j' [map re (nth 0 eB []); map im (nth 0 eB []); map re (nth 1 eB []); map im (nth 1 eB []);
                           map re eqB; map im eqB] [])
           /\ (forall j0, (j0 < rs + (4 * rs + 1))%nat -> map (Xe P T (sx n1 ell lo1 lo2 j0)) (JSn T) = map emb (nth j0 ysS []))
           /\ (forall j', (j' < 6)%nat -> map (Xe P T (SO + rs + j')) (JSn T)
                 = nth j' [map re (nth 0 eS []); map im (nth 0 eS []); map re (nth 1 eS []); map im (nth 1 eS []);
                           map re eqS; map im eqS] [])
       end.
  Proof. intros P T hT. split; [exact (layer_refines P T hT) | exact (open_refines P T hT)]. Qed.

End Main.
