(* Completeness, back end, step 3: the verifier's sumcheck layer (xderive)
   accepts the record built from the prover's output, and the nine values it
   derives are, as field elements, the prover's masked evaluations:

     derive_complete   lengths_ok and derivedE = Some vals with
                       map to_F vals = targets T (below).

   Each sumcheck run of the prover starts from its true sum (sumA, sumB, sumC
   of ExecBack.v), so sc_loop_complete (ExecFold.v) applies: the verifier's
   round checks pass and the final values are the masked evaluations of the
   prover's tables. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field String.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex Sumcheck SumcheckMask LayoutLemmas RowLayout MixBridge Opening SlotKinds MaskedExt MixSummands MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecMerkle ExecProveBase ExecSerial ExecFold ExecFront ExecShape ExecDec ExecProve ExecRows ExecBack.
Import ListNotations.

Add Field fieldF2d2 : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation fsum := (@LogDer.fsum Fq2 fzero fadd).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation gmask2 := (@gmask Fq2 fzero fadd fmul).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).

(* ---------------------------------------------------------------------- *)
(* generic *)

Lemma cuts_shape : forall {A : Type} ds (l : list A),
  List.length (fst (cuts ds l)) = List.length ds
  /\ forall i, (i < List.length ds)%nat -> (List.length (nth i (fst (cuts ds l)) []) <= nth i ds 0%nat)%nat.
Proof.
  intros A ds; induction ds as [| d ds ih]; intro l; [split; [reflexivity | intros i hi; cbn in hi; lia] |].
  cbn [cuts cut]. destruct (cuts ds (skipn d l)) as [xs s2] eqn:e. cbn [fst].
  destruct (ih (skipn d l)) as [h1 h2]. rewrite e in h1, h2. cbn [fst] in h1, h2.
  split; [cbn; rewrite h1; reflexivity |].
  intros i hi. destruct i as [| i]; cbn [nth]; [rewrite length_firstn; lia |]. apply h2. cbn in hi. lia.
Qed.

Lemma mle_eqp : forall M (t x : list F), List.length t = M -> List.length x = M ->
  mle2 M (fun bq => eqp2 bq t) x = eqp2 x t.
Proof.
  induction M as [| M ih]; intros t x ht hx.
  + destruct t, x; try discriminate. rewrite (@mle_0 Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). reflexivity.
  + destruct t as [| t0 t]; [discriminate |]. destruct x as [| x0 x]; [discriminate |].
    cbn in ht, hx. rewrite (@mle_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub M _
               (fun bq => fmul (fsub fone t0) (eqp2 bq t))) by (intros bq _; cbn [Mle.eqp]; field).
    rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub M (fun bq => eqp2 (fone :: bq) (t0 :: t))
               (fun bq => fmul t0 (eqp2 bq t))) by (intros bq _; cbn [Mle.eqp]; field).
    rewrite !(@mle_scale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), ih by lia.
    cbn [Mle.eqp]. field.
Qed.

(* the multilinear extension of the eq table of t, at x *)
Lemma xmle_eq : forall t x, List.length x = List.length t -> to_F (xmle (xeq_table t) x) = to_F (xeq_eval x t).
Proof.
  intros t x hl. rewrite <-(mle_list (List.length t) (fun bq => eqp2 bq (map to_F t))).
  + rewrite mle_eqp by (rewrite length_map; lia). rewrite to_F_eq_eval. reflexivity.
  + apply xeq_table_length.
  + exact hl.
  + intros i hi. rewrite to_F_nth, to_F_eq_table. unfold RowLayout.eqvec. rewrite nth_map_seq_F by exact hi.
    reflexivity.
Qed.

Lemma comb_rows_length : forall (l : list (xf * list Z)) n, l <> [] -> Forall (fun p => List.length (snd p) = n) l ->
  List.length (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) l)) = n.
Proof.
  induction l as [| p l ih]; intros n hne h; [contradiction |].
  apply Forall_cons_iff in h. destruct h as [hp hl].
  destruct l as [| p2 l].
  + cbn [map fold_right]. rewrite xpadd_length. unfold xpscale. rewrite !length_map, hp. cbn. lia.
  + assert (e := ih n ltac:(discriminate) hl). cbn [map fold_right] in e |- *. rewrite xpadd_length.
    unfold xpscale at 1. rewrite !length_map, hp, e. lia.
Qed.

Section BackD.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
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

  Local Notation hPx := (hP ell pplain a b cin wr we1 we2).
  Local Notation hhPx := (hhP cout sig).
  Local Notation uPx := (uP ell pplain a b cin wr we1 we2).
  Local Notation uhPx := (uhP cout sig).
  Local Notation tablesAx := (tablesA ell pplain a b cin cout sig wr we1 we2).
  Local Notation tablesBx := (tablesB n1 pplain a b wr we1 we2 k).
  Local Notation validx := (valid n1 ell pplain a b cin cout sig wr we1 we2 sigma).
  Local Notation stmtx := (stmt_ok n1 ell a b cin).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).
  Local Notation cok := (coins_ok n1 ell lo1 lo2 nB nqB nS nqS k).
  Local Notation ptransx := (ptrans n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k get_F get_I).
  Local Notation gAx := (gA ell k).
  Local Notation gBx := (ExecProve.gB n1 ell k).
  Local Notation gCx := (gC n1 ell k).

  (* the lengths of the drawn challenges *)
  Lemma drawn_F : forall nm n x, (exists c c', get_F c (sb nm) n = Some (x, c')) -> List.length x = n.
  Proof. intros nm n x (c & c' & h). exact (proj1 (get_F_shape _ _ _ _ _ h)). Qed.

  Lemma mask_lengths : cok -> forall off ds, (off + 1 + list_sum ds <= n_mask n1 ell)%nat ->
    List.length (snd (mask_of ds (skipn off (kmask k)))) = List.length ds
    /\ forall i, (i < List.length ds)%nat -> (List.length (nth i (snd (mask_of ds (skipn off (kmask k)))) []) <= nth i ds 0%nat)%nat.
  Proof. intros _ off ds _. unfold mask_of. cbn [snd]. apply cuts_shape. Qed.

  Lemma dA_nth : forall i, (i < ell)%nat -> nth i (dA ell) 0%nat = if Nat.eqb (S i) ell then 5%nat else 3%nat.
  Proof.
    intros i hi. unfold dA, dAE. rewrite (nth_indep _ 0%nat (if Nat.eqb 1 ell then 5%nat else 3%nat))
      by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth (fun i => if Nat.eqb (S i) ell then 5%nat else 3%nat)), seq_nth by exact hi. reflexivity.
  Qed.

  Lemma dC_nth : forall i, (i < m)%nat -> nth i (dC n1 ell) 0%nat = if Nat.eqb (S i) m then 7%nat else 4%nat.
  Proof.
    intros i hi. unfold dC, dCE. rewrite (nth_indep _ 0%nat (if Nat.eqb 1 m then 7%nat else 4%nat))
      by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth (fun i => if Nat.eqb (S i) m then 7%nat else 4%nat)), seq_nth by exact hi. reflexivity.
  Qed.

  Lemma dB_nth : forall i, (i < n1)%nat -> nth i (dB n1) 0%nat = 2%nat.
  Proof.
    intros i hi. unfold dB, dBE. exact (nth_map_seq_any (fun _ => 2%nat) n1 i 0%nat hi).
  Qed.

  Lemma dA_len : List.length (dA ell) = ell. Proof. unfold dA, dAE. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma dB_len : List.length (dB n1) = n1. Proof. unfold dB, dBE. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma dC_len : List.length (dC n1 ell) = m. Proof. unfold dC, dCE. rewrite length_map, length_seq. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* sumcheck A *)

  Theorem scA : stmtx -> wshape -> cok -> validx -> forall P T, ptransx P T ->
    exists clA,
      xsc_verify (tmA T) (trA T) (claimA (tkA T ++ trhoA T) (nth 0 (GP n1 ell k) xzero)) = Some clA
      /\ to_F clA = fadd (termsF (map sF (termsA (tkA T))) (map to_F (tfinA T)))
                         (fmul (to_F (nth 0 (trhoA T) xzero)) (gmask2 (to_F (fst gAx)) (csF (snd gAx)) (map to_F (trA T))))
      /\ List.length (trA T) = ell /\ Forall2 msg_ok (tmA T) (dA ell)
      /\ (forall j, (j < 5)%nat ->
            to_F (nth j (tfinA T) xzero)
            = fadd (to_F (xmle (nth j (tablesAx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T) (ttc T)) []) (trA T)))
                   (fmul (maskv (tmaskA k (ExecProve.beT T)) j) (Zp2 (map to_F (trA T))))).
  Proof.
    intros hs hw hk hv P T hT.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    destruct hT as (_ & hdr & hnz & _ & _ & (c0 & c1 & eA) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & dab & dtc & dkA & drhoA & _).
    apply drawn_F in dru, drv, dab, dtc, dkA, drhoA.
    set (al := ExecProve.alT T) in *. set (be := ExecProve.beT T) in *.
    assert (hlen : List.length (snd gAx) = ell /\
                   forall i, (i < ell)%nat -> (List.length (nth i (snd gAx) []) <= nth i (dA ell) 0%nat)%nat).
    { unfold gA. cbn [snd]. destruct (cuts_shape (dA ell) (tl (skipn 7 (kmask k)))) as [h1 h2].
      rewrite dA_len in h1, h2. split; [exact h1 | exact h2]. }
    destruct hlen as [hcsl hcsd].
    assert (hclaim : to_F (claimA (tkA T ++ trhoA T) (nth 0 (GP n1 ell k) xzero))
                     = fadd (csum (map sF (termsA (tkA T))) (tF (tablesAx (tru T) (trv T) al be (ttc T))) (2 ^ List.length (dA ell)))
                            (fmul (to_F (nth 0 (trhoA T) xzero)) (@tsum Fq2 fzero fone fadd (gmask2 (to_F (fst gAx)) (csF (snd gAx))) (map to_F []) (List.length (dA ell))))).
    { rewrite dA_len.
      rewrite (sumA n1 ell pplain a b cin cout sig wr we1 we2 sigma (tru T) (trv T) al be (ttc T) (tkA T) hv hw hci dru drv dtc hnz).
      unfold claimA, xkk. rewrite !app_nth1 by lia. rewrite app_nth2 by lia. rewrite dkA. cbn [Nat.sub].
      unfold GP. cbn [nth]. rewrite !to_F_add, to_F_mul, to_F_mtotal.
      + rewrite hcsl. reflexivity.
      + intro e. rewrite e in hcsl. cbn in hcsl. lia. }
    destruct (sc_loop_complete (fun c nm => get_F c nm 1) "A"%string (tmaskA k be) (termsA (tkA T)) (fst gAx) (snd gAx)
                (nth 0 (trhoA T) xzero) (dA ell) 0 (tablesAx (tru T) (trv T) al be (ttc T)) [] c0 (tmA T) (trA T) (tfinA T) c1
                (claimA (tkA T ++ trhoA T) (nth 0 (GP n1 ell k) xzero))) as ((clA & hv1 & hv2) & _ & _ & hpt & hmsg & hfin).
    - intro e. pose proof (f_equal (@List.length nat) e) as e'. rewrite dA_len in e'. cbn in e'. lia.
    - discriminate.
    - rewrite hcsl, dA_len. reflexivity.
    - intros i hi. rewrite dA_len in hi |- *. cbn [Nat.add]. unfold round_ok. rewrite dA_nth by exact hi.
      split; [destruct (Nat.eqb (S i) ell); unfold DMAX; lia |].
      split; [rewrite <-dA_nth by exact hi; apply hcsd; exact hi |].
      intros t ht. unfold termsA in ht. unfold mdeg, tmaskA.
      destruct (Nat.eqb (S i) ell); cbn in ht;
        destruct ht as [<- | [<- | [<- | [<- | []]]]]; cbn; lia.
    - reflexivity.
    - rewrite dA_len. unfold tablesA, uP, uhP. repeat constructor.
      + rewrite xeq_table_length, dtc. reflexivity.
      + rewrite length_map. apply hP_length.
      + apply hP_length.
      + rewrite length_map. apply (hhP_length n1 ell cout sig wr we1 we2 _ _ al be hw).
      + apply (hhP_length n1 ell cout sig wr we1 we2 _ _ al be hw).
    - reflexivity.
    - exact hclaim.
    - exact eA.
    - exists clA. rewrite skipn_O in hv1. split; [exact hv1 |]. split; [exact hv2 |].
      rewrite dA_len in hpt. split; [exact hpt |]. split; [exact hmsg |].
      intros j hj. rewrite (hfin j) by (cbn; lia). rewrite skipn_O. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* sumcheck B *)

  Lemma WpP_length : wshape -> forall rA w, In w [wr; we1; we2] -> List.length rA = ell ->
    List.length (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p)))
                                         (combine (xeq_table rA) (map (map zm) w)))) = N.
  Proof.
    intros hw rA w hin hrA. apply comb_rows_length.
    + destruct hw as (_ & _ & hw'). rewrite Forall_forall in hw'. destruct (hw' w hin) as [h1 _].
      intro e. pose proof (f_equal (@List.length (xf * list Z)) e) as e'. rewrite length_combine, xeq_table_length, length_map, h1, hrA in e'.
      cbn in e'. pose proof (Nat.pow_nonzero 2 ell ltac:(lia)). lia.
    + apply Forall_forall. intros [p1 p2] hp. apply in_combine_r in hp. apply in_map_iff in hp. destruct hp as (q & <- & hq).
      cbn [snd].
      rewrite length_map. destruct hw as (_ & _ & hw'). rewrite Forall_forall in hw'. destruct (hw' w hin) as [_ h2].
      rewrite Forall_forall in h2. apply h2, hq.
  Qed.

  Theorem scB : stmtx -> wshape -> cok -> validx -> forall P T, ptransx P T ->
    List.length (trA T) = ell ->
    to_F (nth 2 (tfinA T) xzero)
      = fadd (to_F (xmle (hPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) (trA T)))
             (fmul (to_F (a_h k)) (Zp2 (map to_F (trA T)))) ->
    exists clB finB,
      xsc_verify (tmB T) (try T)
        (claimB (cinX cin) (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T) (trA T) (nth 0 (trhoB T) xzero)
                (nth 1 (GP n1 ell k) xzero) (nth 2 (tfinA T) xzero)) = Some clB
      /\ to_F clB = fadd (termsF (map sF termsB) (map to_F finB))
                         (fmul (to_F (nth 0 (trhoB T) xzero)) (gmask2 (to_F (fst gBx)) (csF (snd gBx)) (map to_F (try T))))
      /\ List.length (try T) = n1 /\ Forall2 msg_ok (tmB T) (dB n1)
      /\ (forall j, (j < 7)%nat ->
            to_F (nth j finB xzero) = to_F (xmle (nth j (tablesBx (tru T) (trv T) (trA T)) []) (try T))).
  Proof.
    intros hs hw hk hv P T hT hrA hHd.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    destruct hT as (_ & hdr & hnz & _ & _ & _ & (c0 & finB & c1 & eB) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & dab & _ & _ & _ & drhoB & _).
    apply drawn_F in dru, drv, dab, drhoB.
    set (al := ExecProve.alT T) in *. set (be := ExecProve.beT T) in *.
    assert (hlen : List.length (snd gBx) = n1 /\
                   forall i, (i < n1)%nat -> (List.length (nth i (snd gBx) []) <= nth i (dB n1) 0%nat)%nat).
    { unfold ExecProve.gB. cbn [snd]. destruct (cuts_shape (dB n1) (tl (skipn (8 + list_sum (dA ell)) (kmask k)))) as [h1 h2].
      rewrite dB_len in h1, h2. split; [exact h1 | exact h2]. }
    destruct hlen as [hcsl hcsd].
    assert (hclaim : to_F (claimB (cinX cin) (tru T) (trv T) al be (trA T) (nth 0 (trhoB T) xzero)
                                  (nth 1 (GP n1 ell k) xzero) (nth 2 (tfinA T) xzero))
                     = fadd (csum (map sF termsB) (tF (tablesBx (tru T) (trv T) (trA T))) (2 ^ List.length (dB n1)))
                            (fmul (to_F (nth 0 (trhoB T) xzero)) (@tsum Fq2 fzero fone fadd (gmask2 (to_F (fst gBx)) (csF (snd gBx))) (map to_F []) (List.length (dB n1))))).
    { rewrite dB_len.
      rewrite (sumB n1 ell pplain a b cin cout sig wr we1 we2 k (tru T) (trv T) al be (trA T) hw hs dru drv hrA).
      unfold claimB. rewrite !to_F_add, !to_F_sub, !to_F_mul, to_F_idr, hHd, to_F_zval.
      unfold GP. cbn [nth]. rewrite to_F_mtotal.
      + rewrite hcsl. reflexivity.
      + intro e. rewrite e in hcsl. cbn in hcsl. lia. }
    destruct (sc_loop_complete (fun c nm => get_F c nm 1) "B"%string (repeat None 7) termsB (fst gBx) (snd gBx)
                (nth 0 (trhoB T) xzero) (dB n1) 0 (tablesBx (tru T) (trv T) (trA T)) [] c0 (tmB T) (try T) finB c1
                (claimB (cinX cin) (tru T) (trv T) al be (trA T) (nth 0 (trhoB T) xzero)
                        (nth 1 (GP n1 ell k) xzero) (nth 2 (tfinA T) xzero))) as ((clB & hv1 & hv2) & _ & _ & hpt & hmsg & hfin).
    - intro e. pose proof (f_equal (@List.length nat) e) as e'. rewrite dB_len in e'. cbn in e'. lia.
    - unfold tablesB, rpP. discriminate.
    - rewrite hcsl, dB_len. reflexivity.
    - intros i hi. rewrite dB_len in hi |- *. cbn [Nat.add]. unfold round_ok. rewrite dB_nth by exact hi.
      split; [unfold DMAX; lia |].
      split; [rewrite <-(dB_nth i hi); apply hcsd; exact hi |].
      intros t ht. unfold termsB in ht. unfold mdeg.
      destruct (Nat.eqb (S i) n1); cbn in ht;
        destruct ht as [<- | [<- | [<- | [<- | []]]]]; cbn; lia.
    - reflexivity.
    - rewrite dB_len. pose proof (rpP_lengths n1 pplain a b (tru T) (trv T) ha hb hn1 dru drv) as hrp.
      unfold tablesB, WpP, Wpol. cbn [map]. apply Forall_app. split; [exact hrp |].
      repeat constructor.
      + apply WpP_length; [exact hw | cbn; tauto | exact hrA].
      + apply WpP_length; [exact hw | cbn; tauto | exact hrA].
      + apply WpP_length; [exact hw | cbn; tauto | exact hrA].
      + apply repeat_length.
    - reflexivity.
    - exact hclaim.
    - exact eB.
    - exists clB, finB. rewrite skipn_O in hv1. split; [exact hv1 |]. split; [exact hv2 |].
      rewrite dB_len in hpt. split; [exact hpt |]. split; [exact hmsg |].
      intros j hj. rewrite (hfin j) by (unfold tablesB; cbn; lia). rewrite skipn_O.
      unfold maskv. replace (nth j (repeat (@None xf) 7) None) with (@None xf)
        by (symmetry; apply nth_repeat). field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* sumcheck C *)

  Theorem scC : stmtx -> wshape -> cok -> validx -> forall P T, ptransx P T ->
    exists clC,
      xsc_verify (tmC T) (trz T) (claimC (tkC T ++ trhoC T) (nth 2 (GP n1 ell k) xzero)) = Some clC
      /\ to_F clC = fadd (termsF (map sF (termsC (tkC T))) (map to_F (tfinC T)))
                         (fmul (to_F (nth 0 (trhoC T) xzero)) (gmask2 (to_F (fst gCx)) (csF (snd gCx)) (map to_F (trz T))))
      /\ List.length (trz T) = m /\ Forall2 msg_ok (tmC T) (dC n1 ell)
      /\ (forall j, (j < 4)%nat ->
            to_F (nth j (tfinC T) xzero)
            = fadd (to_F (xmle (nth j (tablesC wr we1 we2 (ttz T)) []) (trz T)))
                   (fmul (maskv (tmaskC k) j) (Zp2 (map to_F (trz T))))).
  Proof.
    intros hs hw hk hv P T hT.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    destruct hT as (_ & hdr & _ & _ & _ & _ & _ & (c0 & c1 & eC) & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (_ & _ & _ & _ & _ & _ & _ & dtz & dkC & drhoC & _).
    apply drawn_F in dtz, dkC, drhoC.
    assert (hlen : List.length (snd gCx) = m /\
                   forall i, (i < m)%nat -> (List.length (nth i (snd gCx) []) <= nth i (dC n1 ell) 0%nat)%nat).
    { unfold gC. cbn [snd]. destruct (cuts_shape (dC n1 ell) (tl (skipn (9 + list_sum (dA ell) + list_sum (dB n1)) (kmask k)))) as [h1 h2].
      rewrite dC_len in h1, h2. split; [exact h1 | exact h2]. }
    destruct hlen as [hcsl hcsd].
    assert (hclaim : to_F (claimC (tkC T ++ trhoC T) (nth 2 (GP n1 ell k) xzero))
                     = fadd (csum (map sF (termsC (tkC T))) (tF (tablesC wr we1 we2 (ttz T))) (2 ^ List.length (dC n1 ell)))
                            (fmul (to_F (nth 0 (trhoC T) xzero)) (@tsum Fq2 fzero fone fadd (gmask2 (to_F (fst gCx)) (csF (snd gCx))) (map to_F []) (List.length (dC n1 ell))))).
    { rewrite dC_len.
      rewrite (sumC n1 ell pplain a b cin cout sig wr we1 we2 sigma (ttz T) (tkC T) hv hw).
      unfold claimC, xkk. rewrite app_nth2 by lia. rewrite dkC. cbn [Nat.sub].
      unfold GP. cbn [nth]. rewrite to_F_mul, to_F_mtotal.
      + rewrite hcsl. cbn [map]. field.
      + intro e. rewrite e in hcsl. cbn in hcsl. lia. }
    destruct (sc_loop_complete (fun c nm => get_F c nm 1) "C"%string (tmaskC k) (termsC (tkC T)) (fst gCx) (snd gCx)
                (nth 0 (trhoC T) xzero) (dC n1 ell) 0 (tablesC wr we1 we2 (ttz T)) [] c0 (tmC T) (trz T) (tfinC T) c1
                (claimC (tkC T ++ trhoC T) (nth 2 (GP n1 ell k) xzero))) as ((clC & hv1 & hv2) & _ & _ & hpt & hmsg & hfin).
    - intro e. pose proof (f_equal (@List.length nat) e) as e'. rewrite dC_len in e'. cbn in e'. lia.
    - discriminate.
    - rewrite hcsl, dC_len. reflexivity.
    - intros i hi. rewrite dC_len in hi |- *. cbn [Nat.add]. unfold round_ok. rewrite dC_nth by exact hi.
      split; [destruct (Nat.eqb (S i) m); unfold DMAX; lia |].
      split; [rewrite <-dC_nth by exact hi; apply hcsd; exact hi |].
      intros t ht. unfold termsC in ht. unfold mdeg, tmaskC, a_w.
      destruct (Nat.eqb (S i) m); cbn in ht;
        destruct ht as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn; lia.
    - reflexivity.
    - rewrite dC_len. unfold tablesC, Wk, Wpol. cbn [map]. repeat constructor.
      + rewrite xeq_table_length, dtz. reflexivity.
      + rewrite length_map. apply (Wk_length n1 ell cout sig wr we1 we2 hw). cbn; tauto.
      + rewrite length_map. apply (Wk_length n1 ell cout sig wr we1 we2 hw). cbn; tauto.
      + rewrite length_map. apply (Wk_length n1 ell cout sig wr we1 we2 hw). cbn; tauto.
    - reflexivity.
    - exact hclaim.
    - exact eC.
    - exists clC. rewrite skipn_O in hv1. split; [exact hv1 |]. split; [exact hv2 |].
      rewrite dC_len in hpt. split; [exact hpt |]. split; [exact hmsg |].
      intros j hj. rewrite (hfin j) by (cbn; lia). rewrite skipn_O. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the hidden values: hhat at r *)

  Lemma hhP_entry : wshape -> forall ru rv al be j, (j < tau)%nat ->
    to_F (nth j (hhPx ru rv al be) xzero)
    = fsub (fadd (to_F (nth j (zhatP cout ru rv) xzero)) (fmul (to_F be) (to_F (nth j (map bx (sigZ sig)) xzero)))) (to_F al).
  Proof.
    intros (hs & hc & _) ru rv al be j hj. unfold hhP.
    rewrite (nth_combine_map _ _ _ j xzero 0%Z xzero) by (unfold zhatP, sigZ, cinX; rewrite ?length_map; lia).
    cbn [fst snd]. rewrite to_F_sub, to_F_add, to_F_mul. f_equal. f_equal. f_equal. f_equal.
    change xzero with (bx 0%Z). rewrite map_nth. reflexivity.
  Qed.

  Lemma xmle_hh : wshape -> forall ru rv al be rA, List.length rA = ell ->
    to_F (xmle (hhPx ru rv al be) rA)
    = fsub (fadd (to_F (xmle (zhatP cout ru rv) rA)) (fmul (to_F be) (to_F (xmle (map bx (sigZ sig)) rA)))) (to_F al).
  Proof.
    intros hw ru rv al be rA hrA. pose proof hw as (hs & hc & _).
    rewrite (xmle_sum (hhPx ru rv al be) rA) by (rewrite (hhP_length n1 ell cout sig wr we1 we2 ru rv al be hw), hrA; reflexivity).
    rewrite (xmle_sum (zhatP cout ru rv) rA) by (unfold zhatP, cinX; rewrite !length_map, hrA; exact hc).
    rewrite (xmle_sum (map bx (sigZ sig)) rA) by (unfold sigZ; rewrite !length_map, hrA; exact hs).
    rewrite hrA.
    rewrite (fsum_seq_ext _ (fun j => fsub (fadd (fmul (nth j (map to_F (xeq_table rA)) fzero) (to_F (nth j (zhatP cout ru rv) xzero)))
                                               (fmul (to_F be) (fmul (nth j (map to_F (xeq_table rA)) fzero) (to_F (nth j (map bx (sigZ sig)) xzero)))))
                                         (fmul (nth j (map to_F (xeq_table rA)) fzero) (to_F al))))
      by (intros j hj; rewrite (hhP_entry hw ru rv al be j hj); field).
    rewrite (@LogDer.fsum_map_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite <-ExecFold.fsum_map_add.
    rewrite (@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite fsum_map_mul_r. rewrite <-hrA, eq_table_sum. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* step 3: the verifier's sumcheck layer on the prover's record *)

  Definition fT (P : mparts) (T : ptrace) : front :=
    front_mk n1 ell lo1 lo2 (tru T) (trv T) (tab T) (ttc T) (tkA T) (trhoA T) (trA T) (trhoB T) (try T)
             (ttz T) (tkC T) (trhoC T) (trz T) (tkp T) (tcl T) (tgB T) (tgS T) (tJB T) (tJS T) P.

  (* the nine values, as the prover's masked evaluations *)
  Definition targets (T : ptrace) : list F :=
    let ru := tru T in let rv := trv T in let al := ExecProve.alT T in let be := ExecProve.beT T in
    let rA := trA T in let ry := try T in let rz := trz T in
    let mB j := to_F (xmle (nth j (tablesBx ru rv rA) []) ry) in
    let Wz j := fadd (to_F (xmle (map bx (nth j (Wk wr we1 we2) [])) rz))
                     (fmul (to_F (nth j (a_w k) xzero)) (Zp2 (map to_F rz))) in
    [ fadd (to_F (xmle (uPx ru rv al be) rA)) (fmul (to_F (a_u k)) (Zp2 (map to_F rA)));
      fadd (to_F (xmle (uhPx ru rv al be) rA)) (fmul (to_F (a_uh k)) (Zp2 (map to_F rA)));
      to_F (s_valP sig k rA);
      fadd (fadd (fadd (fadd (fmul (mB 0%nat) (mB 3%nat)) (fmul (mB 1%nat) (mB 4%nat))) (fmul (mB 2%nat) (mB 5%nat))) (mB 6%nat))
           (fmul (to_F (nth 0 (trhoB T) xzero)) (gmask2 (to_F (fst gBx)) (csF (snd gBx)) (map to_F ry)));
      Wz 0%nat; Wz 1%nat; Wz 2%nat;
      gmask2 (to_F (fst gAx)) (csF (snd gAx)) (map to_F rA);
      gmask2 (to_F (fst gCx)) (csF (snd gCx)) (map to_F rz) ].

  Lemma forallb_dmax : forall ms ds, Forall2 msg_ok ms ds -> (forall d, In d ds -> (d <= DMAX)%nat) ->
    forallb (fun ev => Nat.leb (List.length ev) DMAX) ms = true.
  Proof.
    intros ms ds h hd. induction h as [| ev d ms ds [hl _] h ih]; [reflexivity |].
    cbn [forallb]. rewrite ih by (intros d' hd'; apply hd; right; exact hd').
    rewrite hl. apply andb_true_intro. split; [apply Nat.leb_le; apply hd; left; reflexivity | reflexivity].
  Qed.

  Theorem derive_complete : stmtx -> wshape -> cok -> validx -> forall P T, ptransx P T ->
    lengths_ok n1 ell a b (fT P T) = true
    /\ exists vals, derivedE n1 ell cin cout (fT P T) = Some vals /\ map to_F vals = targets T.
  Proof.
    intros hs hw hk hv P T hT.
    destruct (scA hs hw hk hv P T hT) as (clA & eA & vA & lrA & mA & finA).
    destruct (scC hs hw hk hv P T hT) as (clC & eC & vC & lrz & mC & finC).
    assert (hHd : to_F (nth 2 (tfinA T) xzero)
                  = fadd (to_F (xmle (hPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) (trA T)))
                         (fmul (to_F (a_h k)) (Zp2 (map to_F (trA T))))) by (rewrite (finA 2%nat) by lia; reflexivity).
    destruct (scB hs hw hk hv P T hT lrA hHd) as (clB & finB & eB & vB & lry & mB & finBf).
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ). pose proof hw as (hsl & hcl & _).
    destruct hT as (hP & hdr & hnz & hnA & hnC & _).
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & dab & dtc & dkA & drhoA & drhoB & dtz & dkC & drhoC & _).
    apply drawn_F in dru, drv, dab, dtc, dkA, drhoA, drhoB, dtz, dkC, drhoC.
    assert (hNpos : (0 < N)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    subst P. split.
    { unfold lengths_ok, fT, front_mk. cbn [frA fry frz fru frv].
      rewrite lrA, lry, lrz, dru, drv, ha, hb, !Nat.eqb_refl. cbn [andb].
      replace (Nat.ltb 0 N) with true by (symmetry; apply Nat.ltb_lt; exact hNpos). reflexivity. }
    unfold derivedE, xderive, fT, front_mk.
    cbn [fru frv fal fbe ftc fkA frA frhoB fry ftz fkC frz fGA fGB fGC fmA fU fUh fsv fHd fmB fmC fw1 fw2 fw3
         parts_of qG qmA qevA qmB qmC qevC evAT evCT evAP evCP nth].
    match goal with |- context [if ?c then _ else _] => replace c with true end.
    2: { symmetry. unfold shapes_ok, cinX, coutX, xkk. rewrite !length_map, dru, drv, hci, hcl, lrA, !Nat.eqb_refl.
         rewrite (forallb_dmax _ _ mA), (forallb_dmax _ _ mB), (forallb_dmax _ _ mC).
         - rewrite !app_nth2 by lia. rewrite dkA, dkC. cbn [Nat.sub]. rewrite hnA, hnC. reflexivity.
         - intros d hd. unfold dC, dCE in hd. apply in_map_iff in hd. destruct hd as (i & <- & _).
           destruct (Nat.eqb _ _); unfold DMAX; lia.
         - intros d hd. unfold dB, dBE in hd. apply in_map_iff in hd. destruct hd as (i & <- & _). unfold DMAX; lia.
         - intros d hd. unfold dA, dAE in hd. apply in_map_iff in hd. destruct hd as (i & <- & _).
           destruct (Nat.eqb _ _); unfold DMAX; lia. }
    unfold ExecProve.alT, ExecProve.beT in eB.
    rewrite eA, eB, eC.
    eexists. split; [reflexivity |].
    assert (e1 : to_F (nth 1 (tfinA T) xzero) = fadd (to_F (xmle (uPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) (trA T))) (fmul (to_F (a_u k)) (Zp2 (map to_F (trA T)))))
      by (rewrite (finA 1%nat) by lia; reflexivity).
    assert (e2 : to_F (nth 3 (tfinA T) xzero) = fadd (to_F (xmle (uhPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) (trA T))) (fmul (to_F (a_uh k)) (Zp2 (map to_F (trA T)))))
      by (rewrite (finA 3%nat) by lia; reflexivity).
    assert (ew : forall j, (j < 3)%nat -> to_F (nth (S j) (tfinC T) xzero)
                 = fadd (to_F (xmle (map bx (nth j (Wk wr we1 we2) [])) (trz T))) (fmul (to_F (nth j (a_w k) xzero)) (Zp2 (map to_F (trz T))))).
    { intros j hj. rewrite (finC (S j)) by lia. destruct j as [| [| [| j]]]; try lia; reflexivity. }
    set (mB' := fun j => to_F (xmle (nth j (tablesBx (tru T) (trv T) (trA T)) []) (try T))).
    assert (e4 : to_F clB = fadd (fadd (fadd (fadd (fmul (mB' 0%nat) (mB' 3%nat)) (fmul (mB' 1%nat) (mB' 4%nat))) (fmul (mB' 2%nat) (mB' 5%nat))) (mB' 6%nat))
                                 (fmul (to_F (nth 0 (trhoB T) xzero)) (gmask2 (to_F (fst gBx)) (csF (snd gBx)) (map to_F (try T))))).
    { rewrite vB. unfold termsB, termsF, termF, sF. cbn [map fold_left fst snd LogDer.fsum]. rewrite <-!to_F_nth, !finBf by lia.
      rewrite to_F_one. unfold mB'. field. }
    assert (hrA0 : to_F (nth 0 (trhoA T) xzero) <> fzero) by (apply xnz_sound; exact hnA).
    assert (hrC0 : to_F (nth 0 (trhoC T) xzero) <> fzero) by (apply xnz_sound; exact hnC).
    set (fAv := fA (coutX cout) (tru T) (trv T) (nth 0 (tab T) xzero) (nth 1 (tab T) xzero) (ttc T) (tkA T ++ trhoA T)
                   (trA T) (nth 1 (tfinA T) xzero) (nth 3 (tfinA T) xzero) (s_valP sig k (trA T)) (nth 2 (tfinA T) xzero)).
    assert (hfA : termsF (map sF (termsA (tkA T))) (map to_F (tfinA T)) = to_F fAv).
    { assert (f0 : to_F (nth 0 (tfinA T) xzero) = to_F (xeq_eval (trA T) (ttc T))).
      { rewrite (finA 0%nat) by lia. cbn [nth tablesA tmaskA maskv]. rewrite xmle_eq by lia. field. }
      assert (f4 : to_F (nth 4 (tfinA T) xzero)
                   = fsub (fadd (to_F (xmle (zhat (coutX cout) (tru T) (trv T)) (trA T)))
                                (fmul (to_F (nth 1 (tab T) xzero)) (to_F (s_valP sig k (trA T))))) (to_F (nth 0 (tab T) xzero))).
      { rewrite (finA 4%nat) by lia. cbn [nth tablesA tmaskA maskv]. rewrite (xmle_hh hw) by exact lrA.
        unfold s_valP. rewrite to_F_add, !to_F_mul, to_F_zval. unfold ExecProve.alT, ExecProve.beT.
        unfold zhat, zhatP, coutX, cinX. field. }
      unfold fAv, fA, Hh, xkk. rewrite !app_nth1 by lia.
      repeat rewrite ?to_F_add, ?to_F_mul, ?to_F_sub.
      unfold termsA, termsF, termF, sF. cbn [map fold_left fst snd LogDer.fsum]. rewrite <-!to_F_nth.
      rewrite f0, f4, to_F_neg. field. }
    assert (e8 : to_F (xmul (xsub clA fAv) (xinv (xkk (tkA T ++ trhoA T) 3))) = gmask2 (to_F (fst gAx)) (csF (snd gAx)) (map to_F (trA T))).
    { rewrite to_F_mul, to_F_sub, to_F_inv, vA, hfA. unfold xkk. rewrite app_nth2 by lia. rewrite dkA. cbn [Nat.sub].
      field. exact hrA0. }
    set (fCv := fC (ttz T) (tkC T ++ trhoC T) (trz T) (nth 1 (tfinC T) xzero) (nth 2 (tfinC T) xzero) (nth 3 (tfinC T) xzero)).
    assert (hfC : termsF (map sF (termsC (tkC T))) (map to_F (tfinC T)) = to_F fCv).
    { assert (f0 : to_F (nth 0 (tfinC T) xzero) = to_F (xeq_eval (trz T) (ttz T))).
      { rewrite (finC 0%nat) by lia. cbn [nth tablesC tmaskC maskv]. rewrite xmle_eq by lia. field. }
      unfold fCv, fC, xkk, xcube3. rewrite !app_nth1 by lia.
      repeat rewrite ?to_F_add, ?to_F_mul, ?to_F_sub.
      unfold termsC, termsF, termF, sF. cbn [map fold_left fst snd LogDer.fsum]. rewrite <-!to_F_nth.
      rewrite f0, !to_F_neg. field. }
    assert (e9 : to_F (xmul (xsub clC fCv) (xinv (xkk (tkC T ++ trhoC T) 3))) = gmask2 (to_F (fst gCx)) (csF (snd gCx)) (map to_F (trz T))).
    { rewrite to_F_mul, to_F_sub, to_F_inv, vC, hfC. unfold xkk. rewrite app_nth2 by lia. rewrite dkC. cbn [Nat.sub].
      field. exact hrC0. }
    unfold targets. cbv zeta. cbn [map].
    rewrite e1, e2, e4, e8, e9, (ew 0%nat), (ew 1%nat), (ew 2%nat) by lia. reflexivity.
  Qed.

End BackD.
