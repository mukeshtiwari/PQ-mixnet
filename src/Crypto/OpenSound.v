(* Soundness of the opening protocol (paper, Section 4.2) for two committed
   Reed-Solomon matrices, against an adaptive prover.

   Everything before the opening is fixed in this file: the committed
   words X i, the slots, the claimed values vals. P i is the decoding of
   row i. The big matrix (suffix B) and the small matrix (suffix S) have
   their own codes, rows and slots.

   A slot v is described, for a batching challenge kappa, by
     Lk kappa v    its vector (it may depend on kappa: "func" slots),
     cbk kappa v   the rows it combines, with weights,
     mcb v         its mask, as rows and weights.
   The claims enter through one hypothesis, Hbatch: the batched true value
   sum_v vsum P (cbk kappa v) (Lk kappa v) equals <kappa, tv> for a list
   tv of "true values". For slots with a fixed vector this is batch_sum in
   Opening.v; for the two kinds of slot of the implementation it is
   batch_mixed in SlotKinds.v.

   Challenges and messages:
     kappa in F^K;  the prover sends mu;
     cg = (c, (gamma_B, gamma_S));  the prover sends a vector ub v per slot
       and a proximity vector per matrix;
     J = (J_B, J_S): nqb and nqs distinct columns.
   AccO is the verifier's acceptance (value check and column checks).

   Hypotheses that stand for facts proven elsewhere:
     HfarB, HfarS   clb gam = false implies that the combination of the
                    committed rows with coefficients gam is not within e
                    of the code (clb is a boolean test of closeness);
     HdecB, HdecS   if more than pn |F|^(R-1) of the gam are close, the
                    matrix decodes: one set E of at most e columns outside
                    which every row agrees with the encoding of P i. This
                    is the proximity lemma (Lemma 4.2) plus unique decoding.

   Theorem open_sound. If the claimed values vals are not tv, the
   challenges for which the verifier accepts number at most open_bound. As
   fractions of all challenges its five terms are

       1/|F|            a false claim disappears in the batch      (kappa)
       1/|F|            the value check holds for a wrong V        (c)
       pn_B/|F|, pn_S/|F|   a far matrix gives a close combination (gamma)
       max over the two matrices of fall (n-e-1) nq / fall n nq
                        all column queries miss                    (J)

   the last five lines of the error budget of Theorem 5.2. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Proximity ReedSolomon Opening MatQueries.
Import ListNotations.

Section OpenSound.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation pw := (@pw F one mul).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation vsum := (@vsum F zero add mul).
  Local Notation pi := (@pi F zero add mul).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hq0 : (0 < length lf)%nat.
  Local Notation q := (length lf).

  (* ------------------------------------------------------------------ *)
  (* The two codes *)

  Variables omB omS : F.
  Variables nb kb eb nqb pnb : nat.
  Variables ns ks es nqs pns : nat.
  Hypothesis HkB : (kb <= nb)%nat.
  Hypothesis HkS : (ks <= ns)%nat.
  Hypothesis HnodesB : forall i j, (i < nb)%nat -> (j < nb)%nat -> pw omB i = pw omB j -> i = j.
  Hypothesis HnodesS : forall i j, (i < ns)%nat -> (j < ns)%nat -> pw omS i = pw omS j -> i = j.
  Hypothesis HeB : (2 * eb < nb - kb + 1)%nat.
  Hypothesis HeS : (2 * es < ns - ks + 1)%nat.

  Local Notation encB := (@rs_enc F zero one add mul omB).
  Local Notation encS := (@rs_enc F zero one add mul omS).
  Local Notation codeB := (@rs_code F zero one add mul omB nb kb).
  Local Notation codeS := (@rs_code F zero one add mul omS ns ks).

  (* committed words and decoded messages *)
  Variable X : nat -> nat -> F.
  Variable P : nat -> list F.

  (* rows: IB, IS all rows of a matrix; rws the rows combined in the
     proximity test, xmp the word of the proximity mask *)
  Variables IB IS rwsB rwsS : list nat.
  Variables xmpB xmpS : nat -> F.
  Local Notation RB := (length rwsB).
  Local Notation RS := (length rwsS).
  Local Notation GaB := (all_lists lf RB).
  Local Notation GaS := (all_lists lf RS).

  (* closeness of the proximity combination, as a boolean *)
  Variables clb cls : list F -> bool.
  Hypothesis HfarB : forall g, clb g = false -> ~ close nb eb codeB (pi xmpB (map X rwsB) g).
  Hypothesis HfarS : forall g, cls g = false -> ~ close ns es codeS (pi xmpS (map X rwsS) g).

  Definition manyB : Prop := (pnb * q ^ RB < length (filter clb GaB) * q)%nat.
  Definition manyS : Prop := (pns * q ^ RS < length (filter cls GaS) * q)%nat.

  Hypothesis HdecB : manyB -> exists E, (length E <= eb)%nat /\
    forall i, In i IB -> (length (P i) <= kb)%nat /\ agree_out nb E (X i) (encB (P i)).
  Hypothesis HdecS : manyS -> exists E, (length E <= es)%nat /\
    forall i, In i IS -> (length (P i) <= ks)%nat /\ agree_out ns E (X i) (encS (P i)).

  (* slots, claimed values and true values *)
  Variables vals tv : list F.
  Hypothesis Hvals : length vals = length tv.
  Variable Lk : list F -> nat -> list F.
  Variable cbk : list F -> nat -> list (nat * F).
  Variable mcb : nat -> list (nat * F).
  Variables svB svS : list nat.
  Hypothesis Hbatch : forall kp, In kp (all_lists lf (length vals)) ->
    fsum (map (fun v => vsum P (cbk kp v) (Lk kp v)) (svB ++ svS)) = dot kp tv.
  Hypothesis HrowB : forall kp v, In v svB -> forall i, In i (map fst (mcb v) ++ map fst (cbk kp v)) -> In i IB.
  Hypothesis HrowS : forall kp v, In v svS -> forall i, In i (map fst (mcb v) ++ map fst (cbk kp v)) -> In i IS.

  Local Notation K := (length vals).
  Definition cgT : Type := (F * (list F * list F))%type.
  Definition jT : Type := (list nat * list nat)%type.

  Definition OK : list (list F) := all_lists lf K.
  Definition OG : list (list F * list F) := list_prod GaB GaS.
  Definition OCG : list cgT := list_prod lf OG.
  Definition QB : list (list nat) := qspace nb nqb.
  Definition QS : list (list nat) := qspace ns nqs.
  Definition OJ : list jT := list_prod QB QS.

  (* the prover *)
  Variable mu : list F -> F.
  Variable ub : list F -> cgT -> nat -> list F.
  Variables pvB pvS : list F -> cgT -> list F.

  Definition maccB (kp : list F) (cg : cgT) (J : list nat) : Prop :=
    @macc F zero one add mul omB kb X xmpB rwsB (fst (snd cg)) (pvB kp cg) svB (ub kp cg) mcb (cbk kp) (fst cg) J.
  Definition maccS (kp : list F) (cg : cgT) (J : list nat) : Prop :=
    @macc F zero one add mul omS ks X xmpS rwsS (snd (snd cg)) (pvS kp cg) svS (ub kp cg) mcb (cbk kp) (fst cg) J.

  Definition AccO (kp : list F) (cg : cgT) (J : jT) : Prop :=
    fsum (map (fun v => dot (ub kp cg v) (Lk kp v)) (svB ++ svS)) = mu kp + fst cg * dot kp vals /\
    maccB kp cg (fst J) /\ maccS kp cg (snd J).

  Definition consB (kp : list F) (cg : cgT) : bool :=
    @consb F zero one add mul Fdec omB nb P svB (ub kp cg) mcb (cbk kp) (fst cg).
  Definition consS (kp : list F) (cg : cgT) : bool :=
    @consb F zero one add mul Fdec omS ns P svS (ub kp cg) mcb (cbk kp) (fst cg).

  Definition badB (kp : list F) (cg : cgT) : Prop :=
    (~ manyB /\ clb (fst (snd cg)) = false) \/ (manyB /\ consB kp cg = false).
  Definition badS (kp : list F) (cg : cgT) : Prop :=
    (~ manyS /\ cls (snd (snd cg)) = false) \/ (manyS /\ consS kp cg = false).

  Lemma badB_dec : forall kp cg, badB kp cg \/ ~ badB kp cg.
  Proof.
    intros kp cg. unfold badB.
    destruct (lt_dec (pnb * q ^ RB) (length (filter clb GaB) * q)) as [h | h];
      destruct (clb (fst (snd cg))); destruct (consB kp cg); unfold manyB; try tauto;
      right; intros [[h1 h2] | [h1 h2]]; try tauto; discriminate.
  Qed.

  Lemma badS_dec : forall kp cg, badS kp cg \/ ~ badS kp cg.
  Proof.
    intros kp cg. unfold badS.
    destruct (lt_dec (pns * q ^ RS) (length (filter cls GaS) * q)) as [h | h];
      destruct (cls (snd (snd cg))); destruct (consS kp cg); unfold manyS; try tauto;
      right; intros [[h1 h2] | [h1 h2]]; try tauto; discriminate.
  Qed.

  (* the decoded mask value, for a given kappa *)
  Definition mu' (kp : list F) : F := fsum (map (fun v => vsum P (mcb v) (Lk kp v)) (svB ++ svS)).

  (* ------------------------------------------------------------------ *)
  (* The bad events *)

  Definition Ek (kp : list F) : Prop := dot kp vals = dot kp tv.
  Definition Ec (kp : list F) (c : F) : Prop :=
    dot kp vals <> dot kp tv /\ mu kp + c * dot kp vals = mu' kp + c * dot kp tv.
  Definition EgB (g : list F) : Prop := ~ manyB /\ clb g = true.
  Definition EgS (g : list F) : Prop := ~ manyS /\ cls g = true.
  Definition EJ (kp : list F) (cg : cgT) (J : jT) : Prop :=
    (badB kp cg /\ maccB kp cg (fst J)) \/ (~ badB kp cg /\ badS kp cg /\ maccS kp cg (snd J)).

  Definition GbB : nat := (pnb * q ^ RB / q)%nat.
  Definition GbS : nat := (pns * q ^ RS / q)%nat.
  Definition QbB : nat := fall (nb - eb - 1) nqb.
  Definition QbS : nat := fall (ns - es - 1) nqs.

  Lemma card_Ek : vals <> tv -> card_le OK Ek (q ^ (K - 1)).
  Proof.
    intro hne. apply (card_le_of_filter (list_eq_dec Fdec)). intros b hb.
    assert (hl : length vals = length tv) by exact Hvals.
    eapply Nat.le_trans; [| exact (@batch_count F zero one add mul sub div opp inv Fdec Hf lf Hnd vals tv hl hne)].
    apply filter_length_imp. intros kp hk. apply feqb_true.
    rewrite (@dot_sym F zero one add mul sub div opp inv Hf vals kp),
            (@dot_sym F zero one add mul sub div opp inv Hf tv kp). exact (hb kp hk).
  Qed.

  Lemma card_Ec : forall kp, card_le lf (Ec kp) 1.
  Proof.
    intro kp. destruct (Fdec (dot kp vals) (dot kp tv)) as [e | e].
    + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
      intros c _ [hn _]. apply hn. exact e.
    + apply (card_le_of_filter Fdec). intros b hb.
      eapply Nat.le_trans;
        [| exact (@c_count F zero one add mul sub div opp inv Fdec Hf lf Hnd (mu kp) (mu' kp) (dot kp vals) (dot kp tv) e)].
      apply filter_length_imp. intros c hc. apply feqb_true. exact (proj2 (hb c hc)).
  Qed.

  Lemma card_Eg : forall (R pn : nat) (cl : list F -> bool),
    card_le (all_lists lf R)
            (fun g => ~ (pn * q ^ R < length (filter cl (all_lists lf R)) * q)%nat /\ cl g = true)
            (pn * q ^ R / q).
  Proof.
    intros R pn cl.
    destruct (lt_dec (pn * q ^ R) (length (filter cl (all_lists lf R)) * q)) as [h | h].
    + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
      intros g _ [hn _]. apply hn. exact h.
    + apply (card_le_of_filter (list_eq_dec Fdec)). intros b hb.
      eapply Nat.le_trans; [apply (filter_length_imp b cl); intros g hg; exact (proj2 (hb g hg)) |].
      apply Nat.div_le_lower_bound; lia.
  Qed.

  Lemma card_EJ : forall kp cg, card_le OJ (EJ kp cg) (Nat.max (QbB * length QS) (QbS * length QB)).
  Proof.
    intros kp cg.
    assert (ndec : forall x y : list nat, {x = y} + {x <> y}) by (apply list_eq_dec, Nat.eq_dec).
    destruct (badB_dec kp cg) as [hb | hb].
    + (* the big matrix is bad *)
      assert (hq : card_le QB (maccB kp cg) QbB).
      { apply (@mat_bad_queries F zero one add mul sub div opp inv Fdec Hf omB nb kb eb nqb HkB HnodesB HeB X P).
        destruct hb as [[_ hcl] | [hm hc]].
        + left. apply HfarB. exact hcl.
        + right. destruct (HdecB hm) as (E & hE & hrows). exists E; split; [exact hE | split; [| exact hc]].
          intros v hv i hi. apply hrows. exact (HrowB kp v hv i hi). }
      pose proof (card_le_prod_cyl ndec QB QS (maccB kp cg) QbB (qspace_NoDup ns nqs) hq) as h.
      eapply card_le_mono; [ | apply Nat.le_max_l | exact h].
      intros J _ [[_ ha] | [hn _]]; [exact ha | contradiction].
    + destruct (badS_dec kp cg) as [hs | hs].
      - assert (hq : card_le QS (maccS kp cg) QbS).
        { apply (@mat_bad_queries F zero one add mul sub div opp inv Fdec Hf omS ns ks es nqs HkS HnodesS HeS X P).
          destruct hs as [[_ hcl] | [hm hc]].
          + left. apply HfarS. exact hcl.
          + right. destruct (HdecS hm) as (E & hE & hrows). exists E; split; [exact hE | split; [| exact hc]].
            intros v hv i hi. apply hrows. exact (HrowS kp v hv i hi). }
        pose proof (card_le_prod_fiber ndec QB QS (fun J => maccS kp cg (snd J)) QbS (qspace_NoDup nb nqb)
                      (fun _ _ => hq)) as h.
        eapply card_le_mono; [ | apply Nat.le_max_r | exact h].
        intros J _ [[hbb _] | (_ & _ & ha)]; [contradiction | exact ha].
      - apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros J _ [[hbb _] | (_ & hss & _)]; contradiction.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Acceptance with wrong values goes through a bad event *)

  Lemma AccO_events : forall kp cg J, In kp OK -> AccO kp cg J ->
    Ek kp \/ Ec kp (fst cg) \/ EgB (fst (snd cg)) \/ EgS (snd (snd cg)) \/ EJ kp cg J.
  Proof.
    intros kp cg J hkp (hval & haB & haS).
    destruct (badB_dec kp cg) as [hb | hb]; [right; right; right; right; left; split; assumption |].
    destruct (badS_dec kp cg) as [hs | hs]; [right; right; right; right; right; tauto |].
    (* neither matrix is bad *)
    destruct (lt_dec (pnb * q ^ RB) (length (filter clb GaB) * q)) as [hmB | hmB].
    2:{ right; right; left. split; [exact hmB |].
        destruct (clb (fst (snd cg))) eqn:e; [reflexivity | exfalso; apply hb; left; split; [exact hmB | exact e]]. }
    destruct (lt_dec (pns * q ^ RS) (length (filter cls GaS) * q)) as [hmS | hmS].
    2:{ right; right; right; left. split; [exact hmS |].
        destruct (cls (snd (snd cg))) eqn:e; [reflexivity | exfalso; apply hs; left; split; [exact hmS | exact e]]. }
    assert (hcB : consB kp cg = true).
    { destruct (consB kp cg) eqn:e; [reflexivity | exfalso; apply hb; right; split; [exact hmB | exact e]]. }
    assert (hcS : consS kp cg = true).
    { destruct (consS kp cg) eqn:e; [reflexivity | exfalso; apply hs; right; split; [exact hmS | exact e]]. }
    destruct (HdecB hmB) as (EB & _ & hrB). destruct (HdecS hmS) as (ES & _ & hrS).
    destruct haB as (_ & _ & huB). destruct haS as (_ & _ & huS).
    (* every slot vector is the decoded combination *)
    assert (hall : forall v, In v (svB ++ svS) -> forall t,
              nth t (ub kp cg v) zero = nth t (@dm F add mul P (mcb v) (cbk kp v) (fst cg)) zero).
    { intros v hv. apply in_app_or in hv. destruct hv as [hv | hv].
      + apply (@mat_consistent F zero one add mul sub div opp inv Fdec Hf omB nb kb eb HkB HnodesB HeB
                 P svB (ub kp cg) mcb (cbk kp) (fst cg) hcB).
        - intros v' hv'. exact (proj1 (huB v' hv')).
        - intros v' hv' i hi. exact (proj1 (hrB i (HrowB kp v' hv' i hi))).
        - exact hv.
      + apply (@mat_consistent F zero one add mul sub div opp inv Fdec Hf omS ns ks es HkS HnodesS HeS
                 P svS (ub kp cg) mcb (cbk kp) (fst cg) hcS).
        - intros v' hv'. exact (proj1 (huS v' hv')).
        - intros v' hv' i hi. exact (proj1 (hrS i (HrowS kp v' hv' i hi))).
        - exact hv. }
    pose proof (@opening_values F zero one add mul sub div opp inv Hf P (Lk kp) mcb (cbk kp) (ub kp cg) (svB ++ svS)
                  (fst cg) (mu kp) (dot kp vals) (dot kp tv) hall (Hbatch kp hkp) hval) as heq.
    destruct (Fdec (dot kp vals) (dot kp tv)) as [e | e]; [left; exact e |].
    right; left. split; [exact e | exact heq].
  Qed.

  (* ------------------------------------------------------------------ *)

  Definition open_bound : nat :=
    (q ^ (K - 1) * length (list_prod OCG OJ)
     + 1 * length OG * length OJ * length OK
     + GbB * length GaS * q * length OJ * length OK
     + GbS * length GaB * q * length OJ * length OK
     + Nat.max (QbB * length QS) (QbS * length QB) * length OCG * length OK)%nat.

  Theorem open_sound : vals <> tv ->
    card_le (list_prod OK (list_prod OCG OJ))
            (fun w => AccO (fst w) (fst (snd w)) (snd (snd w)))
            open_bound.
  Proof.
    intro hne.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (ndec : forall x y : list nat, {x = y} + {x <> y}) by (apply list_eq_dec, Nat.eq_dec).
    assert (gdec : forall x y : list F * list F, {x = y} + {x <> y}) by (decide equality).
    assert (cgdec : forall x y : cgT, {x = y} + {x <> y}) by (unfold cgT; decide equality).
    assert (jdec : forall x y : jT, {x = y} + {x <> y}) by (unfold jT; decide equality).
    assert (cjdec : forall x y : cgT * jT, {x = y} + {x <> y}) by (decide equality).
    assert (hOK : NoDup OK) by (apply all_lists_NoDup; exact Hnd).
    assert (hGB : NoDup GaB) by (apply all_lists_NoDup; exact Hnd).
    assert (hGS : NoDup GaS) by (apply all_lists_NoDup; exact Hnd).
    assert (hOG : NoDup OG) by (apply NoDup_list_prod; assumption).
    assert (hOCG : NoDup OCG) by (apply NoDup_list_prod; assumption).
    assert (hOJ : NoDup OJ) by (apply NoDup_list_prod; apply qspace_NoDup).
    assert (hCJ : NoDup (list_prod OCG OJ)) by (apply NoDup_list_prod; assumption).
    (* kappa *)
    pose proof (card_le_prod_cyl cjdec OK (list_prod OCG OJ) Ek _ hCJ (card_Ek hne)) as h1.
    (* c *)
    assert (h2 : card_le (list_prod OK (list_prod OCG OJ)) (fun w => Ec (fst w) (fst (fst (snd w))))
                   (1 * length OG * length OJ * length OK)).
    { apply (card_le_prod_fiber ldec OK (list_prod OCG OJ) (fun w => Ec (fst w) (fst (fst (snd w)))) _ hOK).
      intros kp _. cbn [fst snd].
      pose proof (card_le_prod_cyl gdec lf OG (Ec kp) 1 hOG (card_Ec kp)) as hc.
      exact (card_le_prod_cyl jdec OCG OJ (fun cg => Ec kp (fst cg)) _ hOJ hc). }
    (* gamma, big matrix *)
    assert (h3 : card_le (list_prod OK (list_prod OCG OJ)) (fun w => EgB (fst (snd (fst (snd w)))))
                   (GbB * length GaS * q * length OJ * length OK)).
    { apply (card_le_prod_fiber ldec OK (list_prod OCG OJ) (fun w => EgB (fst (snd (fst (snd w))))) _ hOK).
      intros kp _. cbn [fst snd].
      pose proof (card_le_prod_cyl ldec GaB GaS EgB GbB hGS (card_Eg RB pnb clb)) as hg.
      pose proof (card_le_prod_fiber Fdec lf OG (fun cg => EgB (fst (snd cg))) _ Hnd (fun _ _ => hg)) as hcg.
      exact (card_le_prod_cyl jdec OCG OJ (fun cg => EgB (fst (snd cg))) _ hOJ hcg). }
    (* gamma, small matrix *)
    assert (h4 : card_le (list_prod OK (list_prod OCG OJ)) (fun w => EgS (snd (snd (fst (snd w)))))
                   (GbS * length GaB * q * length OJ * length OK)).
    { apply (card_le_prod_fiber ldec OK (list_prod OCG OJ) (fun w => EgS (snd (snd (fst (snd w))))) _ hOK).
      intros kp _. cbn [fst snd].
      pose proof (card_le_prod_fiber ldec GaB GaS (fun g => EgS (snd g)) GbS hGB
                    (fun _ _ => card_Eg RS pns cls)) as hg.
      pose proof (card_le_prod_fiber Fdec lf OG (fun cg => EgS (snd (snd cg))) _ Hnd (fun _ _ => hg)) as hcg.
      exact (card_le_prod_cyl jdec OCG OJ (fun cg => EgS (snd (snd cg))) _ hOJ hcg). }
    (* queries *)
    assert (h5 : card_le (list_prod OK (list_prod OCG OJ)) (fun w => EJ (fst w) (fst (snd w)) (snd (snd w)))
                   (Nat.max (QbB * length QS) (QbS * length QB) * length OCG * length OK)).
    { apply (card_le_prod_fiber ldec OK (list_prod OCG OJ) (fun w => EJ (fst w) (fst (snd w)) (snd (snd w))) _ hOK).
      intros kp _. cbn [fst snd].
      apply (card_le_prod_fiber cgdec OCG OJ (fun w => EJ kp (fst w) (snd w)) _ hOCG).
      intros cg _. cbn [fst snd]. apply card_EJ. }
    pose proof (card_le_or _ _ _ _ _ h1 (card_le_or _ _ _ _ _ h2 (card_le_or _ _ _ _ _ h3 (card_le_or _ _ _ _ _ h4 h5)))) as hor.
    eapply card_le_mono; [ | | exact hor].
    + intros [kp [cg J]] hin hacc. cbn [fst snd] in *.
      apply in_prod_iff in hin. destruct hin as [hkp _].
      destruct (AccO_events kp cg J hkp hacc) as [h | [h | [h | [h | h]]]]; tauto.
    + unfold open_bound. lia.
  Qed.

End OpenSound.
