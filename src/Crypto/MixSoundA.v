(* Soundness of the permutation part of the shuffle proof: the challenge
   (rho, alpha, beta), the challenge (tc, k1, k2, k3, rhoA) and sumcheck A,
   against an adaptive prover.

   The first challenge is a point c1 of F^(2N+2), read as
   alpha :: rho_u ++ rho_v ++ [beta]. The verifier's tables are abstract
   functions of c1, constrained by two hypotheses that say what they are
   on the cube:

     Hh    htabT c1 (pt i)  = dot (form (rr i) i) c1          (h_i)
     Hhh   hhtab .. (pt j)  = dot (form (co j) (sigma_j)) c1  (hhat_j)

   where rr i is re-randomised input i for the committed witness, co j is
   output j, and sigma_j = sg (pt j) is the committed table sigma. For the
   concrete tables of the protocol these are proven in MixBridge.v.

   Acceptance (AccA). The verifier runs sumcheck A from the claim
   k1 + k2 + rhoA * G_A, receives (U, Uhat, s, H), and claims 1, 2, 3 and 8
   of the paper hold for the committed tables. Good says that the fourth
   value is right too: H = hstar(r). (That H is right is what sumcheck B
   establishes; see MixSoundB.v.)

   Theorem soundA. If the committed (sigma, W) is not a shuffle of the
   inputs, the challenges (c1, c2, r) for which the verifier accepts and
   H is right number at most

     (2 tau - 1) |F|^(2N+1) * |C2 x RA|
     + ((ell + 1) |F|^(ell+3) * |RA| + (3 (ell - 1) + 5) |F|^(ell-1) * |C2|) * |C1|,

   a fraction ((2 tau - 1) + (ell + 1) + (3 ell + 2)) / |F|: the first
   three budget lines of Theorem 5.2. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask SumcheckSound PolyFun MaskedExt CubeIndex EqBatch Bgv MixMultiset MixSummands MixIdentities MixSoundC.
Import ListNotations.

Section MixSoundA.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation nF := (@nF F zero one add).
  Local Notation allzero := (@allzero F zero Fdec).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation sc_run := (@sc_run F zero one add mul Fdec).
  Local Notation pt := (@pt F zero one).
  Local Notation gA := (@gA F zero one add mul sub).
  Local Notation TA1 := (@TA1 F one mul sub).
  Local Notation TA2 := (@TA2 F one add mul sub).
  Local Notation SA := (@SA F zero one add sub).
  Local Notation GtrueA := (@GtrueA F zero one add mul).
  Local Notation hhtab := (@hhtab F add mul sub).
  Local Notation form := (@form F one opp).
  Local Notation Sin := (@Sin F zero one add opp).
  Local Notation Tout := (@Tout F one opp).
  Local Notation is_shuffle := (@is_shuffle F zero one add).
  Local Notation kk := (@kk F zero).
  Local Notation ctx := (@ctx F).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Lemma mul_one_inv : forall x y : F, x * y = one -> y <> zero /\ inv y = x.
  Proof.
    intros x y h.
    assert (hy : y <> zero).
    { intro e. rewrite e in h. apply (@zero_neq_one F eq zero one _).
      rewrite <-h. field. }
    split; [exact hy |].
    assert (e : x = (x * y) * inv y) by (field; exact hy).
    rewrite e, h. field. exact hy.
  Qed.

  Variables N ell : nat.
  Hypothesis Hell : (1 <= ell)%nat.
  Local Notation tau := (2 ^ ell)%nat.

  (* the statement and the committed first message *)
  Variables rr co : nat -> ctx.
  Variable sg : list F -> F.
  Definition sgf (j : nat) : F := sg (pt ell j).

  Hypothesis Hchar : forall k, (0 < k <= tau)%nat -> nF k <> zero.
  Hypothesis Hrr : forall i, (i < tau)%nat -> length (fst (rr i)) = N /\ length (snd (rr i)) = N.
  Hypothesis Hco : forall j, (j < tau)%nat -> length (fst (co j)) = N /\ length (snd (co j)) = N.

  Definition C1 : list (list F) := all_lists lf (S (N + N + 1)).
  Definition C2 : list (list F * list F) := list_prod (all_lists lf ell) (all_lists lf 4).
  Definition RA : list (list F) := all_lists lf ell.

  (* the verifier's tables, as functions of the first challenge *)
  Variables htabT zh : list F -> list F -> F.
  Variables al be : list F -> F.

  Hypothesis Hh : forall c1, In c1 C1 -> forall i, (i < tau)%nat ->
    htabT c1 (pt ell i) = dot (form (rr i) (nF i)) c1.
  Hypothesis Hhh : forall c1, In c1 C1 -> forall j, (j < tau)%nat ->
    hhtab sg (zh c1) (al c1) (be c1) (pt ell j) = dot (form (co j) (sgf j)) c1.

  (* the prover *)
  Variables u uh : list F -> list F -> F.
  Variables au auh asg ah a0A GA : list F -> F.
  Variable csA : list F -> list (list F).
  Variable stratA : list F -> list F * list F -> list F -> list F.
  Variables eU eUh eS eH : list F -> list F * list F -> list F -> F.

  Hypothesis HcsA : forall c1, length (csA c1) = ell.
  Hypothesis HdegA : forall c1 i, (i < ell)%nat -> (length (nth i (csA c1) []) <= degA ell i)%nat.
  Hypothesis HmsgA : forall c1 c2 pre, (length (stratA c1 c2 pre) <= S (degA ell (length pre)))%nat.

  Definition gAf (c1 : list F) (c2 : list F * list F) : list F -> F :=
    gA ell (u c1) (uh c1) sg (htabT c1) (zh c1) (au c1) (auh c1) (asg c1) (ah c1) (al c1) (be c1)
       (fst c2) (kk (snd c2) 0) (kk (snd c2) 1) (kk (snd c2) 2) (kk (snd c2) 3) (a0A c1) (csA c1).

  Definition claimA (c1 : list F) (c2 : list F * list F) : F :=
    kk (snd c2) 0 + kk (snd c2) 1 + kk (snd c2) 3 * GA c1.

  Definition AccA (c1 : list F) (c2 : list F * list F) (rA : list F) : Prop :=
    exists clA,
      sc_run (stratA c1 c2) [] rA (claimA c1 c2) = Some clA /\
      eU c1 c2 rA = mstar ell (u c1) (au c1) rA /\
      eUh c1 c2 rA = mstar ell (uh c1) (auh c1) rA /\
      eS c1 c2 rA = mstar ell sg (asg c1) rA /\
      clA = eqp rA (fst c2)
              * (kk (snd c2) 0 * (eU c1 c2 rA * eH c1 c2 rA)
                 + kk (snd c2) 1 * (eUh c1 c2 rA * (mle ell (zh c1) rA + be c1 * eS c1 c2 rA - al c1)))
            + kk (snd c2) 2 * (eU c1 c2 rA - eUh c1 c2 rA)
            + kk (snd c2) 3 * gmask (a0A c1) (csA c1) rA.

  Definition Good (c1 : list F) (c2 : list F * list F) (rA : list F) : Prop :=
    eH c1 c2 rA = mstar ell (htabT c1) (ah c1) rA.

  Lemma AccA_final : forall c1 c2 rA, AccA c1 c2 rA -> Good c1 c2 rA ->
    sc_run (stratA c1 c2) [] rA (claimA c1 c2) = Some (gAf c1 c2 rA).
  Proof.
    intros c1 c2 rA (clA & hrun & e1 & e2 & e3 & ecl) hg. unfold Good in hg.
    rewrite hrun. f_equal. rewrite ecl, hg, e1, e2, e3. reflexivity.
  Qed.

  (* The three facts that sumcheck A is about. *)
  Definition Facts (c1 : list F) : Prop :=
    (forall b, In b (cube ell) -> u c1 b * htabT c1 b = one) /\
    (forall b, In b (cube ell) -> uh c1 b * hhtab sg (zh c1) (al c1) (be c1) b = one) /\
    SA ell (u c1) (uh c1) = zero.

  Definition NotFacts (c1 : list F) : Prop :=
    (exists T, In T [TA1 (u c1) (htabT c1); TA2 (uh c1) sg (zh c1) (al c1) (be c1)] /\
               exists b, In b (cube ell) /\ T b <> zero)
    \/ SA ell (u c1) (uh c1) <> zero.

  Lemma facts_dec : forall c1, Facts c1 \/ NotFacts c1.
  Proof.
    intro c1.
    assert (hdec : forall T : list F -> F,
              (exists b, In b (cube ell) /\ T b <> zero) \/ (forall b, In b (cube ell) -> T b = zero)).
    { intro T. destruct (Exists_dec (fun b => T b <> zero) (cube ell)) as [h | h].
      + intro b. destruct (Fdec (T b) zero); [right | left]; tauto.
      + left. apply Exists_exists in h. exact h.
      + right. intros b hb. destruct (Fdec (T b) zero) as [e | e]; [exact e | exfalso].
        apply h. apply Exists_exists. exists b; split; assumption. }
    destruct (hdec (TA1 (u c1) (htabT c1))) as [h1 | h1].
    { right. left. exists (TA1 (u c1) (htabT c1)); split; [cbn; tauto | exact h1]. }
    destruct (hdec (TA2 (uh c1) sg (zh c1) (al c1) (be c1))) as [h2 | h2].
    { right. left. exists (TA2 (uh c1) sg (zh c1) (al c1) (be c1)); split; [cbn; tauto | exact h2]. }
    destruct (Fdec (SA ell (u c1) (uh c1)) zero) as [h3 | h3]; [| right; right; exact h3].
    left. split; [| split; [| exact h3]].
    + intros b hb. specialize (h1 b hb). unfold MixIdentities.TA1 in h1.
      assert (e : u c1 b * htabT c1 b = (u c1 b * htabT c1 b - one) + one) by field. rewrite e, h1. field.
    + intros b hb. specialize (h2 b hb). unfold MixIdentities.TA2 in h2.
      assert (e : uh c1 b * hhtab sg (zh c1) (al c1) (be c1) b
                  = (uh c1 b * hhtab sg (zh c1) (al c1) (be c1) b - one) + one) by field.
      rewrite e, h2. field.
  Qed.

  (* The logarithmic-derivative identity with non-zero denominators. *)
  Definition E1 (c1 : list F) : Prop :=
    (forall a, In a (Sin tau rr ++ Tout tau co sgf) -> dot a c1 <> zero) /\
    fsum (map (fun a => inv (dot a c1)) (Sin tau rr)) = fsum (map (fun a => inv (dot a c1)) (Tout tau co sgf)).

  Lemma facts_E1 : forall c1, In c1 C1 -> Facts c1 -> E1 c1.
  Proof.
    intros c1 hc1 (f1 & f2 & f3).
    assert (hin : forall i, (i < tau)%nat ->
              dot (form (rr i) (nF i)) c1 <> zero /\ inv (dot (form (rr i) (nF i)) c1) = u c1 (pt ell i)).
    { intros i hi. rewrite <-(Hh c1 hc1 i hi). apply mul_one_inv. apply f1.
      apply (@pt_cube F zero one). }
    assert (hout : forall j, (j < tau)%nat ->
              dot (form (co j) (sgf j)) c1 <> zero /\ inv (dot (form (co j) (sgf j)) c1) = uh c1 (pt ell j)).
    { intros j hj. rewrite <-(Hhh c1 hc1 j hj). apply mul_one_inv. apply f2.
      apply (@pt_cube F zero one). }
    split.
    + intros a ha. apply in_app_or in ha. unfold MixMultiset.Sin, MixMultiset.Tout in ha.
      destruct ha as [ha | ha]; apply in_map_iff in ha; destruct ha as (i & <- & hi); apply in_seq in hi.
      - apply hin; lia.
      - apply hout; lia.
    + unfold MixMultiset.Sin, MixMultiset.Tout. rewrite !map_map.
      rewrite (@fsum_map_ext F zero add _ _ (fun i => u c1 (pt ell i)))
        by (intros i hi; apply in_seq in hi; apply hin; lia).
      rewrite (@fsum_map_ext F zero add _ (fun j => inv (dot (form (co j) (sgf j)) c1)) (fun j => uh c1 (pt ell j)))
        by (intros j hj; apply in_seq in hj; apply hout; lia).
      rewrite <-!(@cube_sum_seq F zero one add mul sub div opp inv Hf ell).
      unfold MixIdentities.SA in f3.
      rewrite (@fsum_map_sub F zero one add mul sub div opp inv Hf) in f3.
      assert (e : fsum (map (u c1) (cube ell))
                  = (fsum (map (u c1) (cube ell)) - fsum (map (uh c1) (cube ell))) + fsum (map (uh c1) (cube ell)))
        by field.
      rewrite e, f3. field.
  Qed.

  Definition b1 : nat := ((2 * tau - 1) * length lf ^ (N + N + 1))%nat.

  Definition boundA : nat :=
    (b1 * length (list_prod C2 RA)
     + ((ell + 1) * length lf ^ (ell + (2 + 2) - 1) * length RA
        + dsum (degA ell) 0 ell * length lf ^ (ell - 1) * length C2) * length C1)%nat.

  Theorem soundA :
    ~ is_shuffle tau rr co sgf ->
    card_le (list_prod C1 (list_prod C2 RA))
            (fun w => AccA (fst w) (fst (snd w)) (snd (snd w)) /\ Good (fst w) (fst (snd w)) (snd (snd w)))
            boundA.
  Proof.
    intro hns.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (pdec : forall x y : list F * list F, {x = y} + {x <> y}) by (decide equality).
    assert (qdec : forall x y : (list F * list F) * list F, {x = y} + {x <> y}) by (decide equality).
    assert (hC1 : NoDup C1) by (apply all_lists_NoDup; exact Hnd).
    assert (hC2 : NoDup C2) by (apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd).
    assert (hRA : NoDup RA) by (apply all_lists_NoDup; exact Hnd).
    (* the first challenge: the three facts can only hold through the identity *)
    assert (hE1 : card_le C1 E1 b1).
    { apply (card_le_of_filter ldec). intros bad hb.
      exact (@multiset_step F zero one add mul sub div opp inv Fdec Hf N tau rr co sgf Hchar Hrr Hco
               lf Hnd Hall hns bad hb). }
    assert (hF : card_le C1 Facts b1).
    { eapply card_le_mono; [ | apply le_n | exact hE1]. intros c1 hc1 hf. apply facts_E1; assumption. }
    pose proof (card_le_prod_cyl qdec C1 (list_prod C2 RA) Facts _ (NoDup_list_prod _ _ hC2 hRA) hF) as hX1.
    (* the other challenges, for a first challenge at which the facts fail *)
    assert (hX2 : card_le (list_prod C1 (list_prod C2 RA))
                    (fun w => NotFacts (fst w) /\ AccA (fst w) (fst (snd w)) (snd (snd w))
                              /\ Good (fst w) (fst (snd w)) (snd (snd w)))
                    (((ell + 1) * length lf ^ (ell + (2 + 2) - 1) * length RA
                      + dsum (degA ell) 0 ell * length lf ^ (ell - 1) * length C2) * length C1)).
    { apply (card_le_prod_fiber ldec C1 (list_prod C2 RA)
               (fun w => NotFacts (fst w) /\ AccA (fst w) (fst (snd w)) (snd (snd w))
                         /\ Good (fst w) (fst (snd w)) (snd (snd w))) _ hC1).
      intros c1 _. cbn [fst snd].
      destruct (facts_dec c1) as [hf | hnf].
      { (* the facts hold: NotFacts may still hold, but then we use the bound below anyway *)
        destruct (facts_dec c1) as [_ | _]; apply (card_le_mono _ _ (fun w => NotFacts c1 /\ False) _ 0);
          try lia; try (apply card_le_false; tauto).
        all: intros w _ (hn & _ & _); split; [exact hn |];
          destruct hf as (f1 & f2 & f3); destruct hn as [(T & hT & b & hb & hne) | hne].
        all: try (apply hne; exact f3).
        all: cbn in hT; destruct hT as [<- | [<- | []]]; apply hne.
        all: try (unfold MixIdentities.TA1; rewrite (f1 b hb); field).
        all: unfold MixIdentities.TA2; rewrite (f2 b hb); field. }
      set (E2 := fun c2 => claimA c1 c2 = tsum (gAf c1 c2) [] ell).
      assert (hbatch : (exists T, In T [TA1 (u c1) (htabT c1); TA2 (uh c1) sg (zh c1) (al c1) (be c1)] /\
                                  exists b, In b (cube ell) /\ T b <> zero)
                       \/ allzero [SA ell (u c1) (uh c1); GtrueA ell (a0A c1) (csA c1) - GA c1] = false).
      { destruct hnf as [h | h]; [left; exact h | right].
        apply (@allzero_false_in F zero Fdec _ (SA ell (u c1) (uh c1))); [cbn; tauto | exact h]. }
      assert (h2 : card_le C2 E2 ((ell + 1) * length lf ^ (ell + (2 + 2) - 1))).
      { pose proof (@eq_batch_card F zero one add mul sub div opp inv Fdec Hf lf Hnd ell _ _ hbatch) as h.
        cbn [length] in h.
        eapply card_le_mono; [ | apply le_n | exact h].
        intros [tc kA] hin e. cbn [fst snd]. unfold C2 in hin. apply in_prod_iff in hin. destruct hin as [htc hk].
        apply all_lists_In in hk. destruct hk as [hk _]. apply all_lists_In in htc. destruct htc as [htc _].
        rewrite (@list4 F zero kA hk).
        rewrite <-(@A_claim_diff F zero one add mul sub div opp inv Hf ell Hell (u c1) (uh c1) sg (htabT c1) (zh c1)
                     (au c1) (auh c1) (asg c1) (ah c1) (al c1) (be c1) tc
                     (kk kA 0) (kk kA 1) (kk kA 2) (kk kA 3) (a0A c1) (csA c1) htc (GA c1)).
        unfold E2, gAf, claimA in e. cbn [fst snd] in e. rewrite <-e. field. }
      pose proof (card_le_prod_cyl ldec C2 RA E2 _ hRA h2) as hE2.
      assert (h3 : card_le (list_prod C2 RA) (fun w => ~ E2 (fst w) /\ AccA c1 (fst w) (snd w) /\ Good c1 (fst w) (snd w))
                     (dsum (degA ell) 0 ell * length lf ^ (ell - 1) * length C2)).
      { apply (card_le_prod_fiber pdec C2 RA
                 (fun w => ~ E2 (fst w) /\ AccA c1 (fst w) (snd w) /\ Good c1 (fst w) (snd w)) _ hC2).
        intros c2 _. cbn [fst snd].
        destruct (Fdec (claimA c1 c2) (tsum (gAf c1 c2) [] ell)) as [e | e].
        + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
          intros rA _ [hn _]. apply hn. exact e.
        + pose proof (@sc_sound F zero one add mul sub div opp inv Fdec Hf lf Hnd (gAf c1 c2) ell (degA ell)
                        (stratA c1 c2) (HmsgA c1 c2)
                        (@certA F zero one add mul sub div opp inv Hf ell (u c1) (uh c1) sg (htabT c1) (zh c1)
                           (au c1) (auh c1) (asg c1) (ah c1) (al c1) (be c1) (fst c2)
                           (kk (snd c2) 0) (kk (snd c2) 1) (kk (snd c2) 2) (kk (snd c2) 3) (a0A c1) (csA c1)
                           (HcsA c1) (HdegA c1))
                        ell [] (claimA c1 c2) eq_refl e) as h.
          eapply card_le_mono; [ | apply le_n | exact h].
          intros rA _ (_ & hacc & hg). cbn [app length]. apply AccA_final; assumption. }
      pose proof (card_le_or _ _ _ _ _ hE2 h3) as hor.
      eapply card_le_mono; [ | apply le_n | exact hor].
      intros [c2 rA] _ (_ & hacc & hg). cbn [fst snd] in *.
      destruct (Fdec (claimA c1 c2) (tsum (gAf c1 c2) [] ell)) as [e | e]; [left; exact e | right; tauto]. }
    pose proof (card_le_or _ _ _ _ _ hX1 hX2) as hor.
    eapply card_le_mono; [ | | exact hor].
    + intros w _ [hacc hg]. destruct (facts_dec (fst w)) as [hf | hnf]; [left; exact hf | right; tauto].
    + unfold boundA. lia.
  Qed.

End MixSoundA.
