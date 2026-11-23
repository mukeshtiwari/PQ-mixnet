(* Zero knowledge at the level of transcripts (paper, Theorem 5.3, steps
   (1) to (3)): the honest prover and the simulator as programs, and
   equality of their transcript distributions.

   Distributions are uniform over finite lists of coins, so "the same
   distribution" is stated as: the list of honest transcripts over all
   prover coins is a permutation of the list of simulated transcripts over
   all simulator coins (zk_perm).

   One masked sumcheck (Section OneSumcheck). The summand is
   f + rho * gmask a0 cs, the challenges rs are fixed.
     honest prover   coins (a0, cs); sends the mask sum G and the round
                     messages hmsgs, built from coefficient lists pf of the
                     round functions of f (hypothesis Hpf);
     simulator       coins (G, tails), uniform; given only the claim cf of
                     the unmasked part, sends G and sim_run tails rs
                     (cf + rho * G).
   - sc_complete: the honest messages pass the verifier's round checks for
     the claim cf + rho * G.
   - sc_honest_sim: the honest transcript on (a0, cs) is the simulated
     transcript on mview (a0, cs).
   - sc_zk: the two transcript lists are permutations of each other.

   The sumcheck layer of the shuffle proof (Section Layer): the masked
   evaluations and three masked sumchecks. The unmasked parts fA, fB, fC
   may depend on the mask coefficients avs; the verifier computes the
   unmasked claims from the evaluations it received (cA, cB, cC with HcA,
   HcB, HcC: for the honest prover these are the true sums).
   - layer_honest_sim, layer_zk: as above, for the whole layer.

   Not here: the opening (ZkOpen.v has its bijection, not its transcript),
   and the instantiation of fA, fB, fC, cA, cB, cC with the summands of
   MixSummands.v. Bad challenges (Z = 0 at a point, rho = 0) are excluded
   by the hypotheses Hgood and Hok. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith FinFun.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask MaskedExt ZkBlocks ZkSumcheck ZkMix.
Import ListNotations.

Section Generic.

  Lemma NoDup_map_inj_on : forall {R V : Type} (f : R -> V) (l : list R), NoDup l ->
    (forall x x', In x l -> In x' l -> f x = f x' -> x = x') -> NoDup (map f l).
  Proof.
    intros R V f l h; induction h as [| x l hx h ih]; intro hinj; cbn; constructor.
    + intro hin. apply in_map_iff in hin. destruct hin as (x' & e & hx').
      assert (x' = x) by (apply hinj; [right; exact hx' | left; reflexivity | exact e]). subst x'. contradiction.
    + apply ih. intros a a' ha ha'. apply hinj; right; assumption.
  Qed.

  Lemma perm_bij : forall {R V : Type} (f : R -> V) (Rl : list R) (Vl : list V),
    NoDup Rl -> NoDup Vl ->
    (forall x, In x Rl -> In (f x) Vl) ->
    (forall x x', In x Rl -> In x' Rl -> f x = f x' -> x = x') ->
    (forall v, In v Vl -> exists x, In x Rl /\ f x = v) ->
    Permutation (map f Rl) Vl.
  Proof.
    intros R V f Rl Vl hR hV hin hinj hsurj.
    apply NoDup_Permutation; [apply NoDup_map_inj_on; assumption | exact hV |].
    intro v. split.
    + intro h. apply in_map_iff in h. destruct h as (x & <- & hx). apply hin. exact hx.
    + intro h. destruct (hsurj v h) as (x & hx & <-). apply in_map. exact hx.
  Qed.

  (* Honest transcripts over all prover coins and simulated transcripts
     over all simulator coins: the same multiset. *)
  Theorem zk_perm : forall {R V T : Type} (f : R -> V) (hon : R -> T) (sim : V -> T) (Rl : list R) (Vl : list V),
    NoDup Rl -> NoDup Vl ->
    (forall x, In x Rl -> In (f x) Vl) ->
    (forall x x', In x Rl -> In x' Rl -> f x = f x' -> x = x') ->
    (forall v, In v Vl -> exists x, In x Rl /\ f x = v) ->
    (forall x, In x Rl -> hon x = sim (f x)) ->
    Permutation (map hon Rl) (map sim Vl).
  Proof.
    intros R V T f hon sim Rl Vl hR hV hin hinj hsurj hs.
    rewrite (map_ext_in hon (fun x => sim (f x)) Rl hs), <-(map_map f sim).
    apply Permutation_map. apply perm_bij; assumption.
  Qed.

End Generic.

Section ZkTranscript.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation fsum := (@fsum F zero add).
  Local Notation peval := (@eval F zero add mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation rnd := (@rnd F zero one add).
  Local Notation honest := (@honest F zero one add mul).
  Local Notation sc_verify := (@sc_verify F zero one add mul Fdec).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation W := (@W F zero one add mul).
  Local Notation p2 := (@p2 F one add mul).
  Local Notation hmsg := (@hmsg F zero one add mul).
  Local Notation hmsgs := (@hmsgs F zero one add mul).
  Local Notation params := (@params F one add mul).
  Local Notation mview := (@mview F zero one add mul).
  Local Notation sim_run := (@sim_run F zero one add mul sub inv).
  Local Notation okparams := (@okparams F zero).
  Local Notation comp_map := (@comp_map F add mul).
  Local Notation shaped := (@shaped F).
  Local Notation evs := (@evs F zero one add mul sub).
  Local Notation View := (@View F zero one add mul sub).
  Local Notation goodspecs := (@goodspecs F zero one mul sub).

  (* ------------------------------------------------------------------ *)
  (* list tools *)

  Lemma skipn_cons_nth : forall (l : list F) j, (j < length l)%nat -> skipn j l = nth j l zero :: skipn (S j) l.
  Proof.
    induction l as [| x l ih]; intros j h; [cbn in h; lia |].
    destruct j as [| j]; [reflexivity |]. cbn [skipn nth]. apply ih. cbn in h. lia.
  Qed.

  Lemma firstn_snoc_nth : forall (l : list F) j, (j < length l)%nat -> firstn j l ++ [nth j l zero] = firstn (S j) l.
  Proof.
    induction l as [| x l ih]; intros j h; [cbn in h; lia |].
    destruct j as [| j]; [reflexivity |]. cbn [firstn nth app]. f_equal. apply ih. cbn in h. lia.
  Qed.

  (* a list of messages that evaluate to the round functions is honest *)
  Lemma honest_of_evals : forall (g : list F -> F) (msg : nat -> list F) (rs : list F) k j,
    length rs = (j + k)%nat ->
    (forall i X, (j <= i < j + k)%nat -> peval (msg i) X = rnd g (firstn i rs) (length rs - 1 - i) X) ->
    honest g (firstn j rs) (map msg (seq j k)) (skipn j rs).
  Proof.
    intros g msg rs; induction k as [| k ih]; intros j hl hm.
    + rewrite skipn_all2 by lia. cbn. exact I.
    + rewrite (skipn_cons_nth rs j) by lia. cbn [seq map Sumcheck.honest]. split.
      - intro X. rewrite (hm j X) by lia. rewrite length_skipn.
        replace (length rs - S j)%nat with (length rs - 1 - j)%nat by lia. reflexivity.
      - rewrite firstn_snoc_nth by lia. apply ih; [lia | intros i X hi; apply hm; lia].
  Qed.

  Lemma tsum_lin : forall (f g : list F -> F) (c : F) pre k,
    tsum (fun x => f x + c * g x) pre k = tsum f pre k + c * tsum g pre k.
  Proof.
    intros f g c pre k. unfold Sumcheck.tsum.
    rewrite (@fsum_map_add F zero one add mul sub div opp inv Hf _ (fun b => f (pre ++ b)) (fun b => c * g (pre ++ b))).
    rewrite (@fsum_map_mul_l F zero one add mul sub div opp inv Hf). reflexivity.
  Qed.

  Lemma rnd_lin : forall (f g : list F -> F) (c : F) pre k X,
    rnd (fun x => f x + c * g x) pre k X = rnd f pre k X + c * rnd g pre k X.
  Proof.
    intros f g c pre k X. unfold Sumcheck.rnd.
    rewrite (@fsum_map_add F zero one add mul sub div opp inv Hf _ (fun b => f (pre ++ X :: b))
               (fun b => c * g (pre ++ X :: b))).
    rewrite (@fsum_map_mul_l F zero one add mul sub div opp inv Hf). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* all coefficient lists of a given shape *)

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Fixpoint all_shaped (degs : list nat) : list (list (list F)) :=
    match degs with
    | [] => [[]]
    | d :: ds => map (fun p => fst p :: snd p) (list_prod (all_lists lf d) (all_shaped ds))
    end.

  Lemma all_shaped_In : forall degs ls, In ls (all_shaped degs) <-> shaped degs ls.
  Proof.
    induction degs as [| d ds ih]; intro ls; cbn [all_shaped]; split.
    + intros [<- | []]. constructor.
    + intro h. inversion h. left. reflexivity.
    + intro h. apply in_map_iff in h. destruct h as ([l ls'] & <- & hp). apply in_prod_iff in hp.
      destruct hp as [hl hls]. apply all_lists_In in hl. cbn [fst snd]. constructor; [tauto | apply ih; exact hls].
    + intro h. inversion h as [| ? l ? ls' hl hls]; subst. apply in_map_iff. exists (l, ls'). split; [reflexivity |].
      apply in_prod_iff. split; [| apply ih; exact hls].
      apply all_lists_In. split; [reflexivity | apply Forall_forall; intros; apply Hall].
  Qed.

  Lemma all_shaped_NoDup : forall degs, NoDup (all_shaped degs).
  Proof.
    induction degs as [| d ds ih]; cbn [all_shaped]; [repeat constructor; intros [] |].
    apply Injective_map_NoDup.
    + intros [x1 y1] [x2 y2] e. cbn in e. injection e as -> ->. reflexivity.
    + apply NoDup_list_prod; [apply all_lists_NoDup; exact Hnd | exact ih].
  Qed.

  Definition masks (degs : list nat) : list (F * list (list F)) := list_prod lf (all_shaped degs).

  Lemma masks_In : forall degs x, In x (masks degs) <-> shaped degs (snd x).
  Proof.
    intros degs [a0 cs]. unfold masks. rewrite in_prod_iff, all_shaped_In. cbn [snd]. split; [tauto |].
    intro h. split; [apply Hall | exact h].
  Qed.

  Lemma masks_NoDup : forall degs, NoDup (masks degs).
  Proof. intro degs. apply NoDup_list_prod; [exact Hnd | apply all_shaped_NoDup]. Qed.

  (* ------------------------------------------------------------------ *)
  (* One masked sumcheck *)

  Section OneSumcheck.

    Variable m : nat.
    Variable f : list F -> F.               (* the unmasked summand *)
    Variable pf : list F -> list F.         (* coefficient lists of its round functions *)
    Variable rho : F.
    Variable rs : list F.
    Variable degs : list nat.
    Hypothesis Hrs : length rs = m.
    Hypothesis Hdegs : length degs = m.
    Hypothesis H2 : (one + one) <> zero.
    Hypothesis Hok : okparams degs (params m pf rho rs).
    Hypothesis Hpf : forall j X, (j < m)%nat ->
      peval (pf (firstn j rs)) X = rnd f (firstn j rs) (m - 1 - j) X.

    (* the honest prover: mask sum and round messages *)
    Definition honT (x : F * list (list F)) : F * list (list F) :=
      (p2 (length (snd x)) * fst x + W (snd x), hmsgs m pf rho (fst x) (snd x) rs).

    (* the simulator: coins (G, tails); cl is the claim of the unmasked part *)
    Definition simT (cl : F) (v : F * list (list F)) : F * list (list F) :=
      (fst v, sim_run (snd v) rs (cl + rho * fst v)).

    Theorem sc_complete : forall a0 cs, length cs = m ->
      sc_verify (hmsgs m pf rho a0 cs rs) rs (tsum f [] m + rho * (p2 (length cs) * a0 + W cs))
      = Some (f rs + rho * gmask a0 cs rs).
    Proof.
      intros a0 cs hcs.
      assert (hh : honest (fun x => f x + rho * gmask a0 cs x) [] (hmsgs m pf rho a0 cs rs) rs).
      { apply (honest_of_evals (fun x => f x + rho * gmask a0 cs x) (hmsg m pf rho a0 cs rs) rs m 0%nat);
          [rewrite Hrs; reflexivity |].
        intros i X hi. rewrite Hrs.
        rewrite (@hmsg_eval F zero one add mul sub div opp inv Hf m pf rho a0 cs rs hcs Hrs i X ltac:(lia)).
        rewrite (Hpf i X ltac:(lia)), rnd_lin. reflexivity. }
      pose proof (@sc_verify_honest F zero one add mul sub div opp inv Fdec Hf _ rs _ [] hh) as h.
      assert (e : tsum (fun x => f x + rho * gmask a0 cs x) [] (length rs)
                  = tsum f [] m + rho * (p2 (length cs) * a0 + W cs)).
      { rewrite tsum_lin, Hrs, <-(@mask_tsum F zero one add mul sub div opp inv Hf a0 cs), hcs. reflexivity. }
      rewrite e in h. exact h.
    Qed.

    (* The honest transcript is the simulated transcript on the view. *)
    Theorem sc_honest_sim : forall a0 cs, shaped degs cs ->
      honT (a0, cs) = simT (tsum f [] m) (mview m pf rho rs a0 cs).
    Proof.
      intros a0 cs hsh.
      assert (hcs : length cs = m) by (rewrite (@shaped_length F degs cs hsh); exact Hdegs).
      unfold honT, simT, ZkSumcheck.mview. cbn [fst snd]. f_equal.
      exact (@hmsgs_sim F zero one add mul sub div opp inv Fdec Hf m pf rho a0 cs rs hcs Hrs H2 _ _
               (sc_complete a0 cs hcs)).
    Qed.

    Theorem sc_zk : Permutation (map honT (masks degs)) (map (simT (tsum f [] m)) (masks degs)).
    Proof.
      apply (zk_perm (fun x => mview m pf rho rs (fst x) (snd x)) honT (simT (tsum f [] m)) (masks degs) (masks degs)
               (masks_NoDup degs) (masks_NoDup degs)).
      + intros [a0 cs] hx. apply masks_In in hx. apply masks_In. cbn [fst snd] in *.
        unfold ZkSumcheck.mview. cbn [snd]. apply (@comp_map_shaped F zero add mul degs _ cs Hok hx).
      + intros [a0 cs] [a0' cs'] hx hx' e. apply masks_In in hx. apply masks_In in hx'. cbn [fst snd] in *.
        destruct (@mview_inj F zero one add mul sub div opp inv Hf m pf rho rs degs Hok H2 a0 a0' cs cs' hx hx' e)
          as [-> ->]. reflexivity.
      + intros [G ys] hv. apply masks_In in hv. cbn [snd] in hv.
        destruct (@mview_surj F zero one add mul sub div opp inv Hf m pf rho rs degs Hok H2 G ys hv) as (a0 & cs & hc & e).
        exists (a0, cs). split; [apply masks_In; exact hc | exact e].
      + intros [a0 cs] hx. apply masks_In in hx. cbn [fst snd] in *. apply sc_honest_sim. exact hx.
    Qed.

  End OneSumcheck.

  (* ------------------------------------------------------------------ *)
  (* The sumcheck layer: masked evaluations and three masked sumchecks *)

  Section Layer.

    Variable specs : list (@evspec F).
    Hypothesis Hgood : goodspecs specs.
    Hypothesis H2 : (one + one) <> zero.

    Variables mA mB mC : nat.
    Variables fA fB fC : list F -> list F -> F.           (* unmasked summands, given the mask coefficients *)
    Variables pfA pfB pfC : list F -> list F -> list F.
    Variables rhoA rhoB rhoC : F.
    Variables rsA rsB rsC : list F.
    Variables degsA degsB degsC : list nat.
    Hypothesis HrsA : length rsA = mA.
    Hypothesis HrsB : length rsB = mB.
    Hypothesis HrsC : length rsC = mC.
    Hypothesis HdA : length degsA = mA.
    Hypothesis HdB : length degsB = mB.
    Hypothesis HdC : length degsC = mC.
    Hypothesis HokA : forall avs, okparams degsA (params mA (pfA avs) rhoA rsA).
    Hypothesis HokB : forall avs, okparams degsB (params mB (pfB avs) rhoB rsB).
    Hypothesis HokC : forall avs, okparams degsC (params mC (pfC avs) rhoC rsC).
    Hypothesis HpfA : forall avs j X, (j < mA)%nat ->
      peval (pfA avs (firstn j rsA)) X = rnd (fA avs) (firstn j rsA) (mA - 1 - j) X.
    Hypothesis HpfB : forall avs j X, (j < mB)%nat ->
      peval (pfB avs (firstn j rsB)) X = rnd (fB avs) (firstn j rsB) (mB - 1 - j) X.
    Hypothesis HpfC : forall avs j X, (j < mC)%nat ->
      peval (pfC avs (firstn j rsC)) X = rnd (fC avs) (firstn j rsC) (mC - 1 - j) X.

    (* the verifier's unmasked claims, computed from the evaluations *)
    Variables cA cB cC : list F -> F.
    Hypothesis HcA : forall avs, length avs = length specs -> tsum (fA avs) [] mA = cA (evs specs avs).
    Hypothesis HcB : forall avs, length avs = length specs -> tsum (fB avs) [] mB = cB (evs specs avs).
    Hypothesis HcC : forall avs, length avs = length specs -> tsum (fC avs) [] mC = cC (evs specs avs).

    Local Notation rand := (@rand F).
    Local Notation view := (@view F).
    Local Notation shaped_rand := (@shaped_rand F specs degsA degsB degsC).
    Local Notation Vw := (View specs mA mB mC pfA pfB pfC rhoA rhoB rhoC rsA rsB rsC).

    (* the honest prover of the layer *)
    Definition honL (x : rand) : view :=
      (evs specs (fst x),
       (honT mA (pfA (fst x)) rhoA rsA (fst (snd x)),
        (honT mB (pfB (fst x)) rhoB rsB (fst (snd (snd x))),
         honT mC (pfC (fst x)) rhoC rsC (snd (snd (snd x)))))).

    (* the simulator of the layer: coins are the free values *)
    Definition simL (v : view) : view :=
      (fst v,
       (simT rhoA rsA (cA (fst v)) (fst (snd v)),
        (simT rhoB rsB (cB (fst v)) (fst (snd (snd v))),
         simT rhoC rsC (cC (fst v)) (snd (snd (snd v)))))).

    Theorem layer_honest_sim : forall x, shaped_rand x -> honL x = simL (Vw x).
    Proof.
      intros [avs [[aA csA] [[aB csB] [aC csC]]]] (h0 & hA & hB & hC). cbn [fst snd] in *.
      unfold honL, simL, ZkMix.View. cbn [fst snd].
      rewrite <-(HcA avs h0), <-(HcB avs h0), <-(HcC avs h0).
      rewrite (sc_honest_sim mA (fA avs) (pfA avs) rhoA rsA degsA HrsA HdA H2 (HpfA avs) aA csA hA).
      rewrite (sc_honest_sim mB (fB avs) (pfB avs) rhoB rsB degsB HrsB HdB H2 (HpfB avs) aB csB hB).
      rewrite (sc_honest_sim mC (fC avs) (pfC avs) rhoC rsC degsC HrsC HdC H2 (HpfC avs) aC csC hC).
      reflexivity.
    Qed.

    (* all coins of the right shape *)
    Definition RL : list rand :=
      list_prod (all_lists lf (length specs))
                (list_prod (masks degsA) (list_prod (masks degsB) (masks degsC))).

    Lemma RL_In : forall x : rand, In x RL <-> shaped_rand x.
    Proof.
      intros [avs [mskA [mskB mskC]]]. unfold ZkMix.shaped_rand. cbn [fst snd]. split.
      + intro h. unfold RL in h.
        apply in_prod_iff in h. destruct h as [h0 h]. apply in_prod_iff in h. destruct h as [hA h].
        apply in_prod_iff in h. destruct h as [hB hC].
        apply all_lists_In in h0. apply masks_In in hA. apply masks_In in hB. apply masks_In in hC. tauto.
      + intros (h0 & hA & hB & hC). unfold RL.
        apply in_prod_iff. split.
        - apply all_lists_In. split; [exact h0 | apply Forall_forall; intros; apply Hall].
        - apply in_prod_iff. split; [apply masks_In; exact hA |].
          apply in_prod_iff. split; apply masks_In; assumption.
    Qed.

    Lemma RL_NoDup : NoDup RL.
    Proof.
      unfold RL. apply NoDup_list_prod; [apply all_lists_NoDup; exact Hnd |].
      apply NoDup_list_prod; [apply masks_NoDup |]. apply NoDup_list_prod; apply masks_NoDup.
    Qed.

    Lemma evs_length : forall (sp : list (@evspec F)) avs, length avs = length sp -> length (evs sp avs) = length sp.
    Proof.
      induction sp as [| s sp ih]; intros avs h; destruct avs as [| a0 avs]; cbn in h; try lia; [reflexivity |].
      cbn. rewrite ih by lia. reflexivity.
    Qed.

    (* Theorem 5.3 for the sumcheck layer: the honest transcripts over all
       prover coins and the simulated transcripts over all simulator coins
       are the same multiset. *)
    Theorem layer_zk : Permutation (map honL RL) (map simL RL).
    Proof.
      apply (zk_perm Vw honL simL RL RL RL_NoDup RL_NoDup).
      + intros x hx. apply RL_In in hx. apply RL_In.
        destruct x as [avs [[aA csA] [[aB csB] [aC csC]]]]. destruct hx as (h0 & hA & hB & hC). cbn [fst snd] in *.
        unfold ZkMix.shaped_rand, ZkMix.View, ZkSumcheck.mview. cbn [fst snd]. repeat split.
        - apply evs_length. exact h0.
        - apply (@comp_map_shaped F zero add mul degsA _ csA (HokA avs) hA).
        - apply (@comp_map_shaped F zero add mul degsB _ csB (HokB avs) hB).
        - apply (@comp_map_shaped F zero add mul degsC _ csC (HokC avs) hC).
      + intros x x' hx hx' e. apply RL_In in hx. apply RL_In in hx'.
        exact (@mix_view_inj F zero one add mul sub div opp inv Hf specs Hgood H2 mA mB mC pfA pfB pfC
                 rhoA rhoB rhoC rsA rsB rsC degsA degsB degsC HokA HokB HokC x x' hx hx' e).
      + intros v hv. apply RL_In in hv.
        destruct (@mix_view_surj F zero one add mul sub div opp inv Hf specs Hgood H2 mA mB mC pfA pfB pfC
                    rhoA rhoB rhoC rsA rsB rsC degsA degsB degsC HokA HokB HokC v hv) as (x & hx & e).
        exists x. split; [apply RL_In; exact hx | exact e].
      + intros x hx. apply RL_In in hx. apply layer_honest_sim. exact hx.
    Qed.

    (* the pieces of layer_zk, for the composition with the opening (zk_join) *)
    Theorem layer_parts : NoDup RL
      /\ (forall x, In x RL -> In (Vw x) RL)
      /\ (forall x x', In x RL -> In x' RL -> Vw x = Vw x' -> x = x')
      /\ (forall v, In v RL -> exists x, In x RL /\ Vw x = v)
      /\ (forall x, In x RL -> honL x = simL (Vw x)).
    Proof.
      split; [exact RL_NoDup |]. split; [| split; [| split]].
      + intros x hx. apply RL_In in hx. apply RL_In.
        destruct x as [avs [[aA csA] [[aB csB] [aC csC]]]]. destruct hx as (h0 & hA & hB & hC). cbn [fst snd] in *.
        unfold ZkMix.shaped_rand, ZkMix.View, ZkSumcheck.mview. cbn [fst snd]. repeat split.
        - apply evs_length. exact h0.
        - apply (@comp_map_shaped F zero add mul degsA _ csA (HokA avs) hA).
        - apply (@comp_map_shaped F zero add mul degsB _ csB (HokB avs) hB).
        - apply (@comp_map_shaped F zero add mul degsC _ csC (HokC avs) hC).
      + intros x x' hx hx' e. apply RL_In in hx. apply RL_In in hx'.
        exact (@mix_view_inj F zero one add mul sub div opp inv Hf specs Hgood H2 mA mB mC pfA pfB pfC
                 rhoA rhoB rhoC rsA rsB rsC degsA degsB degsC HokA HokB HokC x x' hx hx' e).
      + intros v hv. apply RL_In in hv.
        destruct (@mix_view_surj F zero one add mul sub div opp inv Hf specs Hgood H2 mA mB mC pfA pfB pfC
                    rhoA rhoB rhoC rsA rsB rsC degsA degsB degsC HokA HokB HokC v hv) as (x & hx & e).
        exists x. split; [apply RL_In; exact hx | exact e].
      + intros x hx. apply RL_In in hx. apply layer_honest_sim. exact hx.
    Qed.

  End Layer.

  (* ------------------------------------------------------------------ *)
  (* A layer with two masked sumchecks (the decryption proof) *)

  Section Layer2.

    Variable specs : list (@evspec F).
    Hypothesis Hgood : goodspecs specs.
    Hypothesis H2 : (one + one) <> zero.

    Variables mG mT : nat.
    Variables fG fT : list F -> list F -> F.
    Variables pfG pfT : list F -> list F -> list F.
    Variables rhoG rhoT : F.
    Variables rsG rsT : list F.
    Variables degsG degsT : list nat.
    Hypothesis HrsG : length rsG = mG.
    Hypothesis HrsT : length rsT = mT.
    Hypothesis HdG : length degsG = mG.
    Hypothesis HdT : length degsT = mT.
    Hypothesis HokG : forall avs, okparams degsG (params mG (pfG avs) rhoG rsG).
    Hypothesis HokT : forall avs, okparams degsT (params mT (pfT avs) rhoT rsT).
    Hypothesis HpfG : forall avs j X, (j < mG)%nat ->
      peval (pfG avs (firstn j rsG)) X = rnd (fG avs) (firstn j rsG) (mG - 1 - j) X.
    Hypothesis HpfT : forall avs j X, (j < mT)%nat ->
      peval (pfT avs (firstn j rsT)) X = rnd (fT avs) (firstn j rsT) (mT - 1 - j) X.

    Variables cG cT : list F -> F.
    Hypothesis HcG : forall avs, length avs = length specs -> tsum (fG avs) [] mG = cG (evs specs avs).
    Hypothesis HcT : forall avs, length avs = length specs -> tsum (fT avs) [] mT = cT (evs specs avs).

    Definition rand2 : Type := (list F * ((F * list (list F)) * (F * list (list F))))%type.
    Definition view2 : Type := (list F * ((F * list (list F)) * (F * list (list F))))%type.

    Definition shaped_rand2 (x : rand2) : Prop :=
      length (fst x) = length specs /\ shaped degsG (snd (fst (snd x))) /\ shaped degsT (snd (snd (snd x))).

    (* the free values of an honest run *)
    Definition Vw2 (x : rand2) : view2 :=
      (evs specs (fst x),
       (mview mG (pfG (fst x)) rhoG rsG (fst (fst (snd x))) (snd (fst (snd x))),
        mview mT (pfT (fst x)) rhoT rsT (fst (snd (snd x))) (snd (snd (snd x))))).

    Definition honL2 (x : rand2) : view2 :=
      (evs specs (fst x),
       (honT mG (pfG (fst x)) rhoG rsG (fst (snd x)),
        honT mT (pfT (fst x)) rhoT rsT (snd (snd x)))).

    Definition simL2 (v : view2) : view2 :=
      (fst v,
       (simT rhoG rsG (cG (fst v)) (fst (snd v)),
        simT rhoT rsT (cT (fst v)) (snd (snd v)))).

    Theorem layer2_honest_sim : forall x, shaped_rand2 x -> honL2 x = simL2 (Vw2 x).
    Proof.
      intros [avs [[aG csG] [aT csT]]] (h0 & hG & hT). cbn [fst snd] in *.
      unfold honL2, simL2, Vw2. cbn [fst snd].
      rewrite <-(HcG avs h0), <-(HcT avs h0).
      rewrite (sc_honest_sim mG (fG avs) (pfG avs) rhoG rsG degsG HrsG HdG H2 (HpfG avs) aG csG hG).
      rewrite (sc_honest_sim mT (fT avs) (pfT avs) rhoT rsT degsT HrsT HdT H2 (HpfT avs) aT csT hT).
      reflexivity.
    Qed.

    Definition RL2 : list rand2 :=
      list_prod (all_lists lf (length specs)) (list_prod (masks degsG) (masks degsT)).

    Lemma RL2_In : forall x : rand2, In x RL2 <-> shaped_rand2 x.
    Proof.
      intros [avs [mskG mskT]]. unfold shaped_rand2. cbn [fst snd]. unfold RL2. split.
      + intro h. apply in_prod_iff in h. destruct h as [h0 h]. apply in_prod_iff in h. destruct h as [hG hT].
        apply all_lists_In in h0. apply masks_In in hG. apply masks_In in hT. tauto.
      + intros (h0 & hG & hT). apply in_prod_iff. split.
        - apply all_lists_In. split; [exact h0 | apply Forall_forall; intros; apply Hall].
        - apply in_prod_iff. split; apply masks_In; assumption.
    Qed.

    Lemma RL2_NoDup : NoDup RL2.
    Proof.
      unfold RL2. apply NoDup_list_prod; [apply all_lists_NoDup; exact Hnd |].
      apply NoDup_list_prod; apply masks_NoDup.
    Qed.

    Lemma evs_length2 : forall (sp : list (@evspec F)) avs, length avs = length sp -> length (evs sp avs) = length sp.
    Proof.
      induction sp as [| s0 sp ih]; intros avs h; destruct avs as [| a0 avs]; cbn in h; try lia; [reflexivity |].
      cbn. rewrite ih by lia. reflexivity.
    Qed.

    Lemma Vw2_shaped : forall x, shaped_rand2 x -> shaped_rand2 (Vw2 x).
    Proof.
      intros [avs [[aG csG] [aT csT]]] (h0 & hG & hT). cbn [fst snd] in *.
      unfold shaped_rand2, Vw2, ZkSumcheck.mview. cbn [fst snd]. repeat split.
      - apply evs_length2. exact h0.
      - apply (@comp_map_shaped F zero add mul degsG _ csG (HokG avs) hG).
      - apply (@comp_map_shaped F zero add mul degsT _ csT (HokT avs) hT).
    Qed.

    Lemma Vw2_inj : forall x x', shaped_rand2 x -> shaped_rand2 x' -> Vw2 x = Vw2 x' -> x = x'.
    Proof.
      intros [avs [[aG cG'] [aT cT']]] [avs' [[aG' cG''] [aT' cT'']]] (h0 & hG & hT) (h0' & hG' & hT') e.
      cbn [fst snd] in *. unfold Vw2 in e. cbn [fst snd] in e. inversion e as [[e0 eG eT]]. clear e.
      assert (eav : avs = avs') by (apply (@evs_inj F zero one add mul sub div opp inv Hf specs avs avs' Hgood h0 h0' e0)).
      subst avs'.
      destruct (@mview_inj F zero one add mul sub div opp inv Hf mG (pfG avs) rhoG rsG degsG (HokG avs) H2
                  aG aG' cG' cG'' hG hG' ltac:(unfold ZkSumcheck.mview; f_equal; assumption)) as [<- <-].
      destruct (@mview_inj F zero one add mul sub div opp inv Hf mT (pfT avs) rhoT rsT degsT (HokT avs) H2
                  aT aT' cT' cT'' hT hT' ltac:(unfold ZkSumcheck.mview; f_equal; assumption)) as [<- <-].
      reflexivity.
    Qed.

    Lemma Vw2_surj : forall v, shaped_rand2 v -> exists x, shaped_rand2 x /\ Vw2 x = v.
    Proof.
      intros [ys [[GG tG] [GT tT]]] (h0 & hG & hT). cbn [fst snd] in *.
      destruct (@evs_surj F zero one add mul sub div opp inv Hf specs ys Hgood h0) as (avs & hlen & e0).
      destruct (@mview_surj F zero one add mul sub div opp inv Hf mG (pfG avs) rhoG rsG degsG (HokG avs) H2 GG tG hG)
        as (aG & csG & hcG & eG).
      destruct (@mview_surj F zero one add mul sub div opp inv Hf mT (pfT avs) rhoT rsT degsT (HokT avs) H2 GT tT hT)
        as (aT & csT & hcT & eT).
      exists (avs, ((aG, csG), (aT, csT))). split.
      + unfold shaped_rand2. cbn [fst snd]. tauto.
      + unfold Vw2. cbn [fst snd]. rewrite e0, eG, eT. reflexivity.
    Qed.

    Theorem layer2_parts : NoDup RL2
      /\ (forall x, In x RL2 -> In (Vw2 x) RL2)
      /\ (forall x x', In x RL2 -> In x' RL2 -> Vw2 x = Vw2 x' -> x = x')
      /\ (forall v, In v RL2 -> exists x, In x RL2 /\ Vw2 x = v)
      /\ (forall x, In x RL2 -> honL2 x = simL2 (Vw2 x)).
    Proof.
      split; [exact RL2_NoDup |]. split; [| split; [| split]].
      + intros x hx. apply RL2_In. apply Vw2_shaped. apply RL2_In. exact hx.
      + intros x x' hx hx' e. apply RL2_In in hx. apply RL2_In in hx'. exact (Vw2_inj x x' hx hx' e).
      + intros v hv. apply RL2_In in hv. destruct (Vw2_surj v hv) as (x & hx & e).
        exists x. split; [apply RL2_In; exact hx | exact e].
      + intros x hx. apply layer2_honest_sim. apply RL2_In. exact hx.
    Qed.

    (* Theorem 5.3 for a layer with two masked sumchecks *)
    Theorem layer2_zk : Permutation (map honL2 RL2) (map simL2 RL2).
    Proof.
      destruct layer2_parts as (n & i & j & sj & e).
      apply (zk_perm Vw2 honL2 simL2 RL2 RL2 n n i j sj e).
    Qed.

  End Layer2.

End ZkTranscript.
