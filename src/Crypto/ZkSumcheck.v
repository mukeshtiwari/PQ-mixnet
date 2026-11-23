(* Zero knowledge of one masked sumcheck (paper, Section 2.3 and step (2)
   of the proof of Theorem 5.3).

   The summand is f + rho * gmask a0 cs. The honest prover knows, for every
   prefix of challenges, a coefficient list pf pre for the round function
   of f; pf may depend on anything except the mask (a0, cs). Its message in
   the round of variable j is

       hmsg j = pf pre + rho * (round polynomial of the mask)

   with the round polynomial of the mask from mask_round_poly.

   - hmsg_eval: hmsg j evaluates to the round function of f plus rho times
     that of the mask, so it is the honest message.
   - hmsgs_tails: the non-constant coefficients of the messages are
       comp_map params cs,   params_j = (tl (pf pre_j), rho * 2^(m-1-j)),
     that is t_j + s_j * c_j componentwise: they depend on the mask only
     through the coefficient list of the same variable.
   - comp_map_inj, comp_map_surj: for s_j <> 0 this is a bijection between
     masks of shape degs and tails of shape degs.

   With sim_run_complete (the messages are determined by the claim and the
   tails) and the bijection a0 |-> G, this is the statement that the
   messages of a masked sumcheck are uniform among those consistent with
   the claim. Hypotheses: rho <> 0 and 2 <> 0. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask MaskedExt ZkBlocks.
Import ListNotations.

Section ZkSumcheck.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation peval := (@eval F zero add mul).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation gtail := (@gtail F zero add mul).
  Local Notation W := (@W F zero one add mul).
  Local Notation p2 := (@p2 F one add mul).
  Local Notation rnd := (@rnd F zero one add).

  (* ------------------------------------------------------------------ *)
  (* Componentwise affine maps on lists of coefficient lists *)

  Definition shaped (degs : list nat) (ls : list (list F)) : Prop :=
    Forall2 (fun d l => length l = d) degs ls.

  Definition okparams (degs : list nat) (params : list (list F * F)) : Prop :=
    Forall2 (fun d ts => (length (fst ts) <= d)%nat /\ snd ts <> zero) degs params.

  Fixpoint comp_map (params : list (list F * F)) (cs : list (list F)) : list (list F) :=
    match params, cs with
    | ts :: ps, c :: cs' => padd (fst ts) (pscale (snd ts) c) :: comp_map ps cs'
    | _, _ => []
    end.

  Theorem comp_map_shaped : forall degs params cs, okparams degs params -> shaped degs cs ->
    shaped degs (comp_map params cs).
  Proof.
    intros degs params cs hp; revert cs; induction hp as [| d ts degs params [hl hs] hp ih]; intros cs hc.
    + inversion hc; subst. constructor.
    + inversion hc as [| ? c ? cs' hcl hc']; subst. cbn [comp_map]. constructor; [| apply ih; exact hc'].
      rewrite (@length_padd F add), (@length_pscale F mul). lia.
  Qed.

  Theorem comp_map_inj : forall degs params cs cs', okparams degs params ->
    shaped degs cs -> shaped degs cs' -> comp_map params cs = comp_map params cs' -> cs = cs'.
  Proof.
    intros degs params cs cs' hp; revert cs cs'; induction hp as [| d ts degs params [hl hs] hp ih];
      intros cs cs' hc hc' e.
    + inversion hc; inversion hc'; subst. reflexivity.
    + inversion hc as [| ? c ? cs1 hcl hc1]; subst. inversion hc' as [| ? c' ? cs1' hcl' hc1']; subst.
      cbn [comp_map] in e. inversion e as [[e1 e2]]. f_equal.
      - apply (@affine_list_inj F zero one add mul sub div opp inv Hf (snd ts) (fst ts) c c' hs); [lia | exact e1].
      - exact (ih cs1 cs1' hc1 hc1' e2).
  Qed.

  Theorem comp_map_surj : forall degs params ys, okparams degs params -> shaped degs ys ->
    exists cs, shaped degs cs /\ comp_map params cs = ys.
  Proof.
    intros degs params ys hp; revert ys; induction hp as [| d ts degs params [hl hs] hp ih]; intros ys hy.
    + inversion hy; subst. exists []; split; [constructor | reflexivity].
    + inversion hy as [| ? y ? ys' hyl hy']; subst.
      destruct (ih ys' hy') as (cs & hcs & e).
      destruct (@affine_list_surj F zero one add mul sub div opp inv Hf (snd ts) (fst ts) y hs hl) as (c & hcl & ec).
      exists (c :: cs); split; [constructor; assumption |]. cbn [comp_map]. rewrite ec, e. reflexivity.
  Qed.

  Lemma comp_map_map : forall {A : Type} (Pf : A -> list F * F) (Cf : A -> list F) (l : list A),
    comp_map (map Pf l) (map Cf l) = map (fun j => padd (fst (Pf j)) (pscale (snd (Pf j)) (Cf j))) l.
  Proof. intros A Pf Cf; induction l as [| a l ih]; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Lemma list_map_nth : forall (cs : list (list F)), cs = map (fun j => nth j cs []) (seq 0 (length cs)).
  Proof.
    intro cs. apply (nth_ext _ _ [] []); [rewrite length_map, length_seq; reflexivity |].
    intros i hi.
    rewrite (nth_indep (map (fun j => nth j cs []) (seq 0 (length cs))) [] (nth 0 cs []))
      by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth (fun j => nth j cs []) (seq 0 (length cs)) 0%nat i), seq_nth by exact hi. reflexivity.
  Qed.

  Lemma split_at : forall (cs : list (list F)) (j : nat), (j < length cs)%nat ->
    cs = firstn j cs ++ nth j cs [] :: skipn (S j) cs.
  Proof.
    induction cs as [| c cs ih]; intros j hj; [cbn in hj; lia |].
    destruct j as [| j]; [reflexivity |]. cbn [firstn nth skipn app]. f_equal. apply ih. cbn in hj. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The honest masked prover *)

  Variable m : nat.
  Variable pf : list F -> list F.
  Variables rho a0 : F.
  Variable cs : list (list F).
  Variable rs : list F.
  Hypothesis Hcs : length cs = m.
  Hypothesis Hrs : length rs = m.

  Definition hmsg (j : nat) : list F :=
    padd (pf (firstn j rs))
         (pscale rho ((p2 (m - 1 - j) * (a0 + gtail (firstn j cs) (firstn j rs)) + W (skipn (S j) cs))
                      :: pscale (p2 (m - 1 - j)) (nth j cs []))).

  Definition hmsgs : list (list F) := map hmsg (seq 0 m).

  Definition params : list (list F * F) :=
    map (fun j => (tl (pf (firstn j rs)), rho * p2 (m - 1 - j))) (seq 0 m).

  Theorem hmsg_eval : forall j X, (j < m)%nat ->
    peval (hmsg j) X = peval (pf (firstn j rs)) X + rho * rnd (gmask a0 cs) (firstn j rs) (m - 1 - j) X.
  Proof.
    intros j X hj. unfold hmsg.
    rewrite (@eval_padd F zero one add mul sub div opp inv Hf), (@eval_pscale F zero one add mul sub div opp inv Hf).
    f_equal. f_equal.
    assert (hsk : length (skipn (S j) cs) = (m - 1 - j)%nat) by (rewrite length_skipn; lia).
    rewrite <-hsk at 1 2.
    rewrite (@mask_round_poly F zero one add mul sub div opp inv Hf a0 (firstn j cs) (nth j cs []) (skipn (S j) cs)
               (firstn j rs) X) by (rewrite !length_firstn; lia).
    rewrite <-(split_at cs j ltac:(lia)), hsk. reflexivity.
  Qed.

  Theorem hmsgs_tails : map (@tl F) hmsgs = comp_map params cs.
  Proof.
    unfold hmsgs, params. rewrite map_map.
    assert (ecs : map (fun j => nth j cs []) (seq 0 m) = cs) by (rewrite <-Hcs; symmetry; apply list_map_nth).
    replace (comp_map (map (fun j => (tl (pf (firstn j rs)), rho * p2 (m - 1 - j))) (seq 0 m)) cs)
      with (comp_map (map (fun j => (tl (pf (firstn j rs)), rho * p2 (m - 1 - j))) (seq 0 m))
                     (map (fun j => nth j cs []) (seq 0 m))) by (rewrite ecs; reflexivity).
    rewrite (comp_map_map (fun j => (tl (pf (firstn j rs)), rho * p2 (m - 1 - j))) (fun j => nth j cs []) (seq 0 m)).
    apply map_ext. intro j. cbn [fst snd]. unfold hmsg.
    apply (@masked_tail F zero one add mul sub div opp inv Hf).
  Qed.

  (* the parameters are admissible when the unmasked part respects the
     round degrees, rho <> 0 and 2 <> 0 *)
  Theorem params_ok : forall (deg : nat -> nat),
    rho <> zero -> (one + one) <> zero ->
    (forall pre, (length (pf pre) <= S (deg (length pre)))%nat) ->
    okparams (map deg (seq 0 m)) params.
  Proof.
    intros deg hrho h2 hpf. unfold okparams, params.
    assert (hgen : forall l : list nat, (forall j, In j l -> (j < m)%nat) ->
              Forall2 (fun d ts => (length (fst ts) <= d)%nat /\ snd ts <> zero)
                      (map deg l) (map (fun j => (tl (pf (firstn j rs)), rho * p2 (m - 1 - j))) l)).
    { induction l as [| j l ih]; intro hl; cbn [map]; constructor.
      + cbn [fst snd]. split.
        - specialize (hpf (firstn j rs)). rewrite length_firstn in hpf.
          specialize (hl j (or_introl eq_refl)).
          replace (Nat.min j (length rs)) with j in hpf by lia.
          destruct (pf (firstn j rs)); cbn in *; lia.
        - apply (@mul_nonzero F zero one add mul sub div opp inv Hf); [exact hrho |].
          apply (@p2_nonzero F zero one add mul sub div opp inv Hf). exact h2.
      + apply ih. intros j' hj'. apply hl. right. exact hj'. }
    apply hgen. intros j hj. apply in_seq in hj. lia.
  Qed.

  (* The messages are a function of the claim, the challenges and the tails. *)
  Theorem hmsgs_sim : (one + one) <> zero -> forall claim c : F,
    @sc_verify F zero one add mul Fdec hmsgs rs claim = Some c ->
    hmsgs = @sim_run F zero one add mul sub inv (comp_map params cs) rs claim.
  Proof.
    intros h2 claim c hv. rewrite <-hmsgs_tails.
    apply (@sim_run_complete F zero one add mul sub div opp inv Fdec Hf h2 hmsgs rs claim c); [| exact hv].
    unfold hmsgs. apply Forall_forall. intros p hp. apply in_map_iff in hp. destruct hp as (j & <- & _).
    unfold hmsg. intro e. apply (f_equal (@length F)) in e.
    rewrite (@length_padd F add), (@length_pscale F mul) in e. cbn in e. lia.
  Qed.

  (* The view of the masked sumcheck: the mask sum and the tails. *)
  Definition mview (a : F) (c : list (list F)) : F * list (list F) :=
    (p2 (length c) * a + W c, comp_map params c).

End ZkSumcheck.

Section ZkSumcheckBij.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field2 : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation W := (@W F zero one add mul).
  Local Notation p2 := (@p2 F one add mul).
  Local Notation mview := (@mview F zero one add mul).
  Local Notation params := (@params F one add mul).
  Local Notation okparams := (@okparams F zero).

  Lemma shaped_length : forall degs (ls : list (list F)), shaped degs ls -> length ls = length degs.
  Proof. intros degs ls h. induction h; cbn; [reflexivity | rewrite IHh; reflexivity]. Qed.

  Variable m : nat.
  Variable pf : list F -> list F.
  Variable rho : F.
  Variable rs : list F.
  Variable degs : list nat.
  Hypothesis Hdegs : length degs = m.
  Hypothesis Hok : okparams degs (params m pf rho rs).
  Hypothesis H2 : (one + one) <> zero.

  (* (a0, cs) |-> (G, tails) is a bijection between masks of shape degs
     and views of shape degs. *)
  Theorem mview_inj : forall a a' c c', shaped degs c -> shaped degs c' ->
    mview m pf rho rs a c = mview m pf rho rs a' c' -> a = a' /\ c = c'.
  Proof.
    intros a a' c c' hc hc' e. unfold ZkSumcheck.mview in e. inversion e as [[e1 e2]].
    pose proof (@comp_map_inj F zero one add mul sub div opp inv Hf degs _ c c' Hok hc hc' e2) as ec.
    subst c'. split; [| reflexivity].
    assert (hp : p2 (length c) <> zero) by (apply (@p2_nonzero F zero one add mul sub div opp inv Hf); exact H2).
    apply (@affine_inj F zero one add mul sub div opp inv Hf (p2 (length c)) (W c) a a' hp).
    transitivity (p2 (length c) * a + W c); [field |]. rewrite e1. field.
  Qed.

  Theorem mview_surj : forall (G : F) (ys : list (list F)), shaped degs ys ->
    exists a c, shaped degs c /\ mview m pf rho rs a c = (G, ys).
  Proof.
    intros G ys hy.
    destruct (@comp_map_surj F zero one add mul sub div opp inv Hf degs _ ys Hok hy) as (c & hc & e).
    assert (hp : p2 (length c) <> zero) by (apply (@p2_nonzero F zero one add mul sub div opp inv Hf); exact H2).
    exists ((G - W c) * inv (p2 (length c))), c. split; [exact hc |].
    unfold ZkSumcheck.mview. rewrite e. f_equal. field. exact hp.
  Qed.

End ZkSumcheckBij.
