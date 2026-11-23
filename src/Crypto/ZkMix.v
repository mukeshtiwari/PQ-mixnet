(* Zero knowledge of the sumcheck layer of the shuffle proof (paper,
   Theorem 5.3, steps (1) and (2)).

   What the verifier sees before the opening, apart from its own
   challenges, is determined by the following "free values":

     - the masked evaluations sent by the prover (U, Uhat, s, H and the
       three w_k*(r_z)): one value per masked table, evs specs avs, where
       a spec is (number of variables, table, point) and avs are the mask
       coefficients a_T;
     - for each of the three sumchecks, the mask sum G and the
       non-constant coefficients of the round messages (mview).

   The round messages themselves are sim_run of the tails (hmsgs_sim), and
   the claims are computed by the verifier from the free values.

   Theorems mix_view_inj and mix_view_surj: for points with Z <> 0,
   rho_A, rho_B, rho_C <> 0 and 2 <> 0 (through okparams), the map

     (avs, mask_A, mask_B, mask_C)  |->  free values

   is a bijection between the prover's randomness of the right shape and
   the free values of the right shape. The unmasked parts pfA, pfB, pfC of
   the round messages may depend on the witness, the challenges and the
   mask coefficients avs in any way; they do not appear in the conclusion.
   So uniform randomness gives uniform free values, whatever the witness:
   a simulator draws the free values uniformly and computes the messages.

   Not covered here: the opening (steps (4) to (6) of the proof of
   Theorem 5.3), whose ingredients are shift_list_inj/surj and rs_hiding. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask MaskedExt ZkBlocks ZkSumcheck.
Import ListNotations.

Section ZkMix.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation mview := (@mview F zero one add mul).
  Local Notation params := (@params F one add mul).
  Local Notation okparams := (@okparams F zero).

  (* masked evaluations of several tables *)
  Definition evspec : Type := (nat * (list F -> F) * list F)%type.

  Definition ev (s : evspec) (a : F) : F := mstar (fst (fst s)) (snd (fst s)) a (snd s).

  Fixpoint evs (specs : list evspec) (avs : list F) : list F :=
    match specs, avs with
    | s :: ss, a :: as' => ev s a :: evs ss as'
    | _, _ => []
    end.

  Definition goodspecs (specs : list evspec) : Prop := Forall (fun s => Zp (snd s) <> zero) specs.

  Theorem evs_inj : forall specs avs avs', goodspecs specs ->
    length avs = length specs -> length avs' = length specs ->
    evs specs avs = evs specs avs' -> avs = avs'.
  Proof.
    induction specs as [| s ss ih]; intros avs avs' hg hl hl' e;
      destruct avs as [| a as1], avs' as [| a' as1']; cbn in hl, hl'; try lia; [reflexivity |].
    inversion hg as [| ? ? hs hg']; subst. cbn [evs] in e. inversion e as [[e1 e2]]. f_equal.
    + exact (@mstar_inj F zero one add mul sub div opp inv Hf _ _ _ a a' hs e1).
    + apply (ih as1 as1' hg'); [lia | lia | exact e2].
  Qed.

  Theorem evs_surj : forall specs ys, goodspecs specs -> length ys = length specs ->
    exists avs, length avs = length specs /\ evs specs avs = ys.
  Proof.
    induction specs as [| s ss ih]; intros ys hg hl; destruct ys as [| y ys']; cbn in hl; try lia.
    + exists []; split; reflexivity.
    + inversion hg as [| ? ? hs hg']; subst.
      destruct (ih ys' hg' ltac:(lia)) as (avs & hlen & e).
      exists (mul (sub y (mle (fst (fst s)) (snd (fst s)) (snd s))) (inv (Zp (snd s))) :: avs).
      split; [cbn; lia |]. cbn [evs]. rewrite e. f_equal.
      exact (@mstar_surj F zero one add mul sub div opp inv Hf _ _ _ y hs).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The three masked sumchecks together with the evaluations *)

  Variable specs : list evspec.
  Hypothesis Hgood : goodspecs specs.
  Hypothesis H2 : add one one <> zero.

  Variables mA mB mC : nat.
  Variables pfA pfB pfC : list F -> list F -> list F.   (* may depend on the mask coefficients avs *)
  Variables rhoA rhoB rhoC : F.
  Variables rsA rsB rsC : list F.
  Variables degsA degsB degsC : list nat.
  Hypothesis HdA : length degsA = mA.
  Hypothesis HdB : length degsB = mB.
  Hypothesis HdC : length degsC = mC.
  Hypothesis HokA : forall avs, okparams degsA (params mA (pfA avs) rhoA rsA).
  Hypothesis HokB : forall avs, okparams degsB (params mB (pfB avs) rhoB rsB).
  Hypothesis HokC : forall avs, okparams degsC (params mC (pfC avs) rhoC rsC).

  Definition mask : Type := (F * list (list F))%type.
  Definition rand : Type := (list F * (mask * (mask * mask)))%type.
  Definition view : Type := (list F * ((F * list (list F)) * ((F * list (list F)) * (F * list (list F)))))%type.

  Definition shaped_rand (x : rand) : Prop :=
    length (fst x) = length specs /\
    shaped degsA (snd (fst (snd x))) /\ shaped degsB (snd (fst (snd (snd x)))) /\
    shaped degsC (snd (snd (snd (snd x)))).

  Definition shaped_view (v : view) : Prop :=
    length (fst v) = length specs /\
    shaped degsA (snd (fst (snd v))) /\ shaped degsB (snd (fst (snd (snd v)))) /\
    shaped degsC (snd (snd (snd (snd v)))).

  (* the free values of an honest run *)
  Definition View (x : rand) : view :=
    (evs specs (fst x),
     (mview mA (pfA (fst x)) rhoA rsA (fst (fst (snd x))) (snd (fst (snd x))),
      (mview mB (pfB (fst x)) rhoB rsB (fst (fst (snd (snd x)))) (snd (fst (snd (snd x)))),
       mview mC (pfC (fst x)) rhoC rsC (fst (snd (snd (snd x)))) (snd (snd (snd (snd x))))))).

  Theorem mix_view_inj : forall x x', shaped_rand x -> shaped_rand x' -> View x = View x' -> x = x'.
  Proof.
    intros [avs [[aA cA] [[aB cB] [aC cC]]]] [avs' [[aA' cA'] [[aB' cB'] [aC' cC']]]]
           (h0 & hA & hB & hC) (h0' & hA' & hB' & hC') e.
    cbn [fst snd] in *. unfold View in e. cbn [fst snd] in e.
    inversion e as [[e0 eA eB eC]]. clear e.
    assert (eav : avs = avs') by (apply (evs_inj specs avs avs' Hgood h0 h0' e0)).
    subst avs'.
    destruct (@mview_inj F zero one add mul sub div opp inv Hf mA (pfA avs) rhoA rsA degsA (HokA avs) H2
                aA aA' cA cA' hA hA' ltac:(unfold ZkSumcheck.mview; f_equal; assumption)) as [<- <-].
    destruct (@mview_inj F zero one add mul sub div opp inv Hf mB (pfB avs) rhoB rsB degsB (HokB avs) H2
                aB aB' cB cB' hB hB' ltac:(unfold ZkSumcheck.mview; f_equal; assumption)) as [<- <-].
    destruct (@mview_inj F zero one add mul sub div opp inv Hf mC (pfC avs) rhoC rsC degsC (HokC avs) H2
                aC aC' cC cC' hC hC' ltac:(unfold ZkSumcheck.mview; f_equal; assumption)) as [<- <-].
    reflexivity.
  Qed.

  Theorem mix_view_surj : forall v, shaped_view v -> exists x, shaped_rand x /\ View x = v.
  Proof.
    intros [ys [[GA tA] [[GB tB] [GC tC]]]] (h0 & hA & hB & hC). cbn [fst snd] in *.
    destruct (evs_surj specs ys Hgood h0) as (avs & hlen & e0).
    destruct (@mview_surj F zero one add mul sub div opp inv Hf mA (pfA avs) rhoA rsA degsA (HokA avs) H2 GA tA hA)
      as (aA & cA & hcA & eA).
    destruct (@mview_surj F zero one add mul sub div opp inv Hf mB (pfB avs) rhoB rsB degsB (HokB avs) H2 GB tB hB)
      as (aB & cB & hcB & eB).
    destruct (@mview_surj F zero one add mul sub div opp inv Hf mC (pfC avs) rhoC rsC degsC (HokC avs) H2 GC tC hC)
      as (aC & cC & hcC & eC).
    exists (avs, ((aA, cA), ((aB, cB), (aC, cC)))). split.
    + unfold shaped_rand. cbn [fst snd]. tauto.
    + unfold View. cbn [fst snd]. rewrite e0, eA, eB, eC. reflexivity.
  Qed.

End ZkMix.
