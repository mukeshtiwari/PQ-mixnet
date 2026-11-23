(* Soundness of the shortness part of the shuffle proof (sumcheck C with
   its two challenge messages), against an adaptive prover.

   Everything that precedes the challenge (tz, kC, rhoC) is collected in a
   value p of an arbitrary finite type P: the masks, the mask sum G_C and
   the prover's strategy may depend on p in any way. The witness tables
   W1, W2, W3 are fixed before.

   Acceptance (AccC). The verifier runs sumcheck C from the claim
   rhoC * G_C, receives wz_k, and the claims 5, 6, 7 and 9 of the paper
   hold for the committed tables:
       wz_k = wstar_k(rz),    final claim = f_C(wz) + rhoC * g_C(rz).

   Theorem soundC. If some entry of W1, W2, W3 on the cube is not in
   {-1, 0, 1}, the challenges (p, (tz, kC), rz) for which the verifier
   accepts number at most

       ((m + 1) |F|^(m+3) * |F|^m  +  (4 (m - 1) + 7) |F|^(m-1) * |F|^(m+4)) * |P|,

   that is a fraction ((m + 1) + (4m + 3)) / |F| of all challenges: the
   two budget lines of Theorem 5.2 for sumcheck C. (The sum of round
   degrees appears as dsum (degC m) 0 m.) *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask SumcheckSound PolyFun MaskedExt CubeIndex EqBatch Bgv MixSummands MixIdentities.
Import ListNotations.

Section MixSoundC.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation cube := (@cube F zero one).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation cube3 := (@cube3 F mul sub).
  Local Notation tern := (@tern F zero one opp).
  Local Notation sc_run := (@sc_run F zero one add mul Fdec).
  Local Notation gC := (@gC F zero one add mul sub).
  Local Notation wstar := (@wstar1 F zero one add mul sub).
  Local Notation TC1 := (@TC1 F mul sub).
  Local Notation TC2 := (@TC2 F mul sub).
  Local Notation TC3 := (@TC3 F mul sub).
  Local Notation GtrueC := (@GtrueC F zero one add mul).
  Local Notation coefs := (@coefs F zero one add mul sub).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.

  Definition kk (l : list F) (i : nat) : F := nth i l zero.

  Lemma list4 : forall l : list F, length l = 4%nat -> l = [kk l 0; kk l 1; kk l 2; kk l 3].
  Proof.
    intros l h. destruct l as [| a [| b [| c [| d [| e l]]]]]; cbn in h; try lia. reflexivity.
  Qed.

  Variable m : nat.
  Hypothesis Hm : (1 <= m)%nat.
  Variables W1 W2 W3 : list F -> F.

  Variable P : Type.
  Variable OP : list P.
  Hypothesis HOP : NoDup OP.
  Hypothesis decP : forall x y : P, {x = y} + {x <> y}.

  (* the prover *)
  Variables aw1 aw2 aw3 a0C GC : P -> F.
  Variable csC : P -> list (list F).
  Variable stratC : P -> list F * list F -> list F -> list F.
  Variables wz1 wz2 wz3 : P -> list F * list F -> list F -> F.

  Hypothesis HcsC : forall p, length (csC p) = m.
  Hypothesis HdegC : forall p i, (i < m)%nat -> (length (nth i (csC p) []) <= degC m i)%nat.
  Hypothesis HmsgC : forall p c4 pre, (length (stratC p c4 pre) <= S (degC m (length pre)))%nat.

  Definition gCf (p : P) (c4 : list F * list F) : list F -> F :=
    gC m W1 W2 W3 (aw1 p) (aw2 p) (aw3 p) (fst c4)
       (kk (snd c4) 0) (kk (snd c4) 1) (kk (snd c4) 2) (kk (snd c4) 3) (a0C p) (csC p).

  Definition claimC (p : P) (c4 : list F * list F) : F := kk (snd c4) 3 * GC p.

  Definition AccC (p : P) (c4 : list F * list F) (rz : list F) : Prop :=
    exists clC,
      sc_run (stratC p c4) [] rz (claimC p c4) = Some clC /\
      wz1 p c4 rz = wstar m W1 (aw1 p) rz /\
      wz2 p c4 rz = wstar m W2 (aw2 p) rz /\
      wz3 p c4 rz = wstar m W3 (aw3 p) rz /\
      clC = eqp rz (fst c4) * (kk (snd c4) 0 * cube3 (wz1 p c4 rz) + kk (snd c4) 1 * cube3 (wz2 p c4 rz)
                               + kk (snd c4) 2 * cube3 (wz3 p c4 rz))
            + kk (snd c4) 3 * gmask (a0C p) (csC p) rz.

  Lemma AccC_final : forall p c4 rz, AccC p c4 rz ->
    sc_run (stratC p c4) [] rz (claimC p c4) = Some (gCf p c4 rz).
  Proof.
    intros p c4 rz (clC & hrun & e1 & e2 & e3 & ecl).
    rewrite hrun. f_equal. rewrite ecl, e1, e2, e3. reflexivity.
  Qed.

  Definition C4 : list (list F * list F) := list_prod (all_lists lf m) (all_lists lf 4).
  Definition RZ : list (list F) := all_lists lf m.

  Definition boundC : nat :=
    ((m + 1) * length lf ^ (m + (3 + 1) - 1) * length RZ
     + dsum (degC m) 0 m * length lf ^ (m - 1) * length C4)%nat.

  Theorem soundC :
    (exists b, In b (cube m) /\ (~ tern (W1 b) \/ ~ tern (W2 b) \/ ~ tern (W3 b))) ->
    card_le (list_prod OP (list_prod C4 RZ))
            (fun w => AccC (fst w) (fst (snd w)) (snd (snd w)))
            (boundC * length OP).
  Proof.
    intros (b & hb & hnt).
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (pdec : forall x y : list F * list F, {x = y} + {x <> y}) by (decide equality).
    assert (hC4 : NoDup C4) by (apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd).
    assert (hRZ : NoDup RZ) by (apply all_lists_NoDup; exact Hnd).
    (* a table that is non-zero on the cube *)
    assert (hT : exists T, In T [TC1 W1; TC2 W2; TC3 W3] /\ exists b0, In b0 (cube m) /\ T b0 <> zero).
    { assert (hc : forall W, ~ tern (W b) -> TC1 W b <> zero).
      { intros W hn e. apply hn. apply (@cube_ternary F zero one add mul sub div opp inv Fdec Hf).
        unfold MixIdentities.TC1, MixSummands.cube3 in e.
        assert (hx : W b * W b * W b = (W b * W b * W b - W b) + W b) by field.
        rewrite hx, e. field. }
      destruct hnt as [h | [h | h]].
      + exists (TC1 W1); split; [cbn; tauto | exists b; split; [exact hb | apply hc; exact h]].
      + exists (TC2 W2); split; [cbn; tauto | exists b; split; [exact hb | exact (hc W2 h)]].
      + exists (TC3 W3); split; [cbn; tauto | exists b; split; [exact hb | exact (hc W3 h)]]. }
    apply (card_le_prod_fiber decP OP (list_prod C4 RZ)
             (fun w => AccC (fst w) (fst (snd w)) (snd (snd w))) boundC HOP).
    intros p _. cbn [fst snd].
    set (E6 := fun c4 => claimC p c4 = tsum (gCf p c4) [] m).
    (* the batching challenge *)
    assert (h6 : card_le C4 E6 ((m + 1) * length lf ^ (m + (3 + 1) - 1))).
    { pose proof (@eq_batch_card F zero one add mul sub div opp inv Fdec Hf lf Hnd m
                    [TC1 W1; TC2 W2; TC3 W3] [GtrueC m (a0C p) (csC p) - GC p] (or_introl hT)) as h.
      cbn [length] in h.
      eapply card_le_mono; [ | apply le_n | exact h].
      intros [tz kC] hin e. cbn [fst snd]. unfold C4 in hin. apply in_prod_iff in hin. destruct hin as [_ hk].
      apply all_lists_In in hk. destruct hk as [hk _].
      rewrite (list4 kC hk).
      rewrite <-(@C_claim_diff F zero one add mul sub div opp inv Hf m Hm W1 W2 W3 (aw1 p) (aw2 p) (aw3 p) tz
                   (kk kC 0) (kk kC 1) (kk kC 2) (kk kC 3) (a0C p) (csC p) (GC p)).
      unfold E6, gCf, claimC in e. cbn [fst snd] in e. rewrite <-e. field. }
    pose proof (card_le_prod_cyl ldec C4 RZ E6 _ hRZ h6) as hE6.
    (* the rounds *)
    assert (h7 : card_le (list_prod C4 RZ) (fun w => ~ E6 (fst w) /\ AccC p (fst w) (snd w))
                   (dsum (degC m) 0 m * length lf ^ (m - 1) * length C4)).
    { apply (card_le_prod_fiber pdec C4 RZ (fun w => ~ E6 (fst w) /\ AccC p (fst w) (snd w)) _ hC4).
      intros c4 _. cbn [fst snd].
      destruct (Fdec (claimC p c4) (tsum (gCf p c4) [] m)) as [e | e].
      + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros rz _ [hn _]. apply hn. exact e.
      + pose proof (@sc_sound F zero one add mul sub div opp inv Fdec Hf lf Hnd (gCf p c4) m (degC m)
                      (stratC p c4) (HmsgC p c4)
                      (@certC F zero one add mul sub div opp inv Hf m W1 W2 W3 (aw1 p) (aw2 p) (aw3 p) (fst c4)
                         (kk (snd c4) 0) (kk (snd c4) 1) (kk (snd c4) 2) (kk (snd c4) 3) (a0C p) (csC p)
                         (HcsC p) (HdegC p))
                      m [] (claimC p c4) eq_refl e) as h.
        eapply card_le_mono; [ | apply le_n | exact h].
        intros rz _ [_ hacc]. cbn [app length]. apply AccC_final. exact hacc. }
    pose proof (card_le_or _ _ _ _ _ hE6 h7) as hor.
    eapply card_le_mono; [ | | exact hor].
    + intros [c4 rz] _ hacc. cbn [fst snd] in *.
      destruct (Fdec (claimC p c4) (tsum (gCf p c4) [] m)) as [e | e]; [left; exact e | right; split; assumption].
    + unfold boundC. lia.
  Qed.

End MixSoundC.
