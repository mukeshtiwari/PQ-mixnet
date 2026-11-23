(* Soundness of the linearisation part of the shuffle proof (the challenge
   rhoB and sumcheck B), against an adaptive prover.

   Everything before rhoB is collected in a value p of an arbitrary finite
   type P: the challenges (rho, alpha, beta), the end point r p of
   sumcheck A, the value H p that the prover claimed for hstar(r), the
   masks, the mask sum G_B and the tables rp_k of rho'.

   Acceptance (AccB). The verifier runs sumcheck B from the claim
   H - mle zpub r - beta * id(r) + alpha + rhoB * G_B, and claim 4 of the
   paper holds for the committed tables: the final claim is the summand
   gB at the end point.

   Theorem soundB. The challenges (p, rhoB, ry) for which H p is not
   hstar(r p) and the verifier accepts number at most
       (1 * |F|^n1 + 2 n1 |F|^(n1-1) * |F|) * |P|,
   a fraction (1 + 2 log N)/|F|: the two budget lines of Theorem 5.2 for
   sumcheck B. Needs N = 2^n1 non-zero in F, since the verifier divides
   by N. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask SumcheckSound PolyFun MaskedExt CubeIndex EqBatch MixSummands MixIdentities.
Import ListNotations.

Section MixSoundB.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation nF := (@nF F zero one add).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation idr := (@idr F zero one add mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation sc_run := (@sc_run F zero one add mul Fdec).
  Local Notation gB := (@gB F zero one add mul sub).
  Local Notation htab := (@htab F zero one add mul sub).
  Local Notation GtrueB := (@GtrueB F zero one add mul).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.

  Variables n1 ell : nat.
  Hypothesis HN : nF (2 ^ n1) <> zero.
  Variables W1 W2 W3 : list F -> F.

  Variable P : Type.
  Variable OP : list P.
  Hypothesis HOP : NoDup OP.
  Hypothesis decP : forall x y : P, {x = y} + {x <> y}.

  (* what the earlier rounds fixed *)
  Variables rp1 rp2 rp3 zp : P -> list F -> F.
  Variables al be ah a0B GB Hv : P -> F.
  Variable csB : P -> list (list F).
  Variable r : P -> list F.
  Variable stratB : P -> F -> list F -> list F.

  Hypothesis Hr : forall p, In p OP -> length (r p) = ell.
  Hypothesis HcsB : forall p, length (csB p) = n1.
  Hypothesis HdegB : forall p i, (i < n1)%nat -> (length (nth i (csB p) []) <= 2)%nat.
  Hypothesis HmsgB : forall p rB pre, (length (stratB p rB pre) <= S (degB (length pre)))%nat.

  Definition cBf (p : P) : F := ah p * Zp (r p) * inv (nF (2 ^ n1)).

  Definition gBf (p : P) (rB : F) : list F -> F :=
    gB n1 ell (rp1 p) (rp2 p) (rp3 p) W1 W2 W3 (r p) (cBf p) rB (a0B p) (csB p).

  Definition claimB (p : P) (rB : F) : F :=
    Hv p - mle ell (zp p) (r p) - be p * idr (r p) + al p + rB * GB p.

  Definition AccB (p : P) (rB : F) (ry : list F) : Prop :=
    sc_run (stratB p rB) [] ry (claimB p rB) = Some (gBf p rB ry).

  Definition hstarB (p : P) : F :=
    mstar ell (htab n1 (rp1 p) (rp2 p) (rp3 p) W1 W2 W3 (zp p) (al p) (be p)) (ah p) (r p).

  Definition boundB : nat :=
    (1 * length (all_lists lf n1) + dsum degB 0 n1 * length lf ^ (n1 - 1) * length lf)%nat.

  Theorem soundB :
    card_le (list_prod OP (list_prod lf (all_lists lf n1)))
            (fun w => Hv (fst w) <> hstarB (fst w) /\ AccB (fst w) (fst (snd w)) (snd (snd w)))
            (boundB * length OP).
  Proof.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (hRY : NoDup (all_lists lf n1)) by (apply all_lists_NoDup; exact Hnd).
    apply (card_le_prod_fiber decP OP (list_prod lf (all_lists lf n1))
             (fun w => Hv (fst w) <> hstarB (fst w) /\ AccB (fst w) (fst (snd w)) (snd (snd w))) boundB HOP).
    intros p hp. cbn [fst snd].
    destruct (Fdec (Hv p) (hstarB p)) as [eH | eH].
    { apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
      intros w _ [hn _]. apply hn. exact eH. }
    assert (hcB : nF (2 ^ n1) * cBf p = ah p * Zp (r p)).
    { unfold cBf. field. exact HN. }
    set (E4 := fun rB => claimB p rB = tsum (gBf p rB) [] n1).
    assert (h4 : card_le lf E4 1).
    { pose proof (@affine_card F zero one add mul sub div opp inv Fdec Hf lf Hnd
                    (hstarB p - Hv p) (GtrueB n1 (a0B p) (csB p) - GB p)) as h.
      eapply card_le_mono; [ | apply le_n | apply h].
      + intros rB _ e. unfold E4 in e. unfold hstarB.
        rewrite <-(@B_claim_diff F zero one add mul sub div opp inv Hf n1 ell (rp1 p) (rp2 p) (rp3 p) W1 W2 W3 (zp p)
                     (al p) (be p) (r p) (ah p) (cBf p) rB (a0B p) (csB p) (Hr p hp) hcB (Hv p) (GB p)).
        unfold claimB, gBf in e. rewrite <-e. field.
      + intro e. apply eH.
        assert (hx : Hv p = hstarB p - (hstarB p - Hv p)) by field. rewrite hx, e. field. }
    pose proof (card_le_prod_cyl ldec lf (all_lists lf n1) E4 _ hRY h4) as hE4.
    assert (h5 : card_le (list_prod lf (all_lists lf n1)) (fun w => ~ E4 (fst w) /\ AccB p (fst w) (snd w))
                   (dsum degB 0 n1 * length lf ^ (n1 - 1) * length lf)).
    { apply (card_le_prod_fiber Fdec lf (all_lists lf n1) (fun w => ~ E4 (fst w) /\ AccB p (fst w) (snd w)) _ Hnd).
      intros rB _. cbn [fst snd].
      destruct (Fdec (claimB p rB) (tsum (gBf p rB) [] n1)) as [e | e].
      + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros ry _ [hn _]. apply hn. exact e.
      + pose proof (@sc_sound F zero one add mul sub div opp inv Fdec Hf lf Hnd (gBf p rB) n1 degB
                      (stratB p rB) (HmsgB p rB)
                      (@certB F zero one add mul sub div opp inv Hf n1 ell (rp1 p) (rp2 p) (rp3 p) W1 W2 W3 (r p)
                         (cBf p) rB (a0B p) (csB p) (HcsB p) (HdegB p))
                      n1 [] (claimB p rB) eq_refl e) as h.
        eapply card_le_mono; [ | apply le_n | exact h].
        intros ry _ [_ hacc]. cbn [app length]. exact hacc. }
    pose proof (card_le_or _ _ _ _ _ hE4 h5) as hor.
    eapply card_le_mono; [ | | exact hor].
    + intros [rB ry] _ [_ hacc]. cbn [fst snd] in *.
      destruct (Fdec (claimB p rB) (tsum (gBf p rB) [] n1)) as [e | e]; [left; exact e | right; split; assumption].
    + unfold boundB. lia.
  Qed.

End MixSoundB.
