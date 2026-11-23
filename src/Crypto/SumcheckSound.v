(* Soundness of the whole sumcheck against an adaptive prover.

   The prover is a strategy strat: from the challenges so far to its next
   round polynomial. sc_run replays the verifier: it returns the final
   claim, or None if a round check fails.

   Theorem sc_sound. If the initial claim is false, the number of
   challenge vectors for which every round check passes and the final
   claim equals the summand at the challenge point is at most

       (d_0 + ... + d_(k-1)) * |F|^(k-1)        out of |F|^k,

   where d_i bounds the degree of round i, both for the prover's messages
   and for the true round functions (Hmsg, Hcert). This is the budget
   line "sumcheck accepts a false claim" of Theorem 5.2, and its proof is
   the round-by-round argument: a false running claim stays false after a
   round except for d_i challenges (round_sound). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck.
Import ListNotations.

Section SumcheckSound.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation peval := (@eval F zero add mul).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation rnd := (@rnd F zero one add).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.

  Variable g : list F -> F.
  Variable m : nat.                      (* number of variables *)
  Variable deg : nat -> nat.             (* degree bound of round i *)
  Variable strat : list F -> list F.     (* the prover *)

  Hypothesis Hmsg : forall pre, (length (strat pre) <= S (deg (length pre)))%nat.
  Hypothesis Hcert : forall pre k, (length pre + S k = m)%nat ->
    exists pstar, (length pstar <= S (deg (length pre)))%nat /\ forall X, peval pstar X = rnd g pre k X.

  Fixpoint sc_run (pre chals : list F) (claim : F) : option F :=
    match chals with
    | [] => Some claim
    | r :: cs =>
        if feqb (peval (strat pre) zero + peval (strat pre) one) claim
        then sc_run (pre ++ [r]) cs (peval (strat pre) r)
        else None
    end.

  (* Round-by-round form (paper, Proposition 7.1): the state of a partial sumcheck transcript is
     "doomed" when its running claim is false. Whatever round polynomial p the prover sends next
     (degree at most d, and consistent with the claim, or the verifier rejects at once), at most d
     challenges r lead to a state that is not doomed. *)
  Definition sc_doomed (pre : list F) (k : nat) (claim : F) : Prop := claim <> tsum g pre k.

  Theorem sc_round_rbr : forall pre k claim (p : list F),
    (length pre + S k = m)%nat -> sc_doomed pre (S k) claim ->
    (length p <= S (deg (length pre)))%nat -> peval p zero + peval p one = claim ->
    card_le lf (fun r => ~ sc_doomed (pre ++ [r]) k (peval p r)) (deg (length pre)).
  Proof.
    intros pre k claim p hm hd hp hchk.
    apply (card_le_of_filter Fdec). intros b hb.
    destruct (Hcert pre k ltac:(lia)) as (pstar & hsl & hstar).
    pose proof (@round_sound F zero one add mul sub div opp inv Fdec Hf g lf Hnd pre k (deg (length pre))
                  pstar p claim hstar hsl hp hchk hd) as hrs.
    eapply Nat.le_trans; [| exact hrs]. apply filter_length_imp.
    intros r hr. apply feqb_true. specialize (hb r hr). unfold sc_doomed in hb.
    destruct (Fdec (peval p r) (tsum g (pre ++ [r]) k)) as [e | e]; [exact e | contradiction].
  Qed.

  (* a doomed complete transcript is rejected by the final check *)
  Lemma sc_doomed_final : forall pre claim, sc_doomed pre 0 claim -> claim <> g pre.
  Proof.
    intros pre claim h e. apply h. rewrite e.
    rewrite (@tsum_0 F zero one add mul sub div opp inv Hf g). rewrite ?app_nil_r. reflexivity.
  Qed.

  Fixpoint dsum (i k : nat) : nat :=
    match k with
    | 0 => 0
    | S k' => deg i + dsum (S i) k'
    end.

  Theorem sc_sound : forall (k : nat) (pre : list F) (claim : F),
    (length pre + k = m)%nat -> claim <> tsum g pre k ->
    card_le (all_lists lf k) (fun cs => sc_run pre cs claim = Some (g (pre ++ cs)))
            (dsum (length pre) k * length lf ^ (k - 1)).
  Proof.
    induction k as [| k ih]; intros pre claim hm hfalse.
    + apply card_le_false. intros x hx e. cbn in hx. destruct hx as [<- | []].
      cbn in e. inversion e as [e1]. apply hfalse. rewrite e1.
      rewrite (@tsum_0 F zero one add mul sub div opp inv Hf g), app_nil_r. reflexivity.
    + set (p := strat pre).
      destruct (feqb (peval p zero + peval p one) claim) eqn:echk.
      2:{ apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
          intros x hin e. apply all_lists_In in hin. destruct hin as [hlen _].
          destruct x as [| r cs]; [discriminate |]. cbn in e. fold p in e. rewrite echk in e. discriminate. }
      apply feqb_true in echk.
      set (A := fun r => peval p r = tsum g (pre ++ [r]) k).
      (* the head event: the new claim is true *)
      assert (hA : card_le lf A (deg (length pre))).
      { apply (card_le_of_filter Fdec). intros b hb.
        destruct (Hcert pre k ltac:(lia)) as (pstar & hsl & hstar).
        pose proof (@round_sound F zero one add mul sub div opp inv Fdec Hf g lf Hnd pre k (deg (length pre))
                      pstar p claim hstar hsl (Hmsg pre) echk hfalse) as hrs.
        eapply Nat.le_trans; [| exact hrs]. apply filter_length_imp.
        intros r hr. apply feqb_true. exact (hb r hr). }
      pose proof (card_le_head Fdec lf k A (deg (length pre)) Hnd hA) as hhead.
      (* the fibre event: the new claim is false and the rest of the run escapes *)
      set (E2 := fun x => match x with
                          | r :: cs => ~ A r /\ sc_run (pre ++ [r]) cs (peval p r) = Some (g ((pre ++ [r]) ++ cs))
                          | [] => False
                          end).
      assert (hfib : card_le (all_lists lf (S k)) E2 (dsum (S (length pre)) k * length lf ^ (k - 1) * length lf)).
      { apply (card_le_cons Fdec lf k E2 _ Hnd). intros r _. unfold E2.
        destruct (Fdec (peval p r) (tsum g (pre ++ [r]) k)) as [e | e].
        + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
          intros cs _ [hn _]. apply hn. exact e.
        + assert (hl : length (pre ++ [r]) = S (length pre)) by (rewrite length_app; cbn; lia).
          pose proof (ih (pre ++ [r]) (peval p r) ltac:(lia) e) as h. rewrite hl in h.
          apply (card_le_mono _ _ _ _ _ (fun cs _ hh => proj2 hh) (le_n _) h). }
      pose proof (card_le_or _ _ _ _ _ hhead hfib) as hor.
      eapply card_le_mono; [ | | exact hor].
      - intros x hin hx. apply all_lists_In in hin. destruct hin as [hlen _].
        destruct x as [| r cs]; [discriminate |].
        cbn in hx. fold p in hx. rewrite (proj2 (feqb_true _ _) echk) in hx.
        destruct (Fdec (peval p r) (tsum g (pre ++ [r]) k)) as [e | e]; [left; exact e | right].
        unfold E2. split; [exact e |]. rewrite hx, <-app_assoc. reflexivity.
      - cbn [dsum]. replace (S k - 1)%nat with k by lia.
        destruct k as [| k']; [cbn; lia |].
        replace (S k' - 1)%nat with k' by lia. cbn [Nat.pow]. lia.
  Qed.

End SumcheckSound.
