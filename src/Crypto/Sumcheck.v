(* The sumcheck protocol (paper, Section 2.3), for an arbitrary summand
   g : F^m -> F.

   Notation. rs is the list of challenges so far and k the number of
   variables still to be summed, so length rs + k = m.

     tsum rs k    = sum_{b in cube k} g (rs ++ b)          the true claim
     rnd rs k X   = sum_{b in cube k} g (rs ++ X :: b)     the true round function

   A round message is a univariate polynomial p as a coefficient list.
   The verifier checks p(0) + p(1) = claim and continues with p(r).

   Results:
   - tsum_S, rnd_snoc: the two identities that make the protocol work;
   - round_sound: the round-by-round soundness step. If the running claim
     is false, the true round function is a polynomial of at most dj + 1
     coefficients, and the message has at most dj + 1 coefficients and
     passes the check, then the new claim is true for at most dj
     challenges r;
   - sc_verify_honest: completeness. With the true round polynomials as
     messages the verifier's checks pass and the final claim is g at the
     challenge point.

   The wire format of the paper (evaluations at 0, 2, .., d instead of
   coefficients) is not treated here; it belongs to the executable
   verifier. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle.
Import ListNotations.

Section Sumcheck.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation fsum := (@fsum F zero add).
  Local Notation peval := (@eval F zero add mul).
  Local Notation pz := (@pzero F zero).
  Local Notation cube := (@cube F zero one).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).

  Variable g : list F -> F.

  Definition tsum (rs : list F) (k : nat) : F := fsum (map (fun b => g (rs ++ b)) (cube k)).

  Definition rnd (rs : list F) (k : nat) (X : F) : F := fsum (map (fun b => g (rs ++ X :: b)) (cube k)).

  Lemma tsum_S : forall rs k, tsum rs (S k) = rnd rs k zero + rnd rs k one.
  Proof. intros rs k. unfold tsum, rnd. rewrite fsum_cube_S. reflexivity. Qed.

  Lemma rnd_snoc : forall rs k r, rnd rs k r = tsum (rs ++ [r]) k.
  Proof.
    intros rs k r. unfold tsum, rnd. apply fsum_map_ext; intros b _.
    rewrite <-app_assoc. reflexivity.
  Qed.

  Lemma tsum_0 : forall rs, tsum rs 0 = g rs.
  Proof. intro rs. unfold tsum, cube. cbn. rewrite app_nil_r. field. Qed.

  (* One round: a false claim survives for at most dj challenges. *)
  Theorem round_sound : forall (lf : list F), NoDup lf ->
    forall (rs : list F) (k dj : nat) (pstar p : list F) (claim : F),
    (forall X, peval pstar X = rnd rs k X) ->
    (length pstar <= S dj)%nat -> (length p <= S dj)%nat ->
    peval p zero + peval p one = claim ->
    claim <> tsum rs (S k) ->
    (length (filter (fun r => feqb (peval p r) (tsum (rs ++ [r]) k)) lf) <= dj)%nat.
  Proof.
    intros lf hnd rs k dj pstar p claim hstar hls hlp hcheck hfalse.
    set (df := padd p (pscale (opp one) pstar)).
    assert (hdf : forall X, peval df X = peval p X - peval pstar X).
    { intro X. unfold df. rewrite eval_padd, eval_pscale. field. }
    assert (hnz : ~ pz df).
    { intro hz. apply hfalse. rewrite tsum_S, <-!hstar, <-hcheck.
      pose proof (@eval_pzero F zero one add mul sub div opp inv Hf df zero hz) as h0.
      pose proof (@eval_pzero F zero one add mul sub div opp inv Hf df one hz) as h1.
      rewrite hdf in h0, h1.
      assert (e0 : peval p zero = (peval p zero - peval pstar zero) + peval pstar zero) by field.
      assert (e1 : peval p one = (peval p one - peval pstar one) + peval pstar one) by field.
      rewrite e0, e1, h0, h1. field. }
    assert (hlen : (length df <= S dj)%nat).
    { unfold df. rewrite length_padd, length_pscale. lia. }
    assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf (length df) df (le_n _) hnz
              (filter (fun r => feqb (peval p r) (tsum (rs ++ [r]) k)) lf) (NoDup_filter _ hnd)).
    assert (hr : forall r, In r (filter (fun r => feqb (peval p r) (tsum (rs ++ [r]) k)) lf) -> peval df r = zero).
    { intros r hr. apply filter_In in hr; destruct hr as [_ hr]. apply feqb_true in hr.
      rewrite hdf, hr, <-rnd_snoc, <-hstar. field. }
    specialize (hlt hr). lia.
  Qed.

  (* The verifier's side of the rounds: returns the final claim. *)
  Fixpoint sc_verify (msgs : list (list F)) (chals : list F) (claim : F) : option F :=
    match msgs, chals with
    | [], [] => Some claim
    | p :: ms, r :: cs =>
        if feqb (peval p zero + peval p one) claim then sc_verify ms cs (peval p r) else None
    | _, _ => None
    end.

  (* Messages that are the true round polynomials. *)
  Fixpoint honest (rs : list F) (msgs : list (list F)) (chals : list F) : Prop :=
    match msgs, chals with
    | [], [] => True
    | p :: ms, r :: cs => (forall X, peval p X = rnd rs (length cs) X) /\ honest (rs ++ [r]) ms cs
    | _, _ => False
    end.

  Theorem sc_verify_honest : forall (chals : list F) (msgs : list (list F)) (rs : list F),
    honest rs msgs chals ->
    sc_verify msgs chals (tsum rs (length chals)) = Some (g (rs ++ chals)).
  Proof.
    induction chals as [| r cs ih]; intros msgs rs hh; destruct msgs as [| p ms]; cbn in hh; try contradiction.
    + cbn [sc_verify length]. rewrite tsum_0, app_nil_r. reflexivity.
    + destruct hh as [hp hrest]. cbn [sc_verify length].
      assert (hc : feqb (peval p zero + peval p one) (tsum rs (S (length cs))) = true).
      { apply feqb_true. rewrite tsum_S, !hp. reflexivity. }
      rewrite hc, hp, rnd_snoc, (ih ms (rs ++ [r]) hrest), <-app_assoc. reflexivity.
  Qed.

  (* What an accepting run establishes, round by round: if the verifier
     reaches the final claim c from a starting claim, the checks held. *)
  Lemma sc_verify_step : forall p ms r cs claim c,
    sc_verify (p :: ms) (r :: cs) claim = Some c ->
    peval p zero + peval p one = claim /\ sc_verify ms cs (peval p r) = Some c.
  Proof.
    intros p ms r cs claim c h. cbn in h.
    destruct (feqb (peval p zero + peval p one) claim) eqn:e; [| discriminate].
    apply feqb_true in e. split; assumption.
  Qed.

End Sumcheck.
