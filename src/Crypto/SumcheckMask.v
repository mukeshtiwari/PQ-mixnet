(* The sumcheck mask (paper, Section 2.3 and step (2) of the proof of
   Theorem 5.3).

   The mask is a constant plus one univariate polynomial without constant
   term per variable:

       gmask a0 cs x = a0 + sum_j x_j * (c_{j,1} + c_{j,2} x_j + ...)

   where cs is the list of the coefficient lists c_j.

   Results:
   - mask_tsum: the sum of the mask over the cube is
       G = 2^m * a0 + W cs,   W (c :: cs) = 2^(length cs) * s(c) + 2 * W cs,
     with s(c) the sum of the coefficients of c;
   - mask_round_poly: in the round of variable j, with k variables still
     to be summed, the round function of the mask is the polynomial
       (2^k * (a0 + prefix value) + W post) :: map (2^k * _) c_j,
     so its non-constant coefficients are 2^k times those of c_j;
   - p2_nonzero: 2^k is non-zero when 2 is.

   Together: for 2 <> 0 the map from (a0, cs) to (G, non-constant
   coefficients of every round polynomial) is a bijection, diagonal in cs
   and affine in a0. This is the "triangular affine bijection" used by the
   simulator. Note the hypothesis 2 <> 0, which the paper leaves implicit
   (its field has odd characteristic). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Sumcheck.
Import ListNotations.

Section SumcheckMask.

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
  Local Notation cube := (@cube F zero one).
  Local Notation pscale := (@pscale F mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation rnd := (@rnd F zero one add).
  Local Notation mul_nonzero := (@mul_nonzero F zero one add mul sub div opp inv Hf).

  Definition two : F := one + one.

  Fixpoint p2 (k : nat) : F :=
    match k with
    | 0 => one
    | S k' => two * p2 k'
    end.

  Lemma p2_nonzero : two <> zero -> forall k, p2 k <> zero.
  Proof.
    intros h2; induction k as [| k ih]; cbn.
    + intro e; exact (@zero_neq_one F eq zero one _ (eq_sym e)).
    + apply mul_nonzero; assumption.
  Qed.

  (* x * (c1 + c2 x + ...): a polynomial without constant term *)
  Definition uni (c : list F) (x : F) : F := x * peval c x.

  Fixpoint gtail (cs : list (list F)) (x : list F) : F :=
    match cs, x with
    | c :: cs', xi :: x' => uni c xi + gtail cs' x'
    | _, _ => zero
    end.

  Definition gmask (a0 : F) (cs : list (list F)) (x : list F) : F := a0 + gtail cs x.

  Fixpoint W (cs : list (list F)) : F :=
    match cs with
    | [] => zero
    | c :: cs' => p2 (length cs') * uni c one + two * W cs'
    end.

  Lemma gtail_app : forall pre rs cs' x, length rs = length pre ->
    gtail (pre ++ cs') (rs ++ x) = gtail pre rs + gtail cs' x.
  Proof.
    induction pre as [| c pre ih]; intros rs cs' x hl; destruct rs as [| r rs]; cbn in hl; try lia.
    + cbn. field.
    + cbn. rewrite ih by lia. field.
  Qed.

  Lemma cube_sum_tail : forall cs A,
    fsum (map (fun b => A + gtail cs b) (cube (length cs))) = p2 (length cs) * A + W cs.
  Proof.
    induction cs as [| c cs ih]; intro A.
    + unfold Mle.cube. cbn. field.
    + cbn [length]. rewrite fsum_cube_S.
      rewrite (fsum_map_ext (fun b => A + gtail (c :: cs) (zero :: b)) (fun b => (A + uni c zero) + gtail cs b))
        by (intros; cbn; field).
      rewrite (fsum_map_ext (fun b => A + gtail (c :: cs) (one :: b)) (fun b => (A + uni c one) + gtail cs b))
        by (intros; cbn; field).
      rewrite !ih. cbn [W p2]. unfold uni, two. field.
  Qed.

  Theorem mask_tsum : forall a0 cs,
    tsum (gmask a0 cs) [] (length cs) = p2 (length cs) * a0 + W cs.
  Proof.
    intros a0 cs. unfold Sumcheck.tsum, gmask. cbn [app]. apply cube_sum_tail.
  Qed.

  Theorem mask_round_poly : forall a0 pre c post rs X, length rs = length pre ->
    peval ((p2 (length post) * (a0 + gtail pre rs) + W post) :: pscale (p2 (length post)) c) X
    = rnd (gmask a0 (pre ++ c :: post)) rs (length post) X.
  Proof.
    intros a0 pre c post rs X hl. unfold Sumcheck.rnd, gmask.
    rewrite (fsum_map_ext _ (fun b => (a0 + gtail pre rs + uni c X) + gtail post b)).
    + rewrite cube_sum_tail. cbn [eval]. rewrite eval_pscale. unfold uni. field.
    + intros b _. rewrite gtail_app by exact hl. cbn. field.
  Qed.

End SumcheckMask.
