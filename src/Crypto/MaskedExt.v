(* Masked extensions (paper, Section 2.2) and their degree in one variable.

     Zp x          = prod_i x_i (1 - x_i)
     mstar m T a x = mle m T x + a * Zp x          (the paper's T-star)

   - Zp_cube, mstar_cube: Zp vanishes on the cube {0,1}^m for m >= 1, so
     the masked extension agrees with the table there;
   - mle_coord: a multilinear extension is affine in every coordinate;
   - eqp_coord: so is eq(x, t) in every coordinate of x;
   - mstar_is_poly: in the variable of position length pre, with the later
     variables on the cube, the masked extension has degree 1 if at least
     one later variable exists and degree 2 otherwise. This is the paper's
     "Degrees" remark: the mask terms contribute nothing to a round
     polynomial except in the last round. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle PolyFun.
Import ListNotations.

Section MaskedExt.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation is_poly := (@is_poly F zero add mul).

  Fixpoint Zp (x : list F) : F :=
    match x with
    | [] => one
    | xi :: x' => xi * (one - xi) * Zp x'
    end.

  Definition mstar (m : nat) (T : list F -> F) (a : F) (x : list F) : F := mle m T x + a * Zp x.

  Lemma Zp_app : forall x y, Zp (x ++ y) = Zp x * Zp y.
  Proof. induction x as [| xi x ih]; intro y; cbn; [field | rewrite ih; field]. Qed.

  Lemma Zp_cube : forall m b, In b (cube (S m)) -> Zp b = zero.
  Proof.
    intros m b hb. rewrite cube_S in hb. apply in_app_or in hb.
    destruct hb as [hb | hb]; apply in_map_iff in hb; destruct hb as (b' & <- & _); cbn; field.
  Qed.

  Lemma mstar_cube : forall m T a b, In b (cube (S m)) -> mstar (S m) T a b = T b.
  Proof.
    intros m T a b hb. unfold mstar. rewrite (Zp_cube m b hb).
    rewrite (@mle_cube F zero one add mul sub div opp inv Hf (S m) T b hb). field.
  Qed.

  Lemma mstar_cube_pos : forall m T a b, (1 <= m)%nat -> In b (cube m) -> mstar m T a b = T b.
  Proof. intros m T a b hm hb. destruct m as [| m']; [lia |]. apply mstar_cube; exact hb. Qed.

  Lemma mle_coord : forall (pre : list F) (k : nat) (T : list F -> F) (X : F) (b : list F),
    mle (length pre + S k) T (pre ++ X :: b) =
    (one - X) * mle (length pre + S k) T (pre ++ zero :: b) + X * mle (length pre + S k) T (pre ++ one :: b).
  Proof.
    induction pre as [| p0 pre ih]; intros k T X b.
    + cbn [length app Nat.add]. rewrite !(@mle_S F zero one add mul sub div opp inv Hf). field.
    + cbn [length app Nat.add]. rewrite !(@mle_S F zero one add mul sub div opp inv Hf).
      rewrite (ih k (fun c => T (zero :: c)) X b), (ih k (fun c => T (one :: c)) X b). field.
  Qed.

  Lemma mle_coord_poly : forall (pre : list F) (k : nat) (T : list F -> F) (b : list F),
    is_poly 1 (fun X => mle (length pre + S k) T (pre ++ X :: b)).
  Proof.
    intros pre k T b.
    apply (is_poly_ext _ (fun X => (one - X) * mle (length pre + S k) T (pre ++ zero :: b)
                                   + X * mle (length pre + S k) T (pre ++ one :: b))).
    + intro X. symmetry. apply mle_coord.
    + apply is_poly_affine. lia.
  Qed.

  Lemma eqp_coord : forall (pre b t : list F), exists A B : F,
    forall X, eqp (pre ++ X :: b) t = A + X * B.
  Proof.
    induction pre as [| p0 pre ih]; intros b t.
    + destruct t as [| t0 t'].
      - exists one, zero. intro X. cbn. field.
      - exists ((one - t0) * eqp b t'), ((t0 - (one - t0)) * eqp b t'). intro X. cbn. field.
    + destruct t as [| t0 t'].
      - exists one, zero. intro X. cbn. field.
      - destruct (ih b t') as (A & B & h).
        exists ((p0 * t0 + (one - p0) * (one - t0)) * A), ((p0 * t0 + (one - p0) * (one - t0)) * B).
        intro X. cbn. rewrite h. field.
  Qed.

  Lemma eqp_coord_poly : forall (pre b t : list F), is_poly 1 (fun X => eqp (pre ++ X :: b) t).
  Proof.
    intros pre b t. destruct (eqp_coord pre b t) as (A & B & h).
    exists [A; B]; split; [cbn; lia |]. intro X. rewrite h. cbn. field.
  Qed.

  Definition lastdeg (k : nat) : nat := match k with 0 => 2 | S _ => 1 end.

  (* The masked extension in one variable, the later ones on the cube. *)
  Theorem mstar_is_poly : forall (pre : list F) (k : nat) (T : list F -> F) (a : F) (b : list F),
    In b (cube k) ->
    is_poly (lastdeg k) (fun X => mstar (length pre + S k) T a (pre ++ X :: b)).
  Proof.
    intros pre k T a b hb. unfold mstar.
    destruct k as [| k'].
    + cbn [lastdeg].
      apply (is_poly_mono (Nat.max 1 2)); [lia |].
      apply is_poly_add; [apply mle_coord_poly |].
      apply is_poly_scale.
      apply (is_poly_ext _ (fun X => (Zp pre * Zp b) * (X * (one - X)))).
      - intro X. rewrite Zp_app. cbn. field.
      - apply is_poly_scale.
        apply (is_poly_mono (1 + 1)); [lia |].
        apply is_poly_mul; [apply is_poly_id; lia |].
        apply (is_poly_mono (Nat.max 0 1)); [lia |].
        apply is_poly_sub; [apply is_poly_const | apply is_poly_id; lia].
    + cbn [lastdeg].
      apply (is_poly_ext _ (fun X => mle (length pre + S (S k')) T (pre ++ X :: b))).
      - intro X. rewrite Zp_app. cbn [Zp]. rewrite (Zp_cube k' b hb). field.
      - apply mle_coord_poly.
  Qed.

End MaskedExt.
