(* Indices and points of the cube, and linearity of multilinear extensions.

   pt l i is the point of {0,1}^l whose coordinates are the bits of i,
   least significant first (the paper's convention: variable 0 is the
   least significant index bit). idr x = sum_i 2^i x_i is the paper's
   id(r).

   - pt_perm: i |-> pt l i enumerates the cube, so a sum over the cube is
     a sum over 0 .. 2^l - 1 (cube_sum_seq);
   - idr_pt: idr (pt l i) = i in F, the tag of ballot i;
   - mle_idr: the extension of the table i |-> i is idr itself;
   - mle_add, mle_scale, mle_sub, mle_const, mle_fsum: linearity;
   - mle_prefix_cube: fixing the first variables at a cube point y is the
     same as extending the table restricted to y. This is the folding
     W~(y, r) of the paper. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle.
Import ListNotations.

Section CubeIndex.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation fsum := (@fsum F zero add).
  Local Notation nF := (@nF F zero one add).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).

  Lemma fsum_perm : forall l l' : list F, Permutation l l' -> fsum l = fsum l'.
  Proof.
    intros l l' hp; induction hp; cbn.
    + reflexivity.
    + rewrite IHhp; reflexivity.
    + field.
    + rewrite IHhp1; exact IHhp2.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Points from indices *)

  Definition bit (i : nat) : F := if Nat.odd i then one else zero.

  Fixpoint pt (l i : nat) : list F :=
    match l with
    | 0 => []
    | S l' => bit i :: pt l' (Nat.div2 i)
    end.

  Lemma pt_length : forall l i, length (pt l i) = l.
  Proof. induction l as [| l ih]; intro i; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Lemma pt_cube : forall l i, In (pt l i) (cube l).
  Proof.
    intros l i. apply all_lists_In. split; [apply pt_length |].
    revert i; induction l as [| l ih]; intro i; cbn; constructor; [| apply ih].
    unfold bit. destruct (Nat.odd i); cbn; tauto.
  Qed.

  Lemma one_neq_zero : one <> zero.
  Proof. intro e. exact (@zero_neq_one F eq zero one _ (eq_sym e)). Qed.

  Lemma div2_lt : forall l i, (i < 2 ^ S l)%nat -> (Nat.div2 i < 2 ^ l)%nat.
  Proof.
    intros l i h. pose proof (Nat.div2_odd i) as e. cbn [Nat.pow] in h.
    destruct (Nat.odd i); cbn in e; lia.
  Qed.

  Lemma pt_inj : forall l i j, (i < 2 ^ l)%nat -> (j < 2 ^ l)%nat -> pt l i = pt l j -> i = j.
  Proof.
    induction l as [| l ih]; intros i j hi hj e.
    + cbn in hi, hj. lia.
    + cbn [pt] in e. inversion e as [[e1 e2]].
      pose proof (ih _ _ (div2_lt l i hi) (div2_lt l j hj) e2) as ed.
      pose proof (Nat.div2_odd i) as ei. pose proof (Nat.div2_odd j) as ej.
      assert (eo : Nat.odd i = Nat.odd j).
      { unfold bit in e1. destruct (Nat.odd i), (Nat.odd j); try reflexivity; exfalso.
        + exact (one_neq_zero e1).
        + exact (one_neq_zero (eq_sym e1)). }
      rewrite ei, ej, ed, eo. reflexivity.
  Qed.

  Theorem pt_perm : forall l, Permutation (map (pt l) (seq 0 (2 ^ l))) (cube l).
  Proof.
    intro l. apply NoDup_Permutation_bis.
    + apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
      intros i j hi hj e. apply in_seq in hi. apply in_seq in hj. apply (pt_inj l); [lia | lia | exact e].
    + rewrite length_map, length_seq. unfold Mle.cube. rewrite all_lists_length. cbn [length]. lia.
    + intros x hx. apply in_map_iff in hx. destruct hx as (i & <- & _). apply pt_cube.
  Qed.

  Theorem cube_sum_seq : forall (l : nat) (f : list F -> F),
    fsum (map f (cube l)) = fsum (map (fun i => f (pt l i)) (seq 0 (2 ^ l))).
  Proof.
    intros l f. rewrite <-(map_map (pt l) f). apply fsum_perm. apply Permutation_map.
    apply Permutation_sym. apply pt_perm.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The index as a field element *)

  Fixpoint idr (x : list F) : F :=
    match x with
    | [] => zero
    | x0 :: xs => x0 + (one + one) * idr xs
    end.

  Lemma nF_double : forall k, nF (2 * k) = (one + one) * nF k.
  Proof.
    intro k. replace (2 * k)%nat with (k + k)%nat by lia.
    rewrite (@nF_add F zero one add mul sub div opp inv Hf). field.
  Qed.

  Theorem idr_pt : forall l i, (i < 2 ^ l)%nat -> idr (pt l i) = nF i.
  Proof.
    induction l as [| l ih]; intros i hi.
    + cbn in hi. assert (i = 0%nat) by lia. subst i. reflexivity.
    + cbn [pt idr]. rewrite (ih _ (div2_lt l i hi)).
      pose proof (Nat.div2_odd i) as e. rewrite e at 3.
      rewrite Nat.add_comm, (@nF_add F zero one add mul sub div opp inv Hf), nF_double.
      unfold bit. destruct (Nat.odd i); cbn; field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Linearity of the multilinear extension *)

  Lemma mle_add : forall m T T' x, mle m (fun b => T b + T' b) x = mle m T x + mle m T' x.
  Proof.
    intros m T T' x. unfold Mle.mle.
    rewrite <-(@fsum_map_add F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros b _. field.
  Qed.

  Lemma mle_scale : forall m c T x, mle m (fun b => c * T b) x = c * mle m T x.
  Proof.
    intros m c T x. unfold Mle.mle.
    rewrite <-(@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros b _. field.
  Qed.

  Lemma mle_sub : forall m T T' x, mle m (fun b => T b - T' b) x = mle m T x - mle m T' x.
  Proof.
    intros m T T' x.
    rewrite (@mle_ext F zero one add mul sub m _ (fun b => T b + opp one * T' b))
      by (intros; field).
    rewrite mle_add, mle_scale. field.
  Qed.

  Lemma mle_const : forall m c x, length x = m -> mle m (fun _ => c) x = c.
  Proof.
    intros m c x hx.
    rewrite (@mle_ext F zero one add mul sub m _ (fun _ => c * one)) by (intros; field).
    rewrite mle_scale, (@mle_const_one F zero one add mul sub div opp inv Hf m x hx). field.
  Qed.

  Lemma mle_fsum : forall {A : Type} m (phi : A -> list F -> F) (l : list A) x, length x = m ->
    mle m (fun b => fsum (map (fun a => phi a b) l)) x = fsum (map (fun a => mle m (phi a) x) l).
  Proof.
    intros A m phi l x hx; induction l as [| a l ih]; cbn [map LogDer.fsum].
    + apply mle_const. exact hx.
    + rewrite mle_add, ih. reflexivity.
  Qed.

  Lemma mle_weighted : forall m T t,
    fsum (map (fun b => eqp b t * T b) (cube m)) = mle m T t.
  Proof.
    intros m T t. unfold Mle.mle. apply (@fsum_map_ext F zero add). intros b _. field.
  Qed.

  Theorem mle_prefix_cube : forall (n l : nat) (T : list F -> F) (y r : list F),
    In y (cube n) -> mle (n + l) T (y ++ r) = mle l (fun bb => T (y ++ bb)) r.
  Proof.
    induction n as [| n ih]; intros l T y r hy.
    + unfold Mle.cube in hy. cbn in hy. destruct hy as [<- | []]. reflexivity.
    + rewrite cube_S in hy. apply in_app_or in hy.
      destruct hy as [hy | hy]; apply in_map_iff in hy; destruct hy as (y' & <- & hy');
        cbn [Nat.add app]; rewrite (@mle_S F zero one add mul sub div opp inv Hf);
        rewrite !(ih l _ y' r hy'); cbn [app]; field.
  Qed.

  Theorem mle_idr : forall m x, length x = m -> mle m idr x = idr x.
  Proof.
    induction m as [| m ih]; intros x hx.
    + destruct x; [| discriminate]. rewrite (@mle_0 F zero one add mul sub div opp inv Hf). reflexivity.
    + destruct x as [| x0 xs]; [discriminate |]. cbn in hx.
      rewrite (@mle_S F zero one add mul sub div opp inv Hf). cbn [idr].
      rewrite (mle_add m (fun _ => zero) (fun b => (one + one) * idr b) xs).
      rewrite (mle_add m (fun _ => one) (fun b => (one + one) * idr b) xs).
      rewrite !mle_scale, !mle_const, (ih xs) by lia. field.
  Qed.

End CubeIndex.
