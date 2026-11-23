(* Tables on the Boolean cube and their multilinear extensions
   (paper, Section 2.2).

   A point is a list of field elements; the cube {0,1}^m is the list
   cube m of the 2^m points with coordinates zero or one. A table is a
   function on points, of which only the values on the cube matter.

     eqp b x   = prod_i (b_i x_i + (1 - b_i)(1 - x_i))
     mle m T x = sum_{b in cube m} T b * eqp b x

   Results:
   - mle_S: the extension is affine in its first variable,
       mle (m+1) T (x0 :: xs) = (1 - x0) * mle m T0 xs + x0 * mle m T1 xs;
   - mle_cube: the extension agrees with the table on the cube;
   - mle_const_one: sum_b eqp b x = 1;
   - mle_zero_count: a table that is non-zero somewhere on the cube has an
     extension with at most m * |F|^(m-1) zeros in F^m. This is the
     statement behind "sum_x eq(t, x) T(x) = 0 for a random t implies
     T = 0 on the cube", used for the batching challenges t_c, t_z and
     theta of the paper. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer.
Import ListNotations.

Section Mle.

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

  Definition feqb (x y : F) : bool := if Fdec x y then true else false.

  Lemma feqb_true : forall x y, feqb x y = true <-> x = y.
  Proof. intros x y; unfold feqb; destruct (Fdec x y); split; intro h; try assumption; try reflexivity; try discriminate; contradiction. Qed.

  Lemma fsum_app : forall l l' : list F, fsum (l ++ l') = fsum l + fsum l'.
  Proof. induction l as [| x l ih]; intro l'; cbn; [field | rewrite ih; field]. Qed.

  Lemma fsum_map_mul_l : forall {A : Type} (c : F) (g : A -> F) (l : list A),
    fsum (map (fun a => c * g a) l) = c * fsum (map g l).
  Proof. induction l as [| a l ih]; cbn; [field | rewrite ih; field]. Qed.

  (* The Boolean cube *)
  Definition cube (m : nat) : list (list F) := all_lists [zero; one] m.

  Lemma cube_S : forall m, cube (S m) = map (cons zero) (cube m) ++ map (cons one) (cube m).
  Proof.
    intro m. unfold cube. cbn [all_lists list_prod].
    rewrite app_nil_r, map_app, !map_map. reflexivity.
  Qed.

  Lemma cube_length : forall m b, In b (cube m) -> length b = m.
  Proof. intros m b h. apply all_lists_In in h; tauto. Qed.

  Lemma fsum_cube_S : forall (h : list F -> F) (m : nat),
    fsum (map h (cube (S m))) =
    fsum (map (fun b => h (zero :: b)) (cube m)) + fsum (map (fun b => h (one :: b)) (cube m)).
  Proof.
    intros h m. rewrite cube_S, map_app, fsum_app, !map_map. reflexivity.
  Qed.

  Fixpoint eqp (b x : list F) : F :=
    match b, x with
    | bi :: b', xi :: x' => (bi * xi + (one - bi) * (one - xi)) * eqp b' x'
    | _, _ => one
    end.

  Definition mle (m : nat) (T : list F -> F) (x : list F) : F :=
    fsum (map (fun b => T b * eqp b x) (cube m)).

  Lemma mle_0 : forall T x, mle 0 T x = T [].
  Proof. intros T x; unfold mle, cube; cbn. field. Qed.

  Lemma mle_S : forall m T x0 xs,
    mle (S m) T (x0 :: xs) =
    (one - x0) * mle m (fun b => T (zero :: b)) xs + x0 * mle m (fun b => T (one :: b)) xs.
  Proof.
    intros m T x0 xs. unfold mle. rewrite fsum_cube_S.
    rewrite <-!fsum_map_mul_l. f_equal; apply fsum_map_ext; intros b _; cbn; field.
  Qed.

  Lemma mle_ext : forall m T T' x, (forall b, In b (cube m) -> T b = T' b) -> mle m T x = mle m T' x.
  Proof.
    intros m T T' x h. unfold mle. apply fsum_map_ext; intros b hb. rewrite (h b hb); reflexivity.
  Qed.

  Lemma mle_cube : forall m T b, In b (cube m) -> mle m T b = T b.
  Proof.
    induction m as [| m ih]; intros T b hb.
    + rewrite mle_0. unfold cube in hb; cbn in hb. destruct hb as [<- | []]; reflexivity.
    + rewrite cube_S in hb. apply in_app_or in hb.
      destruct hb as [hb | hb]; apply in_map_iff in hb; destruct hb as (b' & <- & hb').
      - rewrite mle_S, !ih by exact hb'. field.
      - rewrite mle_S, !ih by exact hb'. field.
  Qed.

  Lemma mle_const_one : forall m x, length x = m -> mle m (fun _ => one) x = one.
  Proof.
    induction m as [| m ih]; intros x hx.
    + apply mle_0.
    + destruct x as [| x0 xs]; [discriminate |]. rewrite mle_S, !ih by (cbn in hx; lia). field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Zeros of a multilinear extension *)

  Lemma affine_roots : forall (lf : list F), NoDup lf -> forall A B : F, (A <> zero \/ B <> zero) ->
    Nat.le (length (filter (fun x0 => feqb ((one - x0) * A + x0 * B) zero) lf)) 1.
  Proof.
    intros lf hnd A B hAB.
    set (p := [A; B - A]).
    assert (hp : ~ pz p).
    { intro h. inversion h as [| ? ? hA h']; subst. inversion h' as [| ? ? hB _]; subst.
      destruct hAB as [hne | hne]; apply hne; [reflexivity |].
      assert (e : B = (B - zero) + zero) by field. rewrite e, hB; field. }
    assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf 2 p (le_n _) hp
              (filter (fun x0 => feqb ((one - x0) * A + x0 * B) zero) lf) (NoDup_filter _ hnd)).
    assert (hr : forall r, In r (filter (fun x0 => feqb ((one - x0) * A + x0 * B) zero) lf) -> peval p r = zero).
    { intros r hr. apply filter_In in hr; destruct hr as [_ hr]. apply feqb_true in hr.
      unfold p; cbn. transitivity ((one - r) * A + r * B); [field | exact hr]. }
    specialize (hlt hr). cbn in hlt. lia.
  Qed.

  Theorem mle_zero_count : forall (lf : list F), NoDup lf ->
    forall (m : nat) (T : list F -> F),
    (exists b, In b (cube m) /\ T b <> zero) ->
    (length (filter (fun x => feqb (mle m T x) zero) (all_lists lf m)) <= m * length lf ^ (m - 1))%nat.
  Proof.
    intros lf hnd; induction m as [| m ih]; intros T (b & hb & hTb).
    + unfold cube in hb; cbn in hb. destruct hb as [<- | []].
      cbn [all_lists filter].
      destruct (feqb (mle 0 T []) zero) eqn:e; [| cbn; lia].
      apply feqb_true in e. rewrite mle_0 in e. contradiction.
    + (* one of the two halves of the table is non-zero *)
      assert (hhalf : exists c : F, (c = zero \/ c = one) /\ exists b', In b' (cube m) /\ T (c :: b') <> zero).
      { rewrite cube_S in hb. apply in_app_or in hb.
        destruct hb as [hb | hb]; apply in_map_iff in hb; destruct hb as (b' & <- & hb');
          [exists zero | exists one]; (split; [tauto | exists b'; split; assumption]). }
      destruct hhalf as (c & hcz & hc).
      specialize (ih (fun b' => T (c :: b')) hc).
      set (Zc := fun xs => feqb (mle m (fun b' => T (c :: b')) xs) zero) in *.
      rewrite filter_all_lists_S.
      assert (hbound : (nsum (map (fun xs => length (filter (fun x0 => feqb (mle (S m) T (x0 :: xs)) zero) lf))
                          (all_lists lf m))
                        <= length lf * length (filter Zc (all_lists lf m)) + length (all_lists lf m))%nat).
      { apply nsum_map_le_cases; intros xs _; split; intro hz.
        + apply filter_length_le.
        + assert (hne : mle m (fun b' => T (c :: b')) xs <> zero).
          { intro e0. unfold Zc in hz. apply feqb_true in e0. rewrite e0 in hz; discriminate. }
          assert (hAB : mle m (fun b' => T (zero :: b')) xs <> zero \/ mle m (fun b' => T (one :: b')) xs <> zero).
          { destruct hcz as [ec | ec]; rewrite ec in hne; [left | right]; exact hne. }
          pose proof (affine_roots lf hnd _ _ hAB) as h1.
          erewrite filter_ext; [exact h1 |]. intro x0. cbn beta. rewrite mle_S. reflexivity. }
      rewrite all_lists_length in hbound.
      replace (S m - 1)%nat with m by lia.
      assert (hpow : (length lf * (m * length lf ^ (m - 1)) <= m * length lf ^ m)%nat).
      { destruct m as [| m']; [lia |]. replace (S m' - 1)%nat with m' by lia. cbn [Nat.pow]. lia. }
      assert (h2 : (length lf * length (filter Zc (all_lists lf m)) <= length lf * (m * length lf ^ (m - 1)))%nat)
        by (apply Nat.mul_le_mono_l; exact ih).
      cbn [Nat.mul]. lia.
  Qed.

End Mle.
