(* The batching challenges of the sumchecks (paper, Theorem 5.2, budget
   lines "claim of A true although an inverse or the sum is wrong",
   "claim of C true although W is not ternary", and "H wrong although the
   claim of B is true").

   A sumcheck claim of the paper has the form

       sum_i k_i * mle T_i (t)  +  sum_j x_j * e_j  =  0

   for tables T_i that should vanish on the cube and constants e_j that
   should be zero, with challenges t in F^m and (k, x) in F^n.

   eq_batch_card. If some table is non-zero somewhere on the cube, or some
   constant is non-zero, the equation holds for at most
   (m + 1) * |F|^(m + n - 1) of the |F|^(m + n) challenges.

   For sumcheck A the tables are u*h - 1 and uhat*hhat - 1 and the
   constants are sum (u - uhat) and G_A' - G_A; for sumcheck C the tables
   are the three w_k^3 - w_k and the constant is G_C' - G_C.

   affine_card. a + x * b = 0 with a <> 0 holds for at most one x. This is
   the step of rho_B: (h*(r) - H) + rho_B * (G_B' - G_B) = 0. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Proximity ReedSolomon Opening.
Import ListNotations.

Section EqBatch.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation dot := (@dot F zero add mul).
  Local Notation allzero := (@allzero F zero Fdec).
  Local Notation peval := (@eval F zero add mul).
  Local Notation pz := (@pzero F zero).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.

  Lemma allzero_false_in : forall (g : list F) (x : F), In x g -> x <> zero -> allzero g = false.
  Proof.
    intros g x hin hx. destruct (allzero g) eqn:e; [| reflexivity].
    exfalso. apply hx. apply (@allzero_spec F zero Fdec) in e. rewrite Forall_forall in e. exact (e x hin).
  Qed.

  Lemma linear_card : forall g : list F, allzero g = false ->
    card_le (all_lists lf (length g)) (fun v => dot g v = zero) (length lf ^ (length g - 1)).
  Proof.
    intros g hg. apply (card_le_of_filter (list_eq_dec Fdec)). intros b hb.
    eapply Nat.le_trans; [| exact (@linear_form_zero_count F zero one add mul sub div opp inv Fdec Hf lf Hnd g hg)].
    apply filter_length_imp. intros v hv. apply feqb_true. exact (hb v hv).
  Qed.

  Theorem affine_card : forall a b : F, a <> zero ->
    card_le lf (fun x => a + x * b = zero) 1.
  Proof.
    intros a b ha. apply (card_le_of_filter Fdec). intros bb hb.
    set (p := [a; b]).
    assert (hp : ~ pz p).
    { intro hz. inversion hz as [| ? ? e0 _]. contradiction. }
    assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf 2 p (le_n _) hp
              (filter bb lf) (NoDup_filter _ Hnd)).
    assert (hr : forall r, In r (filter bb lf) -> peval p r = zero).
    { intros r hr. apply filter_In in hr. destruct hr as [_ hr]. specialize (hb r hr).
      unfold p; cbn. transitivity (a + r * b); [field | exact hb]. }
    specialize (hlt hr). change (length p) with 2%nat in hlt. lia.
  Qed.

  Variable m : nat.
  Variable Ts : list (list F -> F).
  Variable es : list F.

  Definition coefs (t : list F) : list F := map (fun T => mle m T t) Ts ++ es.

  Lemma coefs_length : forall t, length (coefs t) = (length Ts + length es)%nat.
  Proof. intro t. unfold coefs. rewrite length_app, length_map. reflexivity. Qed.

  Theorem eq_batch_card :
    (exists T, In T Ts /\ exists b, In b (cube m) /\ T b <> zero) \/ allzero es = false ->
    card_le (list_prod (all_lists lf m) (all_lists lf (length Ts + length es)))
            (fun tv => dot (coefs (fst tv)) (snd tv) = zero)
            ((m + 1) * length lf ^ (m + (length Ts + length es) - 1)).
  Proof.
    intro hne.
    set (n' := (length Ts + length es)%nat).
    set (q := length lf).
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (hOA : NoDup (all_lists lf m)) by (apply all_lists_NoDup; exact Hnd).
    assert (hOB : NoDup (all_lists lf n')) by (apply all_lists_NoDup; exact Hnd).
    (* the fibre over a point t at which the coefficient vector is non-zero *)
    assert (hfib : forall t, allzero (coefs t) = false ->
              card_le (all_lists lf n') (fun v => dot (coefs t) v = zero) (q ^ (n' - 1))).
    { intros t ht. pose proof (linear_card (coefs t) ht) as h. rewrite coefs_length in h. exact h. }
    destruct hne as [(T & hT & hTb) | hes].
    + (* some table is non-zero *)
      set (Z := fun t => mle m T t = zero).
      assert (hZ : card_le (all_lists lf m) Z (m * q ^ (m - 1))).
      { apply (card_le_of_filter ldec). intros b hb.
        eapply Nat.le_trans; [| exact (@mle_zero_count F zero one add mul sub div opp inv Fdec Hf lf Hnd m T hTb)].
        apply filter_length_imp. intros t ht. apply feqb_true. exact (hb t ht). }
      pose proof (card_le_prod_cyl ldec (all_lists lf m) (all_lists lf n') Z _ hOB hZ) as h1.
      assert (h2 : card_le (list_prod (all_lists lf m) (all_lists lf n'))
                     (fun tv => ~ Z (fst tv) /\ dot (coefs (fst tv)) (snd tv) = zero)
                     (q ^ (n' - 1) * length (all_lists lf m))).
      { apply (card_le_prod_fiber ldec _ _ _ _ hOA). intros t _. cbn [fst snd].
        destruct (Fdec (mle m T t) zero) as [e | e].
        + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
          intros v _ [hn _]. apply hn. exact e.
        + assert (ht : allzero (coefs t) = false).
          { apply (allzero_false_in _ (mle m T t)); [| exact e].
            unfold coefs. apply in_or_app. left. apply (in_map (fun T0 => mle m T0 t)). exact hT. }
          apply (card_le_mono _ _ _ _ _ (fun v _ hh => proj2 hh) (le_n _) (hfib t ht)). }
      pose proof (card_le_or _ _ _ _ _ h1 h2) as hor.
      eapply card_le_mono; [ | | exact hor].
      - intros [t v] _ he. cbn [fst snd] in *.
        destruct (Fdec (mle m T t) zero) as [e | e]; [left; exact e | right; split; assumption].
      - rewrite !all_lists_length. fold q.
        assert (hn1 : (1 <= n')%nat).
        { unfold n'. destruct Ts; [contradiction | cbn; lia]. }
        replace (m + n' - 1)%nat with (m + (n' - 1))%nat by lia.
        rewrite Nat.pow_add_r.
        assert (hq : (q ^ n' = q * q ^ (n' - 1))%nat).
        { replace n' with (S (n' - 1)) at 1 by lia. reflexivity. }
        rewrite hq.
        destruct m as [| m'].
        * cbn. lia.
        * replace (S m' - 1)%nat with m' by lia. cbn [Nat.pow]. nia.
    + (* some constant is non-zero: every fibre is small *)
      assert (h2 : card_le (list_prod (all_lists lf m) (all_lists lf n'))
                     (fun tv => dot (coefs (fst tv)) (snd tv) = zero)
                     (q ^ (n' - 1) * length (all_lists lf m))).
      { apply (card_le_prod_fiber ldec _ _ _ _ hOA). intros t _. cbn [fst snd].
        apply hfib.
        destruct (allzero (coefs t)) eqn:ez; [| reflexivity]. exfalso.
        apply (@allzero_spec F zero Fdec) in ez. unfold coefs in ez. apply Forall_app in ez.
        destruct ez as [_ ez]. apply (@allzero_spec F zero Fdec) in ez. rewrite ez in hes. discriminate. }
      eapply card_le_mono; [ | | exact h2]; [intros; assumption |].
      rewrite all_lists_length. fold q.
      assert (hn1 : (1 <= n')%nat).
      { unfold n'. destruct es; [cbn in hes; discriminate | cbn; lia]. }
      replace (m + n' - 1)%nat with (m + (n' - 1))%nat by lia.
      rewrite Nat.pow_add_r. nia.
  Qed.

End EqBatch.
