(* Cardinality bounds for events that need not be decidable.

     card_le Om E B  :=  every duplicate-free list of elements of Om that
                         all satisfy E has length at most B.

   For a uniform challenge in Om this says Pr[E] <= B / |Om|. Unlike
   length (filter b Om), it does not ask for a boolean test of E, so
   events such as "the claim is false for the decoded rows" can be used
   directly. The lemmas are the rules of a union-bound calculus:

   - card_le_of_filter   from the boolean counts of the other files;
   - card_le_mono        a smaller event, a larger bound;
   - card_le_or          union bound;
   - card_le_fiber       a bound on every fibre {b : E (a, b)} of a product;
   - card_le_fiber_r     the same for the fibres {a : E (a, b)};
   - card_le_map         transport along a map of the challenge space;
   - card_le_cons        the product structure of all_lists lf (S m).

   Round-by-round soundness is composed from these: a false statement can
   only be accepted through one of finitely many bad events, each of which
   has a small fibre over the challenges that precede it. *)

From Stdlib Require Import Utf8 List Lia Bool Permutation PeanoNat Arith.
From Crypto Require Import Counting.
Import ListNotations.

Section Card.

  Definition card_le {A : Type} (Om : list A) (E : A -> Prop) (B : nat) : Prop :=
    forall l, NoDup l -> incl l Om -> (forall x, In x l -> E x) -> length l <= B.

  Lemma card_le_mono : forall {A : Type} (Om : list A) (E E' : A -> Prop) (B B' : nat),
    (forall x, In x Om -> E x -> E' x) -> B' <= B -> card_le Om E' B' -> card_le Om E B.
  Proof.
    intros A Om E E' B B' himp hle h l hnd hincl hE.
    specialize (h l hnd hincl (fun x hx => himp x (hincl x hx) (hE x hx))). lia.
  Qed.

  Lemma card_le_false : forall {A : Type} (Om : list A) (E : A -> Prop),
    (forall x, In x Om -> ~ E x) -> card_le Om E 0.
  Proof.
    intros A Om E h l _ hincl hE. destruct l as [| x l]; [reflexivity |].
    exfalso. apply (h x); [apply hincl; left; reflexivity | apply hE; left; reflexivity].
  Qed.

  Lemma card_le_total : forall {A : Type} (Om : list A) (E : A -> Prop), card_le Om E (length Om).
  Proof. intros A Om E l hnd hincl _. apply NoDup_incl_length; assumption. Qed.

  Lemma card_le_of_filter : forall {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
    (Om : list A) (E : A -> Prop) (B : nat),
    (forall b : A -> bool, (forall x, b x = true -> E x) -> length (filter b Om) <= B) ->
    card_le Om E B.
  Proof.
    intros A dec Om E B h l hnd hincl hE.
    set (b := fun x => if in_dec dec x l then true else false).
    assert (hb : forall x, b x = true -> E x).
    { intros x hx. unfold b in hx. destruct (in_dec dec x l); [apply hE; assumption | discriminate]. }
    specialize (h b hb).
    assert (hle : length l <= length (filter b Om)).
    { apply NoDup_incl_length; [exact hnd |]. intros x hx. apply filter_In; split; [apply hincl; exact hx |].
      unfold b. destruct (in_dec dec x l); [reflexivity | contradiction]. }
    lia.
  Qed.

  Lemma split_or : forall {A : Type} (E1 E2 : A -> Prop) (l : list A),
    (forall x, In x l -> E1 x \/ E2 x) ->
    exists l1 l2, Permutation l (l1 ++ l2) /\ (forall x, In x l1 -> E1 x) /\ (forall x, In x l2 -> E2 x).
  Proof.
    intros A E1 E2; induction l as [| a l ih]; intro h.
    + exists [], []; split; [constructor | split; intros x []].
    + destruct (ih (fun x hx => h x (or_intror hx))) as (l1 & l2 & hp & h1 & h2).
      destruct (h a (or_introl eq_refl)) as [ha | ha].
      - exists (a :: l1), l2; split; [cbn; constructor; exact hp | split; [| exact h2]].
        intros x [<- | hx]; [exact ha | exact (h1 x hx)].
      - exists l1, (a :: l2); split; [| split; [exact h1 |]].
        * apply Permutation_cons_app; exact hp.
        * intros x [<- | hx]; [exact ha | exact (h2 x hx)].
  Qed.

  Lemma card_le_or : forall {A : Type} (Om : list A) (E1 E2 : A -> Prop) (B1 B2 : nat),
    card_le Om E1 B1 -> card_le Om E2 B2 -> card_le Om (fun x => E1 x \/ E2 x) (B1 + B2).
  Proof.
    intros A Om E1 E2 B1 B2 c1 c2 l hnd hincl hE.
    destruct (split_or E1 E2 l hE) as (l1 & l2 & hp & h1 & h2).
    assert (hnd' : NoDup (l1 ++ l2)) by (apply (Permutation_NoDup hp); exact hnd).
    assert (hi : incl (l1 ++ l2) Om) by (intros x hx; apply hincl; apply (Permutation_in _ (Permutation_sym hp)); exact hx).
    specialize (c1 l1 (NoDup_app_remove_r _ _ hnd') (fun x hx => hi x (in_or_app _ _ _ (or_introl hx))) h1).
    specialize (c2 l2 (NoDup_app_remove_l _ _ hnd') (fun x hx => hi x (in_or_app _ _ _ (or_intror hx))) h2).
    rewrite (Permutation_length hp), length_app. lia.
  Qed.

  Lemma preimage_list : forall {A B : Type} (f : A -> B) (Om : list A) (l : list B),
    incl l (map f Om) -> exists l', map f l' = l /\ incl l' Om.
  Proof.
    intros A B f Om; induction l as [| y l ih]; intro h.
    + exists []; split; [reflexivity | intros x []].
    + destruct (ih (fun x hx => h x (or_intror hx))) as (l' & e & hi).
      assert (hy := h y (or_introl eq_refl)). apply in_map_iff in hy. destruct hy as (x & ex & hx).
      exists (x :: l'); split; [cbn; rewrite ex, e; reflexivity |].
      intros z [<- | hz]; [exact hx | exact (hi z hz)].
  Qed.

  Lemma card_le_map : forall {A B : Type} (f : A -> B) (Om : list A) (E : B -> Prop) (K : nat),
    card_le Om (fun x => E (f x)) K -> card_le (map f Om) E K.
  Proof.
    intros A B f Om E K h l hnd hincl hE.
    destruct (preimage_list f Om l hincl) as (l' & e & hi). subst l.
    rewrite length_map. apply h; [exact (NoDup_map_inv f l' hnd) | exact hi |].
    intros x hx. apply hE. apply in_map; exact hx.
  Qed.

  Lemma filter_none : forall {A : Type} (f : A -> bool) (l : list A),
    (forall b, In b l -> f b = false) -> length (filter f l) = 0.
  Proof.
    induction l as [| a l ih]; intro h; cbn; [reflexivity |].
    rewrite (h a (or_introl eq_refl)). apply ih. intros b hb; apply h; right; exact hb.
  Qed.

  Lemma filter_eq_one : forall {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (Om : list A) (x : A),
    NoDup Om -> In x Om -> length (filter (fun a => if dec x a then true else false) Om) = 1.
  Proof.
    intros A dec; induction Om as [| a Om ih]; intros x hnd hin; [contradiction |].
    inversion hnd as [| ? ? ha hnd']; subst. cbn.
    destruct (dec x a) as [-> | hne].
    + cbn. f_equal. apply filter_none. intros b hb.
      destruct (dec a b) as [-> | _]; [contradiction | reflexivity].
    + destruct hin as [-> | hin]; [contradiction |]. exact (ih x hnd' hin).
  Qed.

  (* Grouping a list by a key. *)
  Lemma group_length : forall {P K : Type} (dec : forall x y : K, {x = y} + {x <> y})
    (key : P -> K) (Ks : list K) (l : list P),
    NoDup Ks -> (forall p, In p l -> In (key p) Ks) ->
    length l = nsum (map (fun a => length (filter (fun p => if dec (key p) a then true else false) l)) Ks).
  Proof.
    intros P K dec key Ks l hnd hin.
    rewrite (count_swap (fun a p => if dec (key p) a then true else false) Ks l).
    rewrite (nsum_map_ext _ (fun _ => 1)).
    + rewrite nsum_map_const. lia.
    + intros p hp. apply filter_eq_one; [exact hnd | apply hin; exact hp].
  Qed.

  (* A bound on every fibre of a key gives a bound on the whole. *)
  Theorem card_le_fiber_gen : forall {P K : Type} (dec : forall x y : K, {x = y} + {x <> y})
    (key : P -> K) (Ks : list K) (Om : list P) (E : P -> Prop) (Bf : nat),
    NoDup Ks -> (forall p, In p Om -> In (key p) Ks) ->
    (forall a, In a Ks -> card_le Om (fun p => key p = a /\ E p) Bf) ->
    card_le Om E (Bf * length Ks).
  Proof.
    intros P K dec key Ks Om E Bf hnd hkey hfib l hl hincl hE.
    rewrite (group_length dec key Ks l hnd (fun p hp => hkey p (hincl p hp))).
    apply nsum_map_le. intros a ha.
    apply (hfib a ha).
    + apply NoDup_filter; exact hl.
    + intros p hp. apply filter_In in hp. apply hincl; tauto.
    + intros p hp. apply filter_In in hp. destruct hp as [hp hk].
      destruct (dec (key p) a); [split; [assumption | apply hE; exact hp] | discriminate].
  Qed.

  (* The challenge space F^(m+1) as F x F^m: fibres over the first coordinate. *)
  Theorem card_le_cons : forall {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
    (lf : list A) (m : nat) (E : list A -> Prop) (Bf : nat), NoDup lf ->
    (forall r, In r lf -> card_le (all_lists lf m) (fun cs => E (r :: cs)) Bf) ->
    card_le (all_lists lf (S m)) E (Bf * length lf).
  Proof.
    intros A dec lf m E Bf hnd hfib.
    assert (odec : forall x y : option A, {x = y} + {x <> y}) by (decide equality).
    assert (h := card_le_fiber_gen odec (@hd_error A) (map Some lf) (all_lists lf (S m)) E Bf).
    rewrite length_map in h. apply h.
    + apply NoDup_map_NoDup_ForallPairs; [| exact hnd]. intros x y _ _ e. inversion e; reflexivity.
    + intros p hp. apply all_lists_In in hp. destruct hp as [hlen hall].
      destruct p as [| r cs]; [discriminate |]. inversion hall; subst. cbn. apply in_map; assumption.
    + intros a ha. apply in_map_iff in ha. destruct ha as (r & <- & hr).
      intros l hl hincl hE.
      assert (hsub : incl l (map (cons r) (all_lists lf m))).
      { intros p hp. destruct (hE p hp) as [hk _]. specialize (hincl p hp).
        apply all_lists_In in hincl. destruct hincl as [hlen hall].
        destruct p as [| r' cs]; [discriminate |]. cbn in hk. inversion hk; subst.
        apply in_map. apply all_lists_In. inversion hall; subst. split; [cbn in hlen; lia | assumption]. }
      destruct (preimage_list (cons r) (all_lists lf m) l hsub) as (l' & e & hi). subst l.
      rewrite length_map. apply (hfib r hr); [exact (NoDup_map_inv _ l' hl) | exact hi |].
      intros cs hcs. apply (hE (r :: cs)). apply in_map; exact hcs.
  Qed.

  (* An event that only depends on the first coordinate. *)
  Theorem card_le_head : forall {A : Type} (dec : forall x y : A, {x = y} + {x <> y})
    (lf : list A) (m : nat) (E1 : A -> Prop) (B : nat), NoDup lf ->
    card_le lf E1 B ->
    card_le (all_lists lf (S m)) (fun p => match p with r :: _ => E1 r | [] => False end) (B * length lf ^ m).
  Proof.
    intros A dec lf m E1 B hnd h1.
    assert (ldec : forall x y : list A, {x = y} + {x <> y}) by (apply list_eq_dec; exact dec).
    assert (h := card_le_fiber_gen ldec (@tl A) (all_lists lf m) (all_lists lf (S m))
                   (fun p => match p with r :: _ => E1 r | [] => False end) B).
    rewrite all_lists_length in h. apply h.
    + apply all_lists_NoDup; exact hnd.
    + intros p hp. apply all_lists_In in hp. destruct hp as [hlen hall].
      destruct p as [| r cs]; [discriminate |]. inversion hall; subst. cbn.
      apply all_lists_In; split; [cbn in hlen; lia | assumption].
    + intros t _ l hl hincl hE.
      assert (hsub : incl l (map (fun r => r :: t) lf)).
      { intros p hp. destruct (hE p hp) as [hk _]. specialize (hincl p hp).
        apply all_lists_In in hincl. destruct hincl as [hlen hall].
        destruct p as [| r cs]; [discriminate |]. cbn in hk. subst cs.
        apply (in_map (fun r0 => r0 :: t)). inversion hall; assumption. }
      destruct (preimage_list (fun r => r :: t) lf l hsub) as (l' & e & hi). subst l.
      rewrite length_map. apply h1; [exact (NoDup_map_inv _ l' hl) | exact hi |].
      intros r hr. destruct (hE (r :: t) (in_map (fun r0 => r0 :: t) _ _ hr)) as [_ he]. exact he.
  Qed.

  (* Products of two challenge spaces. *)
  Theorem card_le_prod_fiber : forall {A B : Type} (decA : forall x y : A, {x = y} + {x <> y})
    (OA : list A) (OB : list B) (E : A * B -> Prop) (Bf : nat), NoDup OA ->
    (forall a, In a OA -> card_le OB (fun b => E (a, b)) Bf) ->
    card_le (list_prod OA OB) E (Bf * length OA).
  Proof.
    intros A B decA OA OB E Bf hnd hfib.
    apply (card_le_fiber_gen decA (@fst A B) OA (list_prod OA OB) E Bf hnd).
    + intros [a b] hp. apply in_prod_iff in hp. tauto.
    + intros a ha l hl hincl hE.
      assert (hsub : incl l (map (pair a) OB)).
      { intros [a' b] hp. destruct (hE _ hp) as [hk _]. cbn in hk. subst a'.
        apply in_map. specialize (hincl _ hp). apply in_prod_iff in hincl. tauto. }
      destruct (preimage_list (pair a) OB l hsub) as (l' & e & hi). subst l.
      rewrite length_map. apply (hfib a ha); [exact (NoDup_map_inv _ l' hl) | exact hi |].
      intros b hb. exact (proj2 (hE (a, b) (in_map (pair a) _ _ hb))).
  Qed.

  Theorem card_le_prod_cyl : forall {A B : Type} (decB : forall x y : B, {x = y} + {x <> y})
    (OA : list A) (OB : list B) (E1 : A -> Prop) (K : nat), NoDup OB ->
    card_le OA E1 K ->
    card_le (list_prod OA OB) (fun p => E1 (fst p)) (K * length OB).
  Proof.
    intros A B decB OA OB E1 K hnd h1.
    apply (card_le_fiber_gen decB (@snd A B) OB (list_prod OA OB) (fun p => E1 (fst p)) K hnd).
    + intros [a b] hp. apply in_prod_iff in hp. tauto.
    + intros b hb l hl hincl hE.
      assert (hsub : incl l (map (fun a => (a, b)) OA)).
      { intros [a b'] hp. destruct (hE _ hp) as [hk _]. cbn in hk. subst b'.
        apply (in_map (fun a0 => (a0, b))). specialize (hincl _ hp). apply in_prod_iff in hincl. tauto. }
      destruct (preimage_list (fun a => (a, b)) OA l hsub) as (l' & e & hi). subst l.
      rewrite length_map. apply h1; [exact (NoDup_map_inv _ l' hl) | exact hi |].
      intros a ha. exact (proj2 (hE (a, b) (in_map (fun a0 => (a0, b)) _ _ ha))).
  Qed.

  (* Joining two layers of a protocol. The outer challenges w are split by
     a decidable property D: where D holds, acceptance of the whole implies
     the inner event Ideal; where it fails, the fibre over w is small. *)
  Theorem card_join : forall {W O : Type} (decW : forall x y : W, {x = y} + {x <> y})
    (decO : forall x y : O, {x = y} + {x <> y}) (Om : list W) (Oo : list O)
    (Ideal D : W -> Prop) (R : W -> O -> Prop) (Bm Bo : nat),
    NoDup Om -> NoDup Oo ->
    (forall w, D w \/ ~ D w) ->
    card_le Om Ideal Bm ->
    (forall w o, In w Om -> D w -> R w o -> Ideal w) ->
    (forall w, In w Om -> ~ D w -> card_le Oo (R w) Bo) ->
    card_le (list_prod Om Oo) (fun x => R (fst x) (snd x)) (Bm * length Oo + Bo * length Om).
  Proof.
    intros W O decW decO Om Oo Ideal D R Bm Bo hOm hOo hD hI h1 h2.
    pose proof (card_le_prod_cyl decO Om Oo Ideal Bm hOo hI) as hc.
    assert (hf : card_le (list_prod Om Oo) (fun x => ~ D (fst x) /\ R (fst x) (snd x)) (Bo * length Om)).
    { apply (card_le_prod_fiber decW Om Oo (fun x => ~ D (fst x) /\ R (fst x) (snd x)) Bo hOm).
      intros w hw. cbn [fst snd]. destruct (hD w) as [d | d].
      + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros o _ [hn _]. apply hn. exact d.
      + apply (card_le_mono _ _ _ _ _ (fun o _ hh => proj2 hh) (le_n _) (h2 w hw d)). }
    pose proof (card_le_or _ _ _ _ _ hc hf) as hor.
    eapply card_le_mono; [ | apply le_n | exact hor].
    intros [w o] hin hr. cbn [fst snd] in *. apply in_prod_iff in hin. destruct hin as [hw _].
    destruct (hD w) as [d | d]; [left; exact (h1 w o hw d hr) | right; split; assumption].
  Qed.

  (* The space of column queries: tuples of t distinct columns among n. *)
  Definition qspace (n t : nat) : list (list nat) := filter nodupb (all_lists (seq 0 n) t).

  Lemma qspace_NoDup : forall n t, NoDup (qspace n t).
  Proof. intros n t. apply NoDup_filter, all_lists_NoDup, seq_NoDup. Qed.

  Lemma qspace_length : forall n t, length (qspace n t) = fall n t.
  Proof.
    intros n t. unfold qspace.
    rewrite (filter_ext nodupb (fun xs => nodupb xs && forallb (fun _ => true) xs)).
    + rewrite (distinct_pass_count (fun _ => true) (seq 0 n) (seq_NoDup n 0) t).
      rewrite (filter_const_length true), length_seq. reflexivity.
    + intro xs. assert (h : forallb (fun _ : nat => true) xs = true) by (apply forallb_forall; reflexivity).
      rewrite h, andb_true_r. reflexivity.
  Qed.

  (* If fewer than n - e columns pass a check, t distinct queries all pass
     for at most fall (n - e - 1) t of the fall n t tuples. *)
  Theorem query_card : forall (pass : nat -> bool) (n e t : nat),
    length (filter pass (seq 0 n)) + e < n ->
    card_le (qspace n t) (fun J => forall j, In j J -> pass j = true) (fall (n - e - 1) t).
  Proof.
    intros pass n e t hp.
    apply (card_le_of_filter (list_eq_dec Nat.eq_dec)). intros b hb.
    unfold qspace. rewrite filter_filter_length.
    eapply Nat.le_trans; [apply (filter_length_imp _ (fun xs => nodupb xs && forallb pass xs)) |].
    + intros J hJ. apply andb_true_iff in hJ. destruct hJ as [h1 h2]. rewrite h1. cbn.
      apply forallb_forall. intros j hj. exact (hb J h2 j hj).
    + rewrite (distinct_pass_count pass (seq 0 n) (seq_NoDup n 0) t). apply fall_mono. lia.
  Qed.

End Card.
