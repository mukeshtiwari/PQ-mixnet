(* Counting over finite lists: the tools behind every "probability at most
   k/|F|" statement of the development.

   A probability over a uniform challenge is stated as a count: for a
   duplicate-free list X of all challenges and a boolean event bad,
   length (filter bad X) is the number of bad challenges.

   Main results:
   - count_swap: exchange of a double count;
   - shift_count: the averaging principle. If a family of bijections
     phi t of X (t ranging over lt) sends every point x into the bad set
     for at most d values of t, then |bad| * |lt| <= d * |X|;
   - all_lists: the enumeration of the lists of length m over a list lf,
     with its membership, NoDup and length lemmas. *)

From Stdlib Require Import Utf8 List Lia Bool Permutation PeanoNat Arith.
Import ListNotations.

Section Counting.

  Fixpoint nsum (l : list nat) : nat :=
    match l with
    | [] => 0
    | x :: l' => x + nsum l'
    end.

  Lemma nsum_map_add : forall {B : Type} (g h : B -> nat) (lb : list B),
    nsum (map (fun b => g b + h b) lb) = nsum (map g lb) + nsum (map h lb).
  Proof.
    induction lb as [| b lb ih]; cbn; [reflexivity | rewrite ih; lia].
  Qed.

  Lemma nsum_indicator : forall {B : Type} (f : B -> bool) (lb : list B),
    nsum (map (fun b => if f b then 1 else 0) lb) = length (filter f lb).
  Proof.
    induction lb as [| b lb ih]; cbn; [reflexivity |].
    destruct (f b); cbn; rewrite ih; reflexivity.
  Qed.

  Lemma nsum_map_le : forall {B : Type} (g : B -> nat) (d : nat) (lb : list B),
    (forall b, In b lb -> g b <= d) -> nsum (map g lb) <= d * length lb.
  Proof.
    induction lb as [| b lb ih]; intro h; cbn; [lia |].
    specialize (ih (fun x hx => h x (or_intror hx))).
    specialize (h b (or_introl eq_refl)). lia.
  Qed.

  Lemma nsum_map_const : forall {B : Type} (c : nat) (lb : list B),
    nsum (map (fun _ => c) lb) = c * length lb.
  Proof.
    induction lb as [| b lb ih]; cbn; [lia | rewrite ih; lia].
  Qed.

  Lemma nsum_map_ext : forall {B : Type} (g h : B -> nat) (lb : list B),
    (forall b, In b lb -> g b = h b) -> nsum (map g lb) = nsum (map h lb).
  Proof.
    induction lb as [| b lb ih]; intro e; cbn; [reflexivity |].
    rewrite (e b (or_introl eq_refl)), ih; [reflexivity |].
    intros x hx; apply e; right; exact hx.
  Qed.

  (* Double counting. *)
  Lemma count_swap : forall {A B : Type} (f : A -> B -> bool) (la : list A) (lb : list B),
    nsum (map (fun a => length (filter (f a) lb)) la) =
    nsum (map (fun b => length (filter (fun a => f a b) la)) lb).
  Proof.
    induction la as [| a la ih]; intro lb; cbn.
    + induction lb as [| b lb ihb]; cbn; [reflexivity | exact ihb].
    + rewrite ih.
      rewrite <-nsum_indicator, <-nsum_map_add.
      apply nsum_map_ext; intros b _.
      destruct (f a b); cbn; reflexivity.
  Qed.

  Lemma filter_length_perm : forall {A : Type} (f : A -> bool) (l l' : list A),
    Permutation l l' -> length (filter f l) = length (filter f l').
  Proof.
    intros A f l l' hp; induction hp; cbn.
    + reflexivity.
    + destruct (f x); cbn; rewrite IHhp; reflexivity.
    + destruct (f x), (f y); cbn; reflexivity.
    + rewrite IHhp1; exact IHhp2.
  Qed.

  Lemma filter_map_length : forall {A B : Type} (f : B -> bool) (g : A -> B) (l : list A),
    length (filter f (map g l)) = length (filter (fun a => f (g a)) l).
  Proof.
    induction l as [| a l ih]; cbn; [reflexivity |].
    destruct (f (g a)); cbn; rewrite ih; reflexivity.
  Qed.

  (* A map that sends a duplicate-free list into itself injectively
     permutes it. *)
  Lemma map_self_perm : forall {A : Type} (g : A -> A) (X : list A),
    NoDup X -> (forall x, In x X -> In (g x) X) ->
    (forall x y, In x X -> In y X -> g x = g y -> x = y) ->
    Permutation (map g X) X.
  Proof.
    intros A g X hnd hcl hinj.
    apply NoDup_Permutation_bis.
    + apply NoDup_map_NoDup_ForallPairs; [| exact hnd].
      intros x y hx hy e; exact (hinj x y hx hy e).
    + rewrite length_map; lia.
    + intros y hy; apply in_map_iff in hy; destruct hy as (x & <- & hx); exact (hcl x hx).
  Qed.

  (* The averaging principle. *)
  Theorem shift_count : forall {P T : Type} (X : list P) (lt : list T)
    (phi : T -> P -> P) (bad : P -> bool) (d : nat),
    NoDup X ->
    (forall t x, In t lt -> In x X -> In (phi t x) X) ->
    (forall t x y, In t lt -> In x X -> In y X -> phi t x = phi t y -> x = y) ->
    (forall x, In x X -> length (filter (fun t => bad (phi t x)) lt) <= d) ->
    length (filter bad X) * length lt <= d * length X.
  Proof.
    intros P T X lt phi bad d hnd hcl hinj hd.
    assert (h1 : nsum (map (fun x => length (filter (fun t => bad (phi t x)) lt)) X) <= d * length X).
    { apply nsum_map_le; exact hd. }
    rewrite (count_swap (fun x t => bad (phi t x)) X lt) in h1.
    assert (h2 : nsum (map (fun t => length (filter (fun x => bad (phi t x)) X)) lt) =
                 nsum (map (fun _ : T => length (filter bad X)) lt)).
    { apply nsum_map_ext; intros t ht.
      rewrite <-(filter_map_length bad (phi t) X).
      apply filter_length_perm, map_self_perm; [exact hnd | |].
      + intros x hx; exact (hcl t x ht hx).
      + intros x y hx hy e; exact (hinj t x y ht hx hy e). }
    rewrite h2, nsum_map_const in h1. exact h1.
  Qed.

  Lemma NoDup_list_prod : forall {A B : Type} (l : list A) (l' : list B),
    NoDup l -> NoDup l' -> NoDup (list_prod l l').
  Proof.
    induction l as [| x l ih]; intros l' hl hl'; cbn; [constructor |].
    inversion hl as [| ? ? hx hl0]; subst.
    apply NoDup_app.
    + apply NoDup_map_NoDup_ForallPairs; [| exact hl'].
      intros a b _ _ e; inversion e; reflexivity.
    + apply ih; assumption.
    + intros [a b] h1 h2. apply in_map_iff in h1; destruct h1 as (b' & e & _); inversion e; subst.
      apply in_prod_iff in h2; destruct h2 as [h2 _]; contradiction.
  Qed.

  (* All lists of length m over lf. *)
  Fixpoint all_lists {A : Type} (lf : list A) (m : nat) : list (list A) :=
    match m with
    | 0 => [[]]
    | S m' => map (fun xp => fst xp :: snd xp) (list_prod lf (all_lists lf m'))
    end.

  Lemma all_lists_In : forall {A : Type} (lf : list A) (m : nat) (p : list A),
    In p (all_lists lf m) <-> length p = m /\ Forall (fun x => In x lf) p.
  Proof.
    intros A lf; induction m as [| m ih]; intro p; cbn.
    + split.
      - intros [<- | []]; split; [reflexivity | constructor].
      - intros [hl _]; left; destruct p; [reflexivity | discriminate].
    + rewrite in_map_iff; split.
      - intros ((x & p') & <- & hin). apply in_prod_iff in hin; destruct hin as [hx hp'].
        apply ih in hp'; destruct hp' as [hl hf]; cbn; split; [lia | constructor; assumption].
      - intros [hl hf]. destruct p as [| x p']; [discriminate |].
        inversion hf; subst. exists (x, p'); split; [reflexivity |].
        apply in_prod_iff; split; [assumption |]. apply ih; split; [cbn in hl; lia | assumption].
  Qed.

  Lemma all_lists_NoDup : forall {A : Type} (lf : list A) (m : nat),
    NoDup lf -> NoDup (all_lists lf m).
  Proof.
    intros A lf m hnd; induction m as [| m ih]; cbn.
    + constructor; [intros [] | constructor].
    + apply NoDup_map_NoDup_ForallPairs; [| apply NoDup_list_prod; assumption].
      intros [x p] [y q] _ _ e; cbn in e; inversion e; reflexivity.
  Qed.

  Lemma all_lists_length : forall {A : Type} (lf : list A) (m : nat),
    length (all_lists lf m) = length lf ^ m.
  Proof.
    intros A lf; induction m as [| m ih]; cbn; [reflexivity |].
    rewrite length_map, length_prod, ih; reflexivity.
  Qed.

  (* Counting over a product, one coordinate at a time. *)
  Lemma filter_list_prod_length : forall {A B : Type} (h : A * B -> bool) (la : list A) (lb : list B),
    length (filter h (list_prod la lb)) =
    nsum (map (fun a => length (filter (fun b => h (a, b)) lb)) la).
  Proof.
    induction la as [| a la ih]; intro lb; cbn; [reflexivity |].
    rewrite filter_app, length_app, ih, filter_map_length; reflexivity.
  Qed.

  Lemma filter_all_lists_S : forall {A : Type} (f : list A -> bool) (lf : list A) (m : nat),
    length (filter f (all_lists lf (S m))) =
    nsum (map (fun xs => length (filter (fun x0 => f (x0 :: xs)) lf)) (all_lists lf m)).
  Proof.
    intros A f lf m. cbn [all_lists].
    rewrite filter_map_length, filter_list_prod_length.
    exact (count_swap (fun x0 xs => f (x0 :: xs)) lf (all_lists lf m)).
  Qed.

  Lemma nsum_map_le_cases : forall {B : Type} (g : B -> nat) (P : B -> bool) (c : nat) (l : list B),
    (forall b, In b l -> (P b = true -> g b <= c) /\ (P b = false -> g b <= 1)) ->
    nsum (map g l) <= c * length (filter P l) + length l.
  Proof.
    induction l as [| b l ih]; intro h; cbn; [lia |].
    specialize (ih (fun x hx => h x (or_intror hx))).
    destruct (h b (or_introl eq_refl)) as [h1 h2].
    destruct (P b); cbn; [specialize (h1 eq_refl) | specialize (h2 eq_refl)]; lia.
  Qed.

  Lemma filter_partition_length : forall {A : Type} (f : A -> bool) (l : list A),
    length l = length (filter f l) + length (filter (fun x => negb (f x)) l).
  Proof.
    induction l as [| a l ih]; cbn; [reflexivity |]. destruct (f a); cbn; lia.
  Qed.

  Definition memb (j : nat) (E : list nat) : bool := existsb (Nat.eqb j) E.

  Lemma memb_true : forall j E, memb j E = true <-> In j E.
  Proof.
    intros j E; unfold memb; rewrite existsb_exists; split.
    + intros (x & hx & e). apply Nat.eqb_eq in e; subst; exact hx.
    + intro h; exists j; split; [exact h | apply Nat.eqb_refl].
  Qed.

  (* A duplicate-free list has at most |E| elements inside E. *)
  Lemma filter_notin_length : forall (l E : list nat), NoDup l ->
    length l <= length (filter (fun j => negb (memb j E)) l) + length E.
  Proof.
    intros l E hnd.
    rewrite (filter_partition_length (fun j => negb (memb j E)) l) at 1.
    assert (h : length (filter (fun x => negb (negb (memb x E))) l) <= length E).
    { apply NoDup_incl_length; [apply NoDup_filter; exact hnd |].
      intros j hj. apply filter_In in hj; destruct hj as [_ hj].
      apply memb_true. destruct (memb j E); [reflexivity | discriminate]. }
    lia.
  Qed.

  Lemma nsum_map_ite : forall {B : Type} (P : B -> bool) (c : nat) (l : list B),
    nsum (map (fun b => if P b then c else 0) l) = c * length (filter P l).
  Proof.
    induction l as [| b l ih]; cbn; [lia |]. destruct (P b); cbn; rewrite ih; lia.
  Qed.

  Lemma filter_const_length : forall {B : Type} (b : bool) (l : list B),
    length (filter (fun _ => b) l) = if b then length l else 0.
  Proof.
    intros B b l; destruct b; induction l as [| x l ih]; cbn; try reflexivity; rewrite ih; reflexivity.
  Qed.

  (* Tuples of t independent queries that all pass. *)
  Lemma all_pass_count : forall {A : Type} (pass : A -> bool) (l : list A) (t : nat),
    length (filter (forallb pass) (all_lists l t)) = length (filter pass l) ^ t.
  Proof.
    intros A pass l; induction t as [| t ih]; [reflexivity |].
    rewrite filter_all_lists_S.
    rewrite (nsum_map_ext _ (fun xs => if forallb pass xs then length (filter pass l) else 0)).
    + rewrite nsum_map_ite, ih. cbn [Nat.pow]. reflexivity.
    + intros xs _. cbn [forallb].
      destruct (forallb pass xs).
      - f_equal. apply filter_ext. intro a. apply andb_true_r.
      - rewrite (filter_ext (fun x0 => pass x0 && false) (fun _ => false)) by (intro a; apply andb_false_r).
        apply (filter_const_length false).
  Qed.

  Lemma filter_length_imp : forall {A : Type} (b b' : A -> bool) (l : list A),
    (forall x, b x = true -> b' x = true) -> length (filter b l) <= length (filter b' l).
  Proof.
    intros A b b' l h; induction l as [| a l ih]; cbn; [lia |].
    destruct (b a) eqn:e; [rewrite (h a e); cbn; lia | destruct (b' a); cbn; lia].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Tuples of t distinct queries (sampling without replacement) *)

  Fixpoint nodupb (xs : list nat) : bool :=
    match xs with
    | [] => true
    | x :: xs' => negb (memb x xs') && nodupb xs'
    end.

  Lemma nodupb_NoDup : forall xs, nodupb xs = true -> NoDup xs.
  Proof.
    induction xs as [| x xs ih]; intro h; [constructor |].
    cbn in h. apply andb_true_iff in h. destruct h as [h1 h2].
    constructor; [| exact (ih h2)].
    intro i. apply memb_true in i. rewrite i in h1. discriminate.
  Qed.

  Fixpoint fall (p t : nat) : nat :=
    match t with
    | 0 => 1
    | S t' => (p - t') * fall p t'
    end.

  Lemma filter_filter_length : forall {A : Type} (f g : A -> bool) (l : list A),
    length (filter f (filter g l)) = length (filter (fun x => g x && f x) l).
  Proof.
    induction l as [| a l ih]; cbn; [reflexivity |].
    destruct (g a); cbn; [destruct (f a); cbn; rewrite ih; reflexivity | exact ih].
  Qed.

  (* In a duplicate-free list lp, the elements outside a duplicate-free
     sublist xs number |lp| - |xs|. *)
  Lemma filter_outside_length : forall (lp xs : list nat), NoDup lp -> NoDup xs -> incl xs lp ->
    length (filter (fun x => negb (memb x xs)) lp) = length lp - length xs.
  Proof.
    intros lp xs hlp hxs hincl.
    pose proof (filter_partition_length (fun x => negb (memb x xs)) lp) as hp.
    assert (hin : length (filter (fun x => negb (negb (memb x xs))) lp) = length xs).
    { apply Nat.le_antisymm.
      + apply NoDup_incl_length; [apply NoDup_filter; exact hlp |].
        intros j hj. apply filter_In in hj; destruct hj as [_ hj].
        apply memb_true. destruct (memb j xs); [reflexivity | discriminate].
      + apply NoDup_incl_length; [exact hxs |].
        intros j hj. apply filter_In; split; [apply hincl; exact hj |].
        apply memb_true in hj. rewrite hj. reflexivity. }
    lia.
  Qed.

  Lemma distinct_pass_count : forall (pass : nat -> bool) (l : list nat), NoDup l -> forall t : nat,
    length (filter (fun xs => nodupb xs && forallb pass xs) (all_lists l t)) = fall (length (filter pass l)) t.
  Proof.
    intros pass l hnd; induction t as [| t ih]; [reflexivity |].
    rewrite filter_all_lists_S.
    rewrite (nsum_map_ext _ (fun xs => if nodupb xs && forallb pass xs then length (filter pass l) - t else 0)).
    + rewrite nsum_map_ite, ih. reflexivity.
    + intros xs hxs. apply all_lists_In in hxs. destruct hxs as [hlen hall].
      cbn [nodupb forallb].
      destruct (nodupb xs && forallb pass xs) eqn:eg.
      - apply andb_true_iff in eg. destruct eg as [eg1 eg2].
        rewrite (filter_ext _ (fun x0 => pass x0 && negb (memb x0 xs))).
        * rewrite <-filter_filter_length.
          rewrite filter_outside_length; [rewrite hlen; reflexivity | apply NoDup_filter; exact hnd | apply nodupb_NoDup; exact eg1 |].
          intros j hj. apply filter_In; split.
          -- rewrite Forall_forall in hall. apply hall; exact hj.
          -- rewrite forallb_forall in eg2. apply eg2; exact hj.
        * intro x0. rewrite eg1, eg2. destruct (pass x0), (memb x0 xs); reflexivity.
      - rewrite (filter_ext _ (fun _ => false)); [apply (filter_const_length false) |].
        intro x0. destruct (nodupb xs), (forallb pass xs); cbn in eg; try discriminate;
          destruct (memb x0 xs), (pass x0); reflexivity.
  Qed.

  Lemma fall_le : forall (p n t : nat), p <= n -> fall p t * n ^ t <= fall n t * p ^ t.
  Proof.
    intros p n t hpn; induction t as [| t ih]; [cbn; lia |].
    cbn [fall Nat.pow].
    assert (h1 : (p - t) * n <= (n - t) * p).
    { destruct (le_dec p t) as [h | h]; [replace (p - t) with 0 by lia; lia |].
      rewrite !Nat.mul_sub_distr_r.
      assert (h3 : t * p <= t * n) by (apply Nat.mul_le_mono_l; exact hpn).
      assert (h4 : t * n <= p * n) by (apply Nat.mul_le_mono_r; lia).
      rewrite (Nat.mul_comm n p). lia. }
    pose proof (Nat.mul_le_mono _ _ _ _ h1 ih) as h2.
    lia.
  Qed.

  Lemma fall_mono : forall (p p' t : nat), p <= p' -> fall p t <= fall p' t.
  Proof.
    intros p p' t h; induction t as [| t ih]; cbn [fall]; [lia |].
    apply Nat.mul_le_mono; [lia | exact ih].
  Qed.

  Lemma forallb_false_ex : forall {A : Type} (f : A -> bool) (l : list A),
    forallb f l = false -> exists x, In x l /\ f x = false.
  Proof.
    induction l as [| a l ih]; intro h; cbn in h; [discriminate |].
    destruct (f a) eqn:e.
    + cbn in h. destruct (ih h) as (x & hx & hf). exists x; split; [right; exact hx | exact hf].
    + exists a; split; [left; reflexivity | exact e].
  Qed.

  (* The probability that t distinct uniformly chosen columns all pass is
     at most (P / n)^t: (number of passing distinct tuples) * n^t <=
     (number of distinct tuples) * P^t. *)
  Theorem distinct_query_bound : forall (pass : nat -> bool) (l : list nat) (t : nat), NoDup l ->
    length (filter (fun xs => nodupb xs && forallb pass xs) (all_lists l t)) * length l ^ t
    <= length (filter (fun xs => nodupb xs && forallb (fun _ => true) xs) (all_lists l t))
       * length (filter pass l) ^ t.
  Proof.
    intros pass l t hnd.
    rewrite !distinct_pass_count by exact hnd.
    rewrite (filter_const_length true l).
    apply fall_le. apply filter_length_le.
  Qed.

End Counting.
