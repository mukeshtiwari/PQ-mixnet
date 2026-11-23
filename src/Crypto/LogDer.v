(* The logarithmic-derivative lemma (paper, Lemma 5.1), in counting form
   and with the paper's bound.

   Setting. A challenge is a point p = alpha :: c of F^(n+1). An item of a
   multiset is a linear form a = (-1) :: a' of length n+1, with value
   dot a p = dot a' c - alpha. In the protocol a' = coeff(ciphertext) ++ [tag]
   and c = rho ++ [beta].

   Theorem logder_count. Let S and T be lists of tau forms that are not
   permutations of each other, and assume 1, 2, .., tau are non-zero in F.
   Then the number of points p at which all denominators are non-zero and

       sum_{a in S} 1 / dot a p  =  sum_{a in T} 1 / dot a p

   is at most (2 tau - 1) * |F|^n, out of |F|^(n+1) points.

   Proof idea (no multivariate polynomials). With D the distinct forms and
   mu the net multiplicities, the event implies Phi(p) = 0 for
       Phi(p) = sum_{a in D} mu_a * prod_{b in D, b <> a} dot b p.
   Phi is homogeneous of degree |D| - 1, so along any line p + t * dir it
   is a univariate polynomial in t whose top coefficient is Phi(dir). We
   exhibit a direction with Phi(dir) <> 0; then every line parallel to dir
   contains at most |D| - 1 zeros (roots_bound), and averaging over the
   translations t |-> p + t * dir (shift_count) gives the bound. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting.
Import ListNotations.

Section LogDer.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation peval := (@eval F zero add mul).
  Local Notation pz := (@pzero F zero).

  (* ------------------------------------------------------------------ *)
  (* Field facts *)

  Lemma mul_nonzero : forall x y : F, x <> zero -> y <> zero -> x * y <> zero.
  Proof.
    intros x y hx hy e. apply hy.
    assert (h : y = inv x * (x * y)) by (field; exact hx).
    rewrite h, e; field; exact hx.
  Qed.

  Fixpoint nF (k : nat) : F :=
    match k with
    | 0 => zero
    | S k' => one + nF k'
    end.

  Lemma nF_add : forall i j, nF (i + j)%nat = nF i + nF j.
  Proof. induction i as [| i ih]; intro j; cbn; [field | rewrite ih; field]. Qed.

  Lemma nF_inj : forall tau, (forall k, (0 < k <= tau)%nat -> nF k <> zero) ->
    forall i j, (i <= tau)%nat -> (j <= tau)%nat -> nF i = nF j -> i = j.
  Proof.
    intros tau hc.
    assert (hlt : forall i j, (i < j)%nat -> (j <= tau)%nat -> nF i <> nF j).
    { intros i j hij hj e. apply (hc (j - i)%nat ltac:(lia)).
      assert (h : nF j = nF (j - i)%nat + nF i) by (rewrite <-nF_add; f_equal; lia).
      assert (h2 : nF (j - i)%nat = nF j - nF i) by (rewrite h; field).
      rewrite h2, e; field. }
    intros i j hi hj e.
    destruct (Nat.lt_trichotomy i j) as [h | [h | h]]; [| exact h |].
    + exfalso; exact (hlt i j h hj e).
    + exfalso; exact (hlt j i h hi (eq_sym e)).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Sums and products over lists *)

  Fixpoint fsum (l : list F) : F :=
    match l with
    | [] => zero
    | x :: l' => x + fsum l'
    end.

  Fixpoint fprod (l : list F) : F :=
    match l with
    | [] => one
    | x :: l' => x * fprod l'
    end.

  Lemma fsum_map_ext : forall {A : Type} (g h : A -> F) (l : list A),
    (forall a, In a l -> g a = h a) -> fsum (map g l) = fsum (map h l).
  Proof.
    induction l as [| a l ih]; intro e; cbn; [reflexivity |].
    rewrite (e a (or_introl eq_refl)), ih; [reflexivity |].
    intros x hx; apply e; right; exact hx.
  Qed.

  Lemma fsum_map_add : forall {A : Type} (g h : A -> F) (l : list A),
    fsum (map (fun a => g a + h a) l) = fsum (map g l) + fsum (map h l).
  Proof. induction l as [| a l ih]; cbn; [field | rewrite ih; field]. Qed.

  Lemma fsum_map_sub : forall {A : Type} (g h : A -> F) (l : list A),
    fsum (map (fun a => g a - h a) l) = fsum (map g l) - fsum (map h l).
  Proof. induction l as [| a l ih]; cbn; [field | rewrite ih; field]. Qed.

  Lemma fsum_map_zero : forall {A : Type} (l : list A), fsum (map (fun _ => zero) l) = zero.
  Proof. induction l as [| a l ih]; cbn; [reflexivity | rewrite ih; field]. Qed.

  Lemma fsum_map_zero_ext : forall {A : Type} (g : A -> F) (l : list A),
    (forall a, In a l -> g a = zero) -> fsum (map g l) = zero.
  Proof.
    intros A g l h. rewrite (fsum_map_ext g (fun _ => zero) l h). apply fsum_map_zero.
  Qed.

  Section Counts.
    Context {A : Type} (dec : forall x y : A, {x = y} + {x <> y}).

    Lemma fsum_indicator : forall (g : A -> F) (x : A) (D : list A),
      NoDup D -> In x D ->
      fsum (map (fun a => (if dec x a then one else zero) * g a) D) = g x.
    Proof.
      intros g x; induction D as [| b D ih]; intros hnd hin; [contradiction |].
      inversion hnd as [| ? ? hb hnd']; subst. cbn.
      destruct (dec x b) as [-> | hne].
      + assert (hz : fsum (map (fun a => (if dec b a then one else zero) * g a) D) = zero).
        { apply fsum_map_zero_ext; intros a ha.
          destruct (dec b a) as [-> | _]; [contradiction | field]. }
        rewrite hz; field.
      + destruct hin as [-> | hin]; [contradiction |].
        rewrite (ih hnd' hin); field.
    Qed.

    (* A sum over a list is a sum over its distinct elements, weighted by
       the number of occurrences. *)
    Lemma fsum_count : forall (g : A -> F) (l D : list A),
      NoDup D -> incl l D ->
      fsum (map g l) = fsum (map (fun a => nF (count_occ dec l a) * g a) D).
    Proof.
      intros g; induction l as [| x l ih]; intros D hnd hincl.
      + cbn. symmetry. apply fsum_map_zero_ext; intros; field.
      + cbn [map fsum].
        rewrite (ih D hnd (fun a ha => hincl a (or_intror ha))).
        rewrite <-(fsum_indicator g x D hnd (hincl x (or_introl eq_refl))).
        rewrite <-fsum_map_add. apply fsum_map_ext; intros a _.
        cbn. destruct (dec x a); cbn; field.
    Qed.
  End Counts.

  (* PP g l is the product of the g a; SS w g l is the sum over a in l of
     w a times the product of the g b over the other b. *)
  Definition PP {A : Type} (g : A -> F) (l : list A) : F := fprod (map g l).

  Fixpoint SS {A : Type} (w g : A -> F) (l : list A) : F :=
    match l with
    | [] => zero
    | a :: l' => w a * PP g l' + g a * SS w g l'
    end.

  Lemma PP_ext : forall {A : Type} (g h : A -> F) (l : list A),
    (forall a, g a = h a) -> PP g l = PP h l.
  Proof.
    intros A g h l e; unfold PP; induction l as [| a l ih]; cbn; [reflexivity | rewrite e, ih; reflexivity].
  Qed.

  Lemma SS_ext : forall {A : Type} (w g h : A -> F) (l : list A),
    (forall a, g a = h a) -> SS w g l = SS w h l.
  Proof.
    intros A w g h l e; induction l as [| a l ih]; cbn; [reflexivity |].
    rewrite e, ih, (PP_ext g h l e); reflexivity.
  Qed.

  Lemma PP_nonzero : forall {A : Type} (g : A -> F) (l : list A),
    (forall a, In a l -> g a <> zero) -> PP g l <> zero.
  Proof.
    intros A g; unfold PP; induction l as [| a l ih]; intro h; cbn.
    + intro e; exact (@zero_neq_one F eq zero one _ (eq_sym e)).
    + apply mul_nonzero; [apply h; left; reflexivity | apply ih; intros x hx; apply h; right; exact hx].
  Qed.

  Lemma PP_zero : forall {A : Type} (g : A -> F) (l : list A) (a : A),
    In a l -> g a = zero -> PP g l = zero.
  Proof.
    intros A g; unfold PP; induction l as [| b l ih]; intros a hin hz; [contradiction |]; cbn.
    destruct hin as [-> | hin]; [rewrite hz; field | rewrite (ih a hin hz); field].
  Qed.

  Lemma SS_rational : forall {A : Type} (w g : A -> F) (l : list A),
    (forall a, In a l -> g a <> zero) ->
    SS w g l = PP g l * fsum (map (fun a => w a * inv (g a)) l).
  Proof.
    intros A w g; induction l as [| a l ih]; intro h; cbn.
    + unfold PP; cbn; field.
    + rewrite (ih (fun x hx => h x (or_intror hx))).
      unfold PP; cbn. field. apply h; left; reflexivity.
  Qed.

  Lemma SS_special : forall {A : Type} (w g : A -> F) (l : list A) (s : A),
    NoDup l -> In s l -> g s = zero -> (forall b, In b l -> b <> s -> g b <> zero) ->
    w s <> zero -> SS w g l <> zero.
  Proof.
    intros A w g; induction l as [| a l ih]; intros s hnd hin hs hothers hw; [contradiction |].
    inversion hnd as [| ? ? ha hnd']; subst. cbn.
    destruct hin as [-> | hin].
    + rewrite hs.
      assert (hp : PP g l <> zero).
      { apply PP_nonzero; intros b hb; apply hothers; [right; exact hb |].
        intro e; subst; contradiction. }
      intro e. apply (mul_nonzero (w s) (PP g l) hw hp). rewrite <-e; field.
    + rewrite (PP_zero g l s hin hs).
      assert (hga : g a <> zero).
      { apply hothers; [left; reflexivity | intro e; subst; contradiction]. }
      assert (hss : SS w g l <> zero).
      { apply (ih s hnd' hin hs); [| exact hw]. intros b hb; apply hothers; right; exact hb. }
      intro e. apply (mul_nonzero (g a) (SS w g l) hga hss). rewrite <-e; field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Univariate polynomials: (u + v t) * q, sums, and the polynomials of
     PP and SS along a line *)

  Fixpoint mul_lin (u v : F) (q : list F) (c : F) : list F :=
    match q with
    | [] => [c]
    | x :: q' => (u * x + c) :: mul_lin u v q' (v * x)
    end.

  Lemma eval_mul_lin : forall u v q c t,
    peval (mul_lin u v q c) t = c + (u + v * t) * peval q t.
  Proof.
    intros u v; induction q as [| x q ih]; intros c t; cbn.
    + field.
    + rewrite ih; field.
  Qed.

  Lemma length_mul_lin : forall u v q c, length (mul_lin u v q c) = S (length q).
  Proof. intros u v; induction q as [| x q ih]; intro c; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Lemma nth_mul_lin : forall u v q c k,
    nth k (mul_lin u v q c) zero =
    u * nth k q zero + match k with 0 => c | S k' => v * nth k' q zero end.
  Proof.
    intros u v; induction q as [| x q ih]; intros c k.
    + destruct k as [| k]; cbn; [field |]. destruct k; cbn; field.
    + destruct k as [| k]; cbn [mul_lin nth]; [field |].
      rewrite ih. destruct k; cbn; field.
  Qed.

  Fixpoint padd (p q : list F) : list F :=
    match p, q with
    | [], _ => q
    | _, [] => p
    | x :: p', y :: q' => (x + y) :: padd p' q'
    end.

  Lemma eval_padd : forall p q t, peval (padd p q) t = peval p t + peval q t.
  Proof.
    induction p as [| x p ih]; intros q t; cbn; [field |].
    destruct q as [| y q]; cbn; [field | rewrite ih; field].
  Qed.

  Lemma nth_padd : forall p q k, nth k (padd p q) zero = nth k p zero + nth k q zero.
  Proof.
    induction p as [| x p ih]; intros q k; cbn.
    + destruct k; field.
    + destruct q as [| y q]; cbn.
      - destruct k; field.
      - destruct k as [| k]; [reflexivity | apply ih].
  Qed.

  Lemma length_padd : forall p q, length (padd p q) = Nat.max (length p) (length q).
  Proof.
    induction p as [| x p ih]; intro q; cbn; [reflexivity |].
    destruct q as [| y q]; cbn; [reflexivity | rewrite ih; reflexivity].
  Qed.

  Definition pscale (c : F) (p : list F) : list F := map (mul c) p.

  Lemma eval_pscale : forall c p t, peval (pscale c p) t = c * peval p t.
  Proof. intro c; induction p as [| x p ih]; intro t; cbn; [field | rewrite ih; field]. Qed.

  Lemma nth_pscale : forall c p k, nth k (pscale c p) zero = c * nth k p zero.
  Proof.
    intro c; induction p as [| x p ih]; intro k; cbn.
    + destruct k; field.
    + destruct k as [| k]; [reflexivity | apply ih].
  Qed.

  Lemma length_pscale : forall c p, length (pscale c p) = length p.
  Proof. intros; unfold pscale; apply length_map. Qed.

  Lemma nth_nonzero_not_pzero : forall p k, nth k p zero <> zero -> ~ pz p.
  Proof.
    induction p as [| x p ih]; intros k h hz.
    + destruct k; apply h; reflexivity.
    + inversion hz; subst. destruct k as [| k]; [apply h; reflexivity | exact (ih k h H2)].
  Qed.

  Section LinePolys.
    Context {A : Type} (w u v : A -> F).

    Fixpoint prodlin (l : list A) : list F :=
      match l with
      | [] => [one]
      | a :: l' => mul_lin (u a) (v a) (prodlin l') zero
      end.

    Lemma eval_prodlin : forall l t, peval (prodlin l) t = PP (fun a => u a + v a * t) l.
    Proof.
      induction l as [| a l ih]; intro t; unfold PP; cbn.
      + field.
      + rewrite eval_mul_lin, ih; unfold PP; field.
    Qed.

    Lemma length_prodlin : forall l, length (prodlin l) = S (length l).
    Proof. induction l as [| a l ih]; cbn; [reflexivity | rewrite length_mul_lin, ih; reflexivity]. Qed.

    Lemma nth_prodlin_top : forall l, nth (length l) (prodlin l) zero = PP v l.
    Proof.
      induction l as [| a l ih]; unfold PP; cbn [prodlin length map fprod nth].
      + field.
      + rewrite nth_mul_lin, ih.
        rewrite (nth_overflow (prodlin l) zero) by (rewrite length_prodlin; lia).
        unfold PP; field.
    Qed.

    Fixpoint SSp (l : list A) : list F :=
      match l with
      | [] => []
      | a :: l' => padd (pscale (w a) (prodlin l')) (mul_lin (u a) (v a) (SSp l') zero)
      end.

    Lemma eval_SSp : forall l t, peval (SSp l) t = SS w (fun a => u a + v a * t) l.
    Proof.
      induction l as [| a l ih]; intro t; cbn [SSp SS].
      + reflexivity.
      + rewrite eval_padd, eval_pscale, eval_mul_lin, eval_prodlin, ih; field.
    Qed.

    Lemma length_SSp : forall l, (length (SSp l) <= length l)%nat.
    Proof.
      induction l as [| a l ih]; cbn [SSp length]; [lia |].
      rewrite length_padd, length_pscale, length_prodlin, length_mul_lin; lia.
    Qed.

    Lemma nth_SSp_top : forall l, l <> [] -> nth (length l - 1) (SSp l) zero = SS w v l.
    Proof.
      induction l as [| a l ih]; intro hne; [contradiction |].
      cbn [SSp SS length]. replace (S (length l) - 1)%nat with (length l) by lia.
      rewrite nth_padd, nth_pscale, nth_prodlin_top, nth_mul_lin.
      rewrite (nth_overflow (SSp l) zero) by apply length_SSp.
      destruct l as [| b l'].
      + cbn; field.
      + cbn [length]. specialize (ih ltac:(discriminate)).
        cbn [length] in ih. replace (S (length l') - 1)%nat with (length l') in ih by lia.
        rewrite ih; field.
    Qed.
  End LinePolys.

  (* ------------------------------------------------------------------ *)
  (* Vectors as lists: inner product, translation along a direction *)

  Fixpoint dot (a p : list F) : F :=
    match a, p with
    | x :: a', y :: p' => x * y + dot a' p'
    | _, _ => zero
    end.

  Fixpoint vadd (p q : list F) : list F :=
    match p, q with
    | x :: p', y :: q' => (x + y) :: vadd p' q'
    | _, _ => []
    end.

  Fixpoint vsub (p q : list F) : list F :=
    match p, q with
    | x :: p', y :: q' => (x - y) :: vsub p' q'
    | _, _ => []
    end.

  Definition shift (d : list F) (t : F) (p : list F) : list F := vadd p (map (mul t) d).

  Lemma shift_length : forall d t p, length p = length d -> length (shift d t p) = length p.
  Proof.
    unfold shift; induction d as [| z d ih]; intros t p hl; destruct p as [| y p]; cbn in *; try lia.
    rewrite (ih t p); lia.
  Qed.

  Lemma dot_shift : forall a d t p, length p = length d ->
    dot a (shift d t p) = dot a p + dot a d * t.
  Proof.
    unfold shift; induction a as [| x a ih]; intros d t p hl.
    + destruct p, d; cbn; field.
    + destruct p as [| y p], d as [| z d]; cbn in *; try lia; [field |].
      rewrite (ih d t p) by lia. field.
  Qed.

  Lemma shift_inj : forall d t p q, length p = length d -> length q = length d ->
    shift d t p = shift d t q -> p = q.
  Proof.
    unfold shift; induction d as [| z d ih]; intros t p q hp hq e;
      destruct p as [| x p], q as [| y q]; cbn in *; try lia; [reflexivity |].
    inversion e as [[e1 e2]]. f_equal.
    + assert (h : x = (x + t * z) - t * z) by field. rewrite h, e1; field.
    + apply (ih t); [lia | lia | exact e2].
  Qed.

  Lemma vsub_length : forall p q, length p = length q -> length (vsub p q) = length p.
  Proof.
    induction p as [| x p ih]; intros q hl; destruct q as [| y q]; cbn in *; try lia.
    rewrite ih; lia.
  Qed.

  Lemma dot_vsub : forall b a c, length b = length a ->
    dot (vsub b a) c = dot b c - dot a c.
  Proof.
    induction b as [| x b ih]; intros a c hl; destruct a as [| y a]; cbn in *; try lia.
    + destruct c; field.
    + destruct c as [| z c]; [field |]. rewrite ih by lia. field.
  Qed.

  Definition allzero (g : list F) : bool := forallb (fun x => if Fdec x zero then true else false) g.

  Lemma allzero_spec : forall g, allzero g = true <-> Forall (fun x => x = zero) g.
  Proof.
    intro g; unfold allzero; rewrite forallb_forall, Forall_forall; split; intros h x hx.
    + specialize (h x hx); destruct (Fdec x zero); [assumption | discriminate].
    + rewrite (h x hx); destruct (Fdec zero zero); [reflexivity | contradiction].
  Qed.

  Lemma vsub_nonzero : forall b a, length b = length a -> b <> a -> allzero (vsub b a) = false.
  Proof.
    induction b as [| x b ih]; intros a hl hne; destruct a as [| y a]; cbn in *; try lia.
    + contradiction.
    + destruct (Fdec (x - y) zero) as [e | e]; [| reflexivity]. cbn.
      apply ih; [lia |]. intro e2; apply hne; f_equal; [| exact e2].
      assert (h : x = (x - y) + y) by field. rewrite h, e; field.
  Qed.

  (* Fewer than |lf| non-zero linear forms have a common point at which
     none of them vanishes. *)
  Lemma forms_common_nonzero : forall (lf : list F), NoDup lf ->
    forall (m : nat) (gs : list (list F)),
    (forall g, In g gs -> length g = m /\ allzero g = false) ->
    (length gs < length lf)%nat ->
    exists c, length c = m /\ forall g, In g gs -> dot g c <> zero.
  Proof.
    intros lf hnd; induction m as [| m ih]; intros gs hgs hlen.
    + exists []; split; [reflexivity |]. intros g hg.
      destruct (hgs g hg) as [hl hz]. destruct g; [cbn in hz; discriminate | discriminate].
    + set (keep := filter (fun g => negb (allzero (tl g))) gs).
      assert (hk : forall g, In g (map (@tl F) keep) -> length g = m /\ allzero g = false).
      { intros t ht. apply in_map_iff in ht; destruct ht as (g & <- & hg).
        apply filter_In in hg; destruct hg as [hg hnz].
        destruct (hgs g hg) as [hl _]. split.
        + destruct g; cbn in *; lia.
        + destruct (allzero (tl g)); [discriminate | reflexivity]. }
      assert (hkl : (length (map (@tl F) keep) < length lf)%nat).
      { rewrite length_map. unfold keep.
        pose proof (filter_length_le (fun g => negb (allzero (tl g))) gs). lia. }
      destruct (ih (map (@tl F) keep) hk hkl) as (c' & hc' & hgood).
      set (bad := map (fun g => opp (dot (tl g) c') * inv (hd zero g)) gs).
      assert (hbl : (length bad < length lf)%nat) by (unfold bad; rewrite length_map; exact hlen).
      destruct (@pigeonhole_notin F Fdec lf bad hnd hbl) as (x & _ & hx).
      exists (x :: c'); split; [cbn; lia |].
      intros g hg e. destruct (hgs g hg) as [hl hnz].
      destruct g as [| h t]; [discriminate |]. cbn in e, hl.
      destruct (Fdec h zero) as [hh | hh].
      - subst h. assert (e' : dot t c' = zero) by (rewrite <-e; field).
        cbn in hnz. destruct (Fdec zero zero) as [_ | n]; [| contradiction]. cbn in hnz.
        apply (hgood t); [| exact e'].
        apply in_map_iff; exists (zero :: t); split; [reflexivity |].
        apply filter_In; split; [exact hg | cbn; rewrite hnz; reflexivity].
      - apply hx. unfold bad. apply in_map_iff. exists (h :: t); split; [| exact hg]. cbn.
        assert (e1 : h * x = opp (dot t c')).
        { assert (h1 : h * x = (h * x + dot t c') - dot t c') by field. rewrite h1, e; field. }
        rewrite <-e1; field; exact hh.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The lemma *)

  Lemma nodup_length_le : forall {A : Type} (dec : forall x y : A, {x = y} + {x <> y}) (l : list A),
    (length (nodup dec l) <= length l)%nat.
  Proof.
    intros A dec; induction l as [| a l ih]; cbn; [lia |].
    destruct (in_dec dec a l); cbn; lia.
  Qed.

  Theorem logder_count : forall (lf : list F), NoDup lf -> (forall x, In x lf) ->
    forall (n tau : nat) (S T : list (list F)) (bad : list F -> bool),
    length S = tau -> length T = tau ->
    (forall a, In a (S ++ T) -> exists a', a = opp one :: a' /\ length a' = n) ->
    (forall k, (0 < k <= tau)%nat -> nF k <> zero) ->
    ~ Permutation S T ->
    (forall p, bad p = true ->
       (forall a, In a (S ++ T) -> dot a p <> zero) /\
       fsum (map (fun a => inv (dot a p)) S) = fsum (map (fun a => inv (dot a p)) T)) ->
    (length (filter bad (all_lists lf (Datatypes.S n))) <= (2 * tau - 1) * length lf ^ n)%nat.
  Proof.
    intros lf hnd hall n tau S T bad hS hT hforms hchar hnp hbad.
    set (ldec := list_eq_dec Fdec).
    set (D := nodup ldec (S ++ T)).
    assert (hDnd : NoDup D) by apply NoDup_nodup.
    assert (hDin : forall a, In a D <-> In a (S ++ T)) by (intro a; apply nodup_In).
    assert (hDlen : (length D <= 2 * tau)%nat).
    { unfold D. pose proof (nodup_length_le ldec (S ++ T)) as h. rewrite length_app in h. lia. }
    (* a form with different multiplicities *)
    assert (hex : exists s, In s D /\ count_occ ldec S s <> count_occ ldec T s).
    { destruct (Exists_dec (fun a => count_occ ldec S a <> count_occ ldec T a) D) as [h | h].
      + intro a. destruct (Nat.eq_dec (count_occ ldec S a) (count_occ ldec T a)); [right | left]; tauto.
      + apply Exists_exists in h; exact h.
      + exfalso; apply hnp. apply (Permutation_count_occ ldec). intro a.
        destruct (in_dec ldec a D) as [i | i].
        - destruct (Nat.eq_dec (count_occ ldec S a) (count_occ ldec T a)) as [e | e]; [exact e |].
          exfalso; apply h; apply Exists_exists; exists a; split; assumption.
        - assert (hS0 : ~ In a S) by (intro j; apply i, hDin, in_or_app; left; exact j).
          assert (hT0 : ~ In a T) by (intro j; apply i, hDin, in_or_app; right; exact j).
          apply (count_occ_not_In ldec) in hS0. apply (count_occ_not_In ldec) in hT0.
          rewrite hS0, hT0; reflexivity. }
    destruct hex as (s & hsD & hsne).
    set (mu := fun a => nF (count_occ ldec S a) - nF (count_occ ldec T a)).
    assert (hmu : mu s <> zero).
    { unfold mu; intro e. apply hsne. apply (nF_inj tau hchar).
      + rewrite <-hS; apply count_occ_bound.
      + rewrite <-hT; apply count_occ_bound.
      + assert (h : nF (count_occ ldec S s) = (nF (count_occ ldec S s) - nF (count_occ ldec T s)) + nF (count_occ ldec T s)) by field.
        rewrite h, e; field. }
    (* the event implies a zero of Phi *)
    assert (hPhi : forall p, bad p = true -> SS mu (fun a => dot a p) D = zero).
    { intros p hp. destruct (hbad p hp) as [hden hsum].
      rewrite SS_rational by (intros a ha; apply hden, hDin; exact ha).
      assert (hz : fsum (map (fun a => mu a * inv (dot a p)) D) = zero).
      { unfold mu.
        rewrite (fsum_map_ext _ (fun a => nF (count_occ ldec S a) * inv (dot a p) - nF (count_occ ldec T a) * inv (dot a p)))
          by (intros a ha; field; apply hden, hDin; exact ha).
        rewrite fsum_map_sub.
        rewrite <-(fsum_count ldec (fun a => inv (dot a p)) S D hDnd)
          by (intros a ha; apply hDin, in_or_app; left; exact ha).
        rewrite <-(fsum_count ldec (fun a => inv (dot a p)) T D hDnd)
          by (intros a ha; apply hDin, in_or_app; right; exact ha).
        rewrite hsum; field. }
      rewrite hz; field. }
    assert (hDpos : (1 <= length D)%nat) by (destruct D; [contradiction | cbn; lia]).
    destruct (le_lt_dec (length lf) (length D - 1)) as [hsmall | hbig].
    { (* trivial case: the bound exceeds the number of points *)
      pose proof (filter_length_le bad (all_lists lf (Datatypes.S n))) as h.
      rewrite all_lists_length in h. cbn [Nat.pow] in h.
      assert (h2 : (length lf * length lf ^ n <= (2 * tau - 1) * length lf ^ n)%nat)
        by (apply Nat.mul_le_mono_r; lia).
      lia. }
    (* a direction at which Phi does not vanish *)
    destruct (hforms s (proj1 (hDin s) hsD)) as (s' & hs & hs'len).
    set (others := remove ldec s D).
    set (gs := map (fun b => vsub (tl b) s') others).
    assert (hgs : forall g, In g gs -> length g = n /\ allzero g = false).
    { intros g hg. apply in_map_iff in hg; destruct hg as (b & <- & hb).
      apply in_remove in hb; destruct hb as [hbD hbne].
      destruct (hforms b (proj1 (hDin b) hbD)) as (b' & hb & hb'len). subst b. cbn.
      split; [rewrite vsub_length; lia |].
      apply vsub_nonzero; [lia |]. intro e; apply hbne; rewrite hs, e; reflexivity. }
    assert (hgl : (length gs < length lf)%nat).
    { unfold gs, others. rewrite length_map.
      pose proof (remove_length_lt ldec D s hsD). lia. }
    destruct (forms_common_nonzero lf hnd n gs hgs hgl) as (c & hcl & hc).
    set (dir := dot s' c :: c).
    assert (hdirs : dot s dir = zero) by (rewrite hs; unfold dir; cbn; field).
    assert (hdiro : forall b, In b D -> b <> s -> dot b dir <> zero).
    { intros b hbD hbne.
      destruct (hforms b (proj1 (hDin b) hbD)) as (b' & hb & hb'len). subst b.
      unfold dir; cbn. intro e.
      apply (hc (vsub b' s')).
      + unfold gs. apply in_map_iff. exists (opp one :: b'); split; [reflexivity |].
        apply in_in_remove; assumption.
      + rewrite dot_vsub by lia. rewrite <-e; field. }
    assert (htop : SS mu (fun b => dot b dir) D <> zero)
      by (apply (SS_special mu (fun b => dot b dir) D s hDnd hsD hdirs hdiro hmu)).
    (* averaging over the translations along dir *)
    assert (hdl : length dir = Datatypes.S n) by (unfold dir; cbn; lia).
    assert (havg : (length (filter bad (all_lists lf (Datatypes.S n))) * length lf
                    <= (length D - 1) * length (all_lists lf (Datatypes.S n)))%nat).
    { apply (shift_count (all_lists lf (Datatypes.S n)) lf (shift dir) bad (length D - 1)).
      + apply all_lists_NoDup; exact hnd.
      + intros t x _ hx. apply all_lists_In in hx; destruct hx as [hx _].
        apply all_lists_In; split; [rewrite shift_length; lia |].
        apply Forall_forall; intros y _; apply hall.
      + intros t x y _ hx hy e.
        apply all_lists_In in hx; destruct hx as [hx _].
        apply all_lists_In in hy; destruct hy as [hy _].
        apply (shift_inj dir t); [lia | lia | exact e].
      + intros p hp. apply all_lists_In in hp; destruct hp as [hp _].
        set (q := SSp mu (fun b => dot b p) (fun b => dot b dir) D).
        assert (hq : forall t, peval q t = SS mu (fun b => dot b (shift dir t p)) D).
        { intro t. unfold q. rewrite eval_SSp. apply SS_ext; intro b.
          rewrite dot_shift by lia. reflexivity. }
        assert (hqnz : ~ pz q).
        { apply (nth_nonzero_not_pzero q (length D - 1)). unfold q.
          rewrite nth_SSp_top; [exact htop |]. intro e; rewrite e in hsD; contradiction. }
        assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf (length q) q (le_n _) hqnz
                  (filter (fun t => bad (shift dir t p)) lf)
                  (NoDup_filter _ hnd)).
        assert (hroots : forall r, In r (filter (fun t => bad (shift dir t p)) lf) -> peval q r = zero).
        { intros r hr. apply filter_In in hr; destruct hr as [_ hr].
          rewrite hq. apply hPhi; exact hr. }
        specialize (hlt hroots).
        pose proof (length_SSp mu (fun b => dot b p) (fun b => dot b dir) D) as hql. fold q in hql. lia. }
    rewrite all_lists_length in havg. cbn [Nat.pow] in havg.
    assert (hpos : (0 < length lf)%nat) by lia.
    apply (Nat.mul_le_mono_pos_r _ _ (length lf) hpos).
    assert (h3 : ((length D - 1) * (length lf * length lf ^ n) <= (2 * tau - 1) * length lf ^ n * length lf)%nat).
    { rewrite (Nat.mul_comm (length lf) (length lf ^ n)), Nat.mul_assoc.
      apply Nat.mul_le_mono_r, Nat.mul_le_mono_r; lia. }
    lia.
  Qed.

End LogDer.
