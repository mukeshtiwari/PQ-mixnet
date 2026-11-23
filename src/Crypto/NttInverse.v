(* The negacyclic adjoint through evaluations, over any field.

   nadj a rho (Negacyclic.v) is a(X^-1) * rho in F[X]/(X^N + 1). At a root z of X^N + 1 with
   inverse w, its value is a(w) * rho(z) (eval_nadj). If psi^N = -1 and omega = psi^2 has order
   exactly N, the points psi * omega^j (j < N) are N roots of X^N + 1, and a list r of N
   coefficients is recovered from its values there by the inverse transform (ntt_inverse):

     sum_j r(psi omega^j) * (omega'^i)^j = N * psi^i * r_i        (omega * omega' = 1, i < N).

   Used by ExecNadj.v to compute nadj with three NTTs instead of N^2 products. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots Counting LogDer Negacyclic.
Import ListNotations.

Section NttInverse.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation peval := (@eval F zero add mul).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation xadj := (@xadj F opp).
  Local Notation nadj := (@nadj F add mul opp).
  Local Notation pw := (@pw F one mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation nF := (@nF F zero one add).


  (* ------------------------------------------------------------------ *)
  (* powers *)

  Lemma pw_add' : forall x a b, pw x (a + b) = pw x a * pw x b.
  Proof. intros x a b; induction a as [| a ih]; cbn [Nat.add Negacyclic.pw]; [field | rewrite ih; field]. Qed.

  Lemma pw_mul_base : forall x y k, pw (x * y) k = pw x k * pw y k.
  Proof. intros x y k; induction k as [| k ih]; cbn [Negacyclic.pw]; [field | rewrite ih; field]. Qed.

  Lemma pw_pw : forall x a b, pw (pw x a) b = pw x (a * b).
  Proof.
    intros x a b; induction b as [| b ih]; cbn [Negacyclic.pw].
    - rewrite Nat.mul_0_r. reflexivity.
    - rewrite ih, Nat.mul_succ_r, Nat.add_comm, pw_add'. reflexivity.
  Qed.

  Lemma pw_one : forall k, pw one k = one.
  Proof. intro k; induction k as [| k ih]; cbn [Negacyclic.pw]; [reflexivity | rewrite ih; field]. Qed.

  (* ------------------------------------------------------------------ *)
  (* sums *)

  Lemma fsum_app' : forall l l', fsum (l ++ l') = fsum l + fsum l'.
  Proof. induction l as [| x l ih]; intro l'; cbn [app LogDer.fsum]; [field | rewrite ih; field]. Qed.

  Lemma fsum_ext' : forall {A : Type} (g h : A -> F) (l : list A),
    (forall a, In a l -> g a = h a) -> fsum (map g l) = fsum (map h l).
  Proof.
    intros A g h; induction l as [| a l ih]; intro e; cbn [map LogDer.fsum]; [reflexivity |].
    rewrite (e a (or_introl eq_refl)), ih by (intros; apply e; right; assumption). reflexivity.
  Qed.

  Lemma fsum_scale' : forall {A : Type} (c : F) (g : A -> F) (l : list A),
    fsum (map (fun a => c * g a) l) = c * fsum (map g l).
  Proof. intros A c g; induction l as [| a l ih]; cbn [map LogDer.fsum]; [field | rewrite ih; field]. Qed.

  Lemma fsum_add' : forall {A : Type} (g h : A -> F) (l : list A),
    fsum (map (fun a => g a + h a) l) = fsum (map g l) + fsum (map h l).
  Proof. intros A g h; induction l as [| a l ih]; cbn [map LogDer.fsum]; [field | rewrite ih; field]. Qed.

  Lemma fsum_swap' : forall {A B : Type} (f : A -> B -> F) (la : list A) (lb : list B),
    fsum (map (fun a => fsum (map (fun b => f a b) lb)) la) =
    fsum (map (fun b => fsum (map (fun a => f a b) la)) lb).
  Proof.
    intros A B f; induction la as [| a la ih]; intro lb; cbn [map LogDer.fsum].
    - induction lb as [| b lb ihb]; cbn [map LogDer.fsum]; [reflexivity | rewrite <-ihb; field].
    - rewrite ih, <-fsum_add'. reflexivity.
  Qed.

  Lemma fsum_const' : forall {A : Type} (c : F) (l : list A), fsum (map (fun _ => c) l) = nF (length l) * c.
  Proof. intros A c; induction l as [| a l ih]; cbn [map LogDer.fsum length LogDer.nF]; [field | rewrite ih; field]. Qed.

  (* a sum over seq 0 n in which only the term i survives *)
  Lemma fsum_delta : forall (g : nat -> F) n i, (i < n)%nat ->
    (forall k, (k < n)%nat -> k <> i -> g k = zero) ->
    fsum (map g (seq 0 n)) = g i.
  Proof.
    intros g n; induction n as [| n ih]; intros i hi hz; [lia |].
    rewrite seq_S, map_app, fsum_app'. cbn [map LogDer.fsum Nat.add].
    destruct (Nat.eq_dec i n) as [-> | hne].
    - rewrite (fsum_ext' g (fun _ => zero)), fsum_const'.
      + field.
      + intros k hk. apply in_seq in hk. apply hz; lia.
    - rewrite (ih i) by (lia || (intros k hk hki; apply hz; lia)).
      rewrite (hz n) by lia. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* evaluation as a sum *)

  Lemma eval_sum : forall p x, peval p x = fsum (map (fun k => nth k p zero * pw x k) (seq 0 (length p))).
  Proof.
    induction p as [| c p ih]; intro x; [reflexivity |].
    cbn [PolyRoots.eval length seq map LogDer.fsum nth Negacyclic.pw]. rewrite <-seq_shift, map_map.
    rewrite ih, <-fsum_scale'.
    rewrite (fsum_ext' (fun k => x * (nth k p zero * pw x k)) (fun a => nth (S a) (c :: p) zero * (x * pw x a)))
      by (intros k _; cbn [nth]; field).
    transitivity (c + fsum (map (fun x0 => nth x0 p zero * pw x (S x0)) (seq 0 (length p)))); [reflexivity | field].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the adjoint at a root of X^N + 1 *)

  Lemma eval_xadj : forall (N : nat) (z w : F) (rho : list F),
    length rho = N -> pw z N = opp one -> z * w = one ->
    peval (xadj rho) z = w * peval rho z.
  Proof.
    intros N z w rho hl hz hzw. destruct rho as [| h t]; [cbn; field |].
    cbn [Negacyclic.xadj]. rewrite peval_app. cbn [PolyRoots.eval length] in *.
    subst N. cbn [Negacyclic.pw] in hz.
    (* z * pw z |t| = -1 *)
    assert (e : peval t z + pw z (length t) * (opp h + z * zero)
                = w * (z * peval t z) - w * (z * pw z (length t)) * h).
    { replace (w * (z * peval t z)) with ((z * w) * peval t z) by field.
      replace (w * (z * pw z (length t)) * h) with ((z * w) * pw z (length t) * h) by field.
      rewrite hzw. field. }
    rewrite e, hz. field.
  Qed.

  Theorem eval_nadj : forall (N : nat) (z w : F) (a rho : list F),
    length rho = N -> pw z N = opp one -> z * w = one ->
    peval (nadj a rho) z = peval a w * peval rho z.
  Proof.
    intros N z w a rho hl hz hzw. induction a as [| ai a ih]; [cbn; field |].
    cbn [Negacyclic.nadj PolyRoots.eval]. rewrite eval_padd, eval_pscale.
    destruct a as [| aj a'].
    - cbn. field.
    - rewrite (eval_xadj N z w) by (try rewrite nadj_length by discriminate; assumption).
      rewrite ih. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* orthogonality *)

  Lemma geom : forall y n, fsum (map (pw y) (seq 0 n)) * (y - one) = pw y n - one.
  Proof.
    intros y n; induction n as [| n ih]; [cbn; field |].
    rewrite seq_S, map_app, fsum_app'. cbn [map LogDer.fsum Nat.add].
    transitivity (fsum (map (pw y) (seq 0 n)) * (y - one) + pw y n * (y - one)); [field |].
    rewrite ih. cbn [Negacyclic.pw]. field.
  Qed.

  Section Orth.
    Variables (n : nat) (om omi : F).
    Hypothesis hn : pw om n = one.
    Hypothesis hinv : om * omi = one.
    Hypothesis hprim : forall m, (0 < m < n)%nat -> pw om m <> one.

    Lemma omi_n : pw omi n = one.
    Proof.
      assert (h : pw (om * omi) n = one) by (rewrite hinv; apply pw_one).
      rewrite pw_mul_base, hn in h. transitivity (one * pw omi n); [field | exact h].
    Qed.

    (* om^k * omi^i = 1 exactly when k = i, for k, i < n *)
    Lemma ratio_one : forall k i, (k < n)%nat -> (i < n)%nat -> pw om k * pw omi i = one -> k = i.
    Proof.
      intros k i hk hi h.
      assert (h2 : forall j, pw om j * pw omi j = one) by (intro j; rewrite <-pw_mul_base, hinv; apply pw_one).
      destruct (Nat.lt_total k i) as [hlt | [heq | hgt]]; [| exact heq |]; exfalso.
      - apply (hprim (i - k)); [lia |].
        assert (e : pw om i = pw om k * pw om (i - k)) by (rewrite <-pw_add'; f_equal; lia).
        specialize (h2 i). rewrite e in h2.
        transitivity (pw om (i - k) * (pw om k * pw omi i)); [rewrite h; field |].
        transitivity (pw om k * pw om (i - k) * pw omi i); [field | exact h2].
      - apply (hprim (k - i)); [lia |].
        assert (e : pw om k = pw om i * pw om (k - i)) by (rewrite <-pw_add'; f_equal; lia).
        specialize (h2 i). rewrite e in h.
        transitivity (pw om (k - i) * (pw om i * pw omi i)); [rewrite h2; field |].
        transitivity (pw om i * pw om (k - i) * pw omi i); [field | exact h].
    Qed.

    Lemma orth : forall k i, (k < n)%nat -> (i < n)%nat ->
      fsum (map (fun j => pw (pw om k * pw omi i) j) (seq 0 n)) = if Nat.eqb k i then nF n else zero.
    Proof.
      intros k i hk hi. destruct (Nat.eqb_spec k i) as [-> | hne].
      - rewrite (fsum_ext' _ (fun _ => one)).
        + rewrite fsum_const', length_seq. field.
        + intros j _. rewrite <-pw_mul_base, hinv, pw_one. apply pw_one.
      - set (y := pw om k * pw omi i).
        assert (hy : y <> one) by (intro e; apply hne; exact (ratio_one k i hk hi e)).
        assert (hyn : pw y n = one).
        { unfold y. rewrite pw_mul_base, !pw_pw, (Nat.mul_comm k n), (Nat.mul_comm i n), <-!pw_pw, hn, omi_n, !pw_one. field. }
        assert (hg := geom y n). rewrite hyn in hg.
        assert (hy1 : y - one <> zero).
        { intro e. apply hy. transitivity ((y - one) + one); [field |]. rewrite e. field. }
        change (fun j => pw y j) with (pw y).
        transitivity ((fsum (map (pw y) (seq 0 n)) * (y - one)) * inv (y - one)); [field; exact hy1 |].
        rewrite hg. field. exact hy1.
    Qed.
  End Orth.

  (* ------------------------------------------------------------------ *)
  (* the inverse transform *)

  Theorem ntt_inverse : forall (n : nat) (psi om omi : F) (r : list F) (i : nat),
    pw om n = one -> om * omi = one -> (forall m, (0 < m < n)%nat -> pw om m <> one) ->
    length r = n -> (i < n)%nat ->
    peval (map (fun j => peval r (psi * pw om j)) (seq 0 n)) (pw omi i) = nF n * pw psi i * nth i r zero.
  Proof.
    intros n psi om omi r i hn hinv hprim hl hi.
    rewrite eval_sum, length_map, length_seq.
    rewrite (fsum_ext' _ (fun j => fsum (map (fun k => nth k r zero * pw psi k * pw (pw om k * pw omi i) j) (seq 0 n)))).
    2:{ intros j hj. apply in_seq in hj.
        rewrite (nth_indep _ zero ((fun j => peval r (psi * pw om j)) 0%nat)) by (rewrite length_map, length_seq; lia).
        rewrite (map_nth (fun j0 => peval r (psi * pw om j0))), seq_nth by lia. cbn [Nat.add].
        rewrite eval_sum, hl.
        transitivity (pw (pw omi i) j * fsum (map (fun k => nth k r zero * pw (psi * pw om j) k) (seq 0 n))); [field |].
        rewrite <-fsum_scale'. apply fsum_ext'. intros k _.
        rewrite !pw_mul_base, !pw_pw. rewrite (Nat.mul_comm j k). field. }
    rewrite fsum_swap'.
    rewrite (fsum_ext' _ (fun k => nth k r zero * pw psi k * (if Nat.eqb k i then nF n else zero))).
    2:{ intros k hk. apply in_seq in hk. rewrite fsum_scale'. f_equal.
        apply (orth n om omi hn hinv hprim); lia. }
    rewrite (fsum_delta _ n i hi).
    - rewrite Nat.eqb_refl. field.
    - intros k hk hki. apply Nat.eqb_neq in hki. rewrite hki. field.
  Qed.

End NttInverse.
