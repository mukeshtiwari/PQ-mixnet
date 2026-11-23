(* The ring R = F[X]/(X^N + 1) on coefficient lists (paper, Section 2.1).

   An element is its list of N coefficients, constant term first.

     xmul r   = X * r           (shift up, negate the wrapped coefficient)
     nmul a r = a * r           (sum_i a_i * X^i * r)

   Only two facts about this ring are used by the proofs of the paper, and
   both are statements about linear maps on coefficient vectors:

   - nmul_adjoint: dot rho (nmul a r) = dot (nadj a rho) r. Multiplication
     by a fixed a is a linear map, and nadj a is its transpose. This is
     how the verifier moves a public factor onto the challenge side
     ("the verifier's linear algebra", Section 5.1);
   - nmul_eval: at a root zeta of X^N + 1, evaluation is multiplicative.
     This is the CRT slot map; it justifies that nmul really is the ring
     multiplication, and it is what the slot attack exploits.

   poly_eq_of_evals: two lists of N coefficients that agree at N distinct
   points are equal (injectivity of the slot map). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer.
Import ListNotations.

Section Negacyclic.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation peval := (@eval F zero add mul).
  Local Notation pz := (@pzero F zero).

  (* ------------------------------------------------------------------ *)
  (* Inner product: linearity in both arguments *)

  Lemma dot_nil_r : forall a : list F, dot a [] = zero.
  Proof. destruct a; reflexivity. Qed.

  Lemma dot_sym : forall a b : list F, dot a b = dot b a.
  Proof.
    induction a as [| x a ih]; intro b; destruct b as [| y b]; cbn; try reflexivity.
    rewrite ih; field.
  Qed.

  Lemma dot_padd_l : forall a b r : list F, dot (padd a b) r = dot a r + dot b r.
  Proof.
    induction a as [| x a ih]; intros b r.
    + cbn. field.
    + destruct b as [| y b]; cbn [LogDer.padd].
      - rewrite (dot_sym []), dot_nil_r. field.
      - destruct r as [| z r]; cbn; [field | rewrite ih; field].
  Qed.

  Lemma dot_padd_r : forall r a b : list F, dot r (padd a b) = dot r a + dot r b.
  Proof. intros r a b. rewrite dot_sym, dot_padd_l, (dot_sym a), (dot_sym b). reflexivity. Qed.

  Lemma dot_pscale_l : forall t (a r : list F), dot (pscale t a) r = t * dot a r.
  Proof.
    intro t; induction a as [| x a ih]; intro r; cbn; [field |].
    destruct r as [| z r]; cbn; [field |]. unfold LogDer.pscale in ih. rewrite ih; field.
  Qed.

  Lemma dot_pscale_r : forall t (r a : list F), dot r (pscale t a) = t * dot r a.
  Proof. intros t r a. rewrite dot_sym, dot_pscale_l, (dot_sym a). reflexivity. Qed.

  Lemma dot_app : forall a a' b b' : list F, length a = length b ->
    dot (a ++ a') (b ++ b') = dot a b + dot a' b'.
  Proof.
    induction a as [| x a ih]; intros a' b b' hl; destruct b as [| y b]; cbn in hl; try lia.
    + cbn. field.
    + cbn. rewrite ih by lia. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Multiplication by X and its transpose *)

  Definition xmul (r : list F) : list F :=
    match r with
    | [] => []
    | _ => opp (last r zero) :: removelast r
    end.

  Definition xadj (rho : list F) : list F :=
    match rho with
    | [] => []
    | h :: t => t ++ [opp h]
    end.

  Lemma xmul_snoc : forall (r : list F) (l : F), xmul (r ++ [l]) = opp l :: r.
  Proof.
    intros r l. unfold xmul. destruct (r ++ [l]) eqn:E.
    + destruct r; discriminate.
    + rewrite <-E, last_last, removelast_last. reflexivity.
  Qed.

  Lemma xmul_length : forall r, length (xmul r) = length r.
  Proof.
    intro r. destruct r as [| r0 rt]; [reflexivity |].
    destruct (@exists_last F (r0 :: rt) ltac:(discriminate)) as (r' & l & e).
    rewrite e, xmul_snoc, length_app. cbn. lia.
  Qed.

  Lemma xadj_length : forall rho, length (xadj rho) = length rho.
  Proof. destruct rho; cbn; [reflexivity | rewrite length_app; cbn; lia]. Qed.

  Lemma xmul_adjoint : forall X r : list F, length X = length r ->
    dot X (xmul r) = dot (xadj X) r.
  Proof.
    intros X r hl.
    destruct r as [| r0 rt].
    + destruct X; [reflexivity | discriminate].
    + destruct (@exists_last F (r0 :: rt) ltac:(discriminate)) as (r' & l & e).
      rewrite e in *. rewrite xmul_snoc.
      destruct X as [| h t]; [rewrite length_app in hl; cbn in hl; lia |].
      cbn [xadj]. rewrite dot_app by (rewrite length_app in hl; cbn in hl; lia).
      cbn. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Multiplication by a fixed element and its transpose *)

  Fixpoint nmul (a r : list F) : list F :=
    match a with
    | [] => []
    | ai :: a' => padd (pscale ai r) (nmul a' (xmul r))
    end.

  Fixpoint nadj (a rho : list F) : list F :=
    match a with
    | [] => []
    | ai :: a' => padd (pscale ai rho) (xadj (nadj a' rho))
    end.

  Lemma nadj_length : forall a rho, a <> [] -> length (nadj a rho) = length rho.
  Proof.
    induction a as [| ai a ih]; intros rho hne; [contradiction |].
    cbn [nadj]. rewrite length_padd, length_pscale, xadj_length.
    destruct a as [| aj a']; [cbn; lia |]. rewrite ih by discriminate. lia.
  Qed.

  Lemma nmul_length : forall a r, a <> [] -> length (nmul a r) = length r.
  Proof.
    induction a as [| ai a ih]; intros r hne; [contradiction |].
    cbn [nmul]. rewrite length_padd, length_pscale.
    destruct a as [| aj a']; [cbn; lia |]. rewrite ih by discriminate. rewrite xmul_length. lia.
  Qed.

  Theorem nmul_adjoint : forall a rho r : list F, length rho = length r ->
    dot rho (nmul a r) = dot (nadj a rho) r.
  Proof.
    induction a as [| ai a ih]; intros rho r hl.
    + cbn. apply dot_nil_r.
    + cbn [nmul nadj].
      rewrite dot_padd_r, dot_padd_l, dot_pscale_r, dot_pscale_l.
      rewrite (ih rho (xmul r)) by (rewrite xmul_length; exact hl).
      f_equal.
      destruct a as [| aj a'].
      - cbn. reflexivity.
      - apply xmul_adjoint. rewrite nadj_length by discriminate. exact hl.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Evaluation at a root of X^N + 1: the slot map *)

  Fixpoint pw (x : F) (k : nat) : F :=
    match k with
    | 0 => one
    | S k' => x * pw x k'
    end.

  Lemma peval_app : forall (p q : list F) (x : F),
    peval (p ++ q) x = peval p x + pw x (length p) * peval q x.
  Proof.
    induction p as [| c p ih]; intros q x; cbn; [field | rewrite ih; field].
  Qed.

  Lemma xmul_eval : forall (N : nat) (zeta : F) (r : list F),
    length r = N -> pw zeta N = opp one ->
    peval (xmul r) zeta = zeta * peval r zeta.
  Proof.
    intros N zeta r hl hz.
    destruct r as [| r0 rt].
    + cbn. field.
    + destruct (@exists_last F (r0 :: rt) ltac:(discriminate)) as (r' & l & e).
      rewrite e in *. rewrite xmul_snoc, peval_app.
      rewrite length_app in hl. cbn in hl.
      assert (hN : N = S (length r')) by lia. rewrite hN in hz. cbn [pw] in hz.
      cbn.
      assert (h : zeta * (peval r' zeta + pw zeta (length r') * (l + zeta * zero))
                  = zeta * peval r' zeta + (zeta * pw zeta (length r')) * l) by field.
      rewrite h, hz. field.
  Qed.

  Theorem nmul_eval : forall (N : nat) (zeta : F), pw zeta N = opp one ->
    forall a r : list F, length r = N ->
    peval (nmul a r) zeta = peval a zeta * peval r zeta.
  Proof.
    intros N zeta hz; induction a as [| ai a ih]; intros r hl.
    + cbn. field.
    + cbn [nmul]. rewrite eval_padd, eval_pscale.
      rewrite ih by (rewrite xmul_length; exact hl).
      rewrite (xmul_eval N zeta r hl hz). cbn. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Injectivity of evaluation at N distinct points *)

  Lemma pzero_nth : forall (p : list F) (k : nat), pz p -> nth k p zero = zero.
  Proof.
    intros p k h. destruct (Fdec (nth k p zero) zero) as [e | e]; [exact e |].
    exfalso. exact (@nth_nonzero_not_pzero F zero p k e h).
  Qed.

  Theorem poly_eq_of_evals : forall (N : nat) (zs p q : list F),
    NoDup zs -> length zs = N -> length p = N -> length q = N ->
    (forall z, In z zs -> peval p z = peval q z) -> p = q.
  Proof.
    intros N zs p q hnd hzs hp hq hev.
    set (df := padd p (pscale (opp one) q)).
    assert (hlen : length df = N).
    { unfold df. rewrite length_padd, length_pscale. lia. }
    assert (hz : pz df).
    { destruct (@pzero_dec F zero Fdec df) as [h | h]; [exact h | exfalso].
      assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf (length df) df (le_n _) h zs hnd).
      assert (hr : forall r, In r zs -> peval df r = zero).
      { intros r hr. unfold df. rewrite eval_padd, eval_pscale, (hev r hr). field. }
      specialize (hlt hr). lia. }
    apply (nth_ext p q zero zero); [lia |].
    intros k _. pose proof (pzero_nth df k hz) as h. unfold df in h.
    rewrite nth_padd, nth_pscale in h.
    assert (e : nth k p zero = (nth k p zero + opp one * nth k q zero) + nth k q zero) by field.
    rewrite e, h. field.
  Qed.

End Negacyclic.
