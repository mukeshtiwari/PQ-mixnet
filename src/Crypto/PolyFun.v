(* Functions of one variable that are polynomials of bounded degree.

     is_poly d f  :=  there is a coefficient list p with at most d + 1
                      entries and eval p X = f X for all X.

   This is the form in which sc_sound wants the degree bound of a round
   function (its hypothesis Hcert). The lemmas give closure under
   constants, the variable, sums, scaling, products (degrees add) and
   finite sums, so the degree of a concrete summand is obtained by
   following its syntax. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer.
Import ListNotations.

Section PolyFun.

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
  Local Notation fsum := (@fsum F zero add).

  Fixpoint pmul (p q : list F) : list F :=
    match p with
    | [] => []
    | c :: p' => padd (pscale c q) (zero :: pmul p' q)
    end.

  Lemma eval_pmul : forall p q x, peval (pmul p q) x = peval p x * peval q x.
  Proof.
    induction p as [| c p ih]; intros q x; cbn [pmul].
    + cbn. field.
    + rewrite eval_padd, eval_pscale. cbn. rewrite ih. field.
  Qed.

  Lemma length_pmul : forall p q, q <> [] -> (length (pmul p q) <= length p + length q - 1)%nat.
  Proof.
    induction p as [| c p ih]; intros q hq; cbn [pmul]; [cbn; lia |].
    rewrite length_padd, length_pscale. cbn [length].
    specialize (ih q hq). destruct q; [contradiction |]. cbn [length] in *. lia.
  Qed.

  Definition is_poly (d : nat) (f : F -> F) : Prop :=
    exists p : list F, (length p <= S d)%nat /\ forall X, peval p X = f X.

  Lemma is_poly_ext : forall d f g, (forall X, f X = g X) -> is_poly d f -> is_poly d g.
  Proof. intros d f g h (p & hl & hp). exists p; split; [exact hl |]. intro X. rewrite hp. apply h. Qed.

  Lemma is_poly_mono : forall d d' f, (d <= d')%nat -> is_poly d f -> is_poly d' f.
  Proof. intros d d' f h (p & hl & hp). exists p; split; [lia | exact hp]. Qed.

  Lemma is_poly_const : forall d c, is_poly d (fun _ => c).
  Proof. intros d c. exists [c]; split; [cbn; lia |]. intro X. cbn. field. Qed.

  Lemma is_poly_id : forall d, (1 <= d)%nat -> is_poly d (fun X => X).
  Proof. intros d h. exists [zero; one]; split; [cbn; lia |]. intro X. cbn. field. Qed.

  Lemma is_poly_add : forall d1 d2 f g, is_poly d1 f -> is_poly d2 g ->
    is_poly (Nat.max d1 d2) (fun X => f X + g X).
  Proof.
    intros d1 d2 f g (p & hlp & hp) (q & hlq & hq). exists (padd p q); split.
    + rewrite length_padd. lia.
    + intro X. rewrite eval_padd, hp, hq. reflexivity.
  Qed.

  Lemma is_poly_scale : forall d c f, is_poly d f -> is_poly d (fun X => c * f X).
  Proof.
    intros d c f (p & hl & hp). exists (pscale c p); split.
    + rewrite length_pscale. exact hl.
    + intro X. rewrite eval_pscale, hp. reflexivity.
  Qed.

  Lemma is_poly_sub : forall d1 d2 f g, is_poly d1 f -> is_poly d2 g ->
    is_poly (Nat.max d1 d2) (fun X => f X - g X).
  Proof.
    intros d1 d2 f g hf hg.
    apply (is_poly_ext _ (fun X => f X + opp one * g X)); [intro X; field |].
    apply is_poly_add; [exact hf | apply is_poly_scale; exact hg].
  Qed.

  Lemma is_poly_mul : forall d1 d2 f g, is_poly d1 f -> is_poly d2 g ->
    is_poly (d1 + d2) (fun X => f X * g X).
  Proof.
    intros d1 d2 f g (p & hlp & hp) (q & hlq & hq).
    destruct q as [| q0 q'].
    + exists []; split; [cbn; lia |]. intro X. rewrite <-hq. cbn. field.
    + exists (pmul p (q0 :: q')); split.
      - pose proof (length_pmul p (q0 :: q') ltac:(discriminate)) as h. cbn [length] in *. lia.
      - intro X. rewrite eval_pmul, hp, hq. reflexivity.
  Qed.

  Lemma is_poly_fsum : forall {A : Type} d (phi : A -> F -> F) (l : list A),
    (forall a, In a l -> is_poly d (phi a)) ->
    is_poly d (fun X => fsum (map (fun a => phi a X) l)).
  Proof.
    intros A d phi; induction l as [| a l ih]; intro h; cbn [map LogDer.fsum].
    + apply is_poly_const.
    + apply (is_poly_mono (Nat.max d d)); [lia |].
      apply is_poly_add; [apply h; left; reflexivity | apply ih; intros b hb; apply h; right; exact hb].
  Qed.

  (* (1 - X) * A + X * B *)
  Lemma is_poly_affine : forall d A B, (1 <= d)%nat -> is_poly d (fun X => (one - X) * A + X * B).
  Proof.
    intros d A B h. exists [A; B - A]; split; [cbn; lia |]. intro X. cbn. field.
  Qed.

  (* composition with a fixed polynomial phi of degree at most D *)
  Lemma is_poly_peval : forall (phi : list F) (D d : nat) (f : F -> F),
    (length phi <= S D)%nat -> is_poly d f -> is_poly (D * d) (fun X => peval phi (f X)).
  Proof.
    induction phi as [| c phi ih]; intros D d f hl hf.
    + cbn. apply is_poly_const.
    + cbn [PolyRoots.eval]. destruct D as [| D'].
      - destruct phi; [| cbn in hl; lia].
        apply (is_poly_ext _ (fun _ => c)); [intro X; cbn; field | apply is_poly_const].
      - apply (is_poly_mono (Nat.max 0 (d + D' * d))); [lia |].
        apply is_poly_add; [apply is_poly_const |].
        apply is_poly_mul; [exact hf | apply ih; [cbn in hl; lia | exact hf]].
  Qed.

End PolyFun.
