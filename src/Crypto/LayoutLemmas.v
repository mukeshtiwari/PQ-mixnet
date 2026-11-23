(* Evaluations as linear claims on rows (paper, Section 4.2: "An evaluation
   of a multilinear extension at a point is of this form: for a table split
   into rows, L is the eq vector of the low variables and the coefficients
   are the eq values of the high variables").

   - mle_concat: an extension in n + l variables at x ++ r is the extension
     in the first n variables of the extensions in the last l.
   - mle_rows: let a table T on the cube of lo + hi variables be stored in
     2^hi rows of 2^lo data symbols, row t holding T (pt y ++ pt t) at
     position y. Then mle T (xlo ++ xhi) is the value of the claim with one
     term per row t, coefficient eq(pt t, xhi), in a slot whose vector is
     the eq vector of xlo.
   - tval_app, tval_single: claims are added by concatenating their terms;
     a single term reads one inner product. With mle_rows these give the
     masked extensions: T*(x) = mle T x + a_T * Z(x) is the tensor claim
     plus one term on the row that stores a_T.
   - gmask_functional: the value of a sumcheck mask at a point is the inner
     product of its coefficient vector a0 :: concat cs with the public
     vector 1 :: [r_j, r_j^2, ..]_j.

   These are the pieces from which the nine claims of Figure 1, step 7 are
   built. Assembling them for the row layout of the implementation is part
   of the executable verifier (M10). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Sumcheck SumcheckMask CubeIndex Opening MixBridge.
Import ListNotations.

Section LayoutLemmas.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation peval := (@eval F zero add mul).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation pt := (@pt F zero one).
  Local Notation tval := (@tval F zero add mul).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation gtail := (@gtail F zero add mul).
  Local Notation uni := (@uni F zero add mul).
  Local Notation term := (@term F).

  Lemma fsum_swap : forall {A B : Type} (f : A -> B -> F) (la : list A) (lb : list B),
    fsum (map (fun a => fsum (map (fun b => f a b) lb)) la) =
    fsum (map (fun b => fsum (map (fun a => f a b) la)) lb).
  Proof.
    intros A B f; induction la as [| a la ih]; intro lb; cbn [map LogDer.fsum].
    + symmetry. apply (@fsum_map_zero_ext F zero one add mul sub div opp inv Hf). intros; reflexivity.
    + rewrite ih, <-(@fsum_map_add F zero one add mul sub div opp inv Hf). reflexivity.
  Qed.

  Theorem mle_concat : forall (n l : nat) (T : list F -> F) (x r : list F), length x = n ->
    mle (n + l) T (x ++ r) = mle n (fun y => mle l (fun bb => T (y ++ bb)) r) x.
  Proof.
    induction n as [| n ih]; intros l T x r hx.
    + destruct x; [| discriminate]. cbn [Nat.add app].
      rewrite (@mle_0 F zero one add mul sub div opp inv Hf). reflexivity.
    + destruct x as [| x0 xs]; [discriminate |]. cbn in hx. cbn [Nat.add app].
      rewrite !(@mle_S F zero one add mul sub div opp inv Hf).
      rewrite !(ih l _ xs r) by lia. reflexivity.
  Qed.

  Lemma mle_seq : forall (m : nat) (T : list F -> F) (x : list F),
    mle m T x = fsum (map (fun i => T (pt m i) * eqp (pt m i) x) (seq 0 (2 ^ m))).
  Proof.
    intros m T x. unfold Mle.mle.
    apply (@cube_sum_seq F zero one add mul sub div opp inv Hf m (fun b => T b * eqp b x)).
  Qed.

  Lemma tval_app : forall P Ls (cl cl' : list term), tval P Ls (cl ++ cl') = tval P Ls cl + tval P Ls cl'.
  Proof. intros P Ls; induction cl as [| t cl ih]; intro cl'; cbn; [field | rewrite ih; field]. Qed.

  Lemma tval_single : forall P Ls (v i : nat) (a : F), tval P Ls [(v, i, a)] = a * dot (P i) (Ls v).
  Proof. intros. cbn. field. Qed.

  Lemma tval_map : forall {A : Type} P Ls (v : nat) (rowf : A -> nat) (cf : A -> F) (l : list A),
    tval P Ls (map (fun t => (v, rowf t, cf t)) l) = fsum (map (fun t => cf t * dot (P (rowf t)) (Ls v)) l).
  Proof.
    intros A P Ls v rowf cf; induction l as [| t l ih]; cbn [map Opening.tval LogDer.fsum fst snd];
      [reflexivity | rewrite ih; reflexivity].
  Qed.

  (* A table stored in rows. *)
  Theorem mle_rows : forall (lo hi : nat) (T : list F -> F) (P : nat -> list F) (Ls : nat -> list F)
    (v : nat) (rowf : nat -> nat) (xlo xhi : list F),
    length xlo = lo ->
    (forall y t, (y < 2 ^ lo)%nat -> (t < 2 ^ hi)%nat -> nth y (P (rowf t)) zero = T (pt lo y ++ pt hi t)) ->
    Ls v = map (fun y => eqp (pt lo y) xlo) (seq 0 (2 ^ lo)) ->
    mle (lo + hi) T (xlo ++ xhi)
    = tval P Ls (map (fun t => (v, rowf t, eqp (pt hi t) xhi)) (seq 0 (2 ^ hi))).
  Proof.
    intros lo hi T P Ls v rowf xlo xhi hx hrow hL.
    rewrite (mle_concat lo hi T xlo xhi hx), mle_seq.
    rewrite (tval_map P Ls v rowf (fun t => eqp (pt hi t) xhi)), hL.
    rewrite (@fsum_map_ext F zero add _ _
               (fun y => fsum (map (fun t => T (pt lo y ++ pt hi t) * eqp (pt hi t) xhi * eqp (pt lo y) xlo)
                                   (seq 0 (2 ^ hi))))).
    2:{ intros y _. rewrite mle_seq. cbn beta.
        transitivity (eqp (pt lo y) xlo * fsum (map (fun i => T (pt lo y ++ pt hi i) * eqp (pt hi i) xhi) (seq 0 (2 ^ hi))));
          [field |].
        rewrite <-(@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
        apply (@fsum_map_ext F zero add). intros t _. field. }
    rewrite fsum_swap.
    apply (@fsum_map_ext F zero add). intros t ht. apply in_seq in ht.
    rewrite (@dot_seq0 F zero one add mul sub div opp inv Hf).
    rewrite <-(@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros y hy. apply in_seq in hy.
    rewrite (hrow y t ltac:(lia) ltac:(lia)). field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The sumcheck mask as a linear functional of its coefficients *)

  (* p, p x, p x^2, .., k entries *)
  Fixpoint pows (x : F) (k : nat) (p : F) : list F :=
    match k with
    | 0 => []
    | S k' => p :: pows x k' (p * x)
    end.

  Lemma pows_length : forall x k p, length (pows x k p) = k.
  Proof. intros x; induction k as [| k ih]; intro p; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Lemma dot_pows : forall (c : list F) (x p : F), dot c (pows x (length c) p) = p * peval c x.
  Proof.
    induction c as [| c0 c ih]; intros x p; cbn; [field | rewrite ih; field].
  Qed.

  (* [r_0, r_0^2, ..] ++ [r_1, r_1^2, ..] ++ .. *)
  Fixpoint maskfn (cs : list (list F)) (r : list F) : list F :=
    match cs, r with
    | c :: cs', ri :: r' => pows ri (length c) ri ++ maskfn cs' r'
    | _, _ => []
    end.

  Lemma gtail_functional : forall (cs : list (list F)) (r : list F),
    gtail cs r = dot (concat cs) (maskfn cs r).
  Proof.
    induction cs as [| c cs ih]; intro r; cbn [SumcheckMask.gtail concat maskfn].
    + reflexivity.
    + destruct r as [| ri r'].
      - symmetry. apply (@dot_nil_r F zero add mul).
      - rewrite (@dot_app F zero one add mul sub div opp inv Hf) by (rewrite pows_length; reflexivity).
        rewrite dot_pows, ih. unfold SumcheckMask.uni. reflexivity.
  Qed.

  Theorem gmask_functional : forall (a0 : F) (cs : list (list F)) (r : list F),
    gmask a0 cs r = dot (a0 :: concat cs) (one :: maskfn cs r).
  Proof.
    intros a0 cs r. unfold SumcheckMask.gmask. rewrite gtail_functional. cbn. field.
  Qed.

End LayoutLemmas.
