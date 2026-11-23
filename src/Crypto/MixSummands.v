(* The three sumcheck summands of the shuffle proof (paper, Figure 1, steps
   4 to 6) and their degree certificates (the "Degrees" remark).

   Tables are functions on points; only their values on the cube matter.

     gA x = eq(x, tc) * (k1 * ustar x * hstar x + k2 * uhstar x * hhstar x)
            + k3 * (ustar x - uhstar x) + rhoA * gmask_A x          ell variables
     gB y = sum_k mle rp_k y * mle W_k (y ++ r) + cB + rhoB * gmask_B y  logN variables
     gC x = eq(x, tz) * sum_k kc_k * ((wstar_k x)^3 - wstar_k x)
            + rhoC * gmask_C x                                       m variables

   with the masked extensions ustar = mstar u a_u and so on, and
   hhstar x = mle zh x + beta * sgstar x - alpha.

   Certificates (the hypothesis Hcert of sc_sound): the round function of
   round i is a polynomial of degree at most
     degA i = 3, and 5 in the last round;
     degB i = 2;
     degC i = 4, and 7 in the last round,
   provided the coefficient list of the mask for variable i has at most
   that many entries. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Sumcheck SumcheckMask PolyFun MaskedExt.
Import ListNotations.

Section MixSummands.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation peval := (@eval F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation is_poly := (@is_poly F zero add mul).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation gtail := (@gtail F zero add mul).
  Local Notation uni := (@uni F zero add mul).
  Local Notation rnd := (@rnd F zero one add).
  Local Notation lastdeg := MaskedExt.lastdeg.

  (* ------------------------------------------------------------------ *)
  (* Generic pieces *)

  Lemma rnd_is_poly : forall (g : list F -> F) (pre : list F) (k d : nat),
    (forall b, In b (cube k) -> is_poly d (fun X => g (pre ++ X :: b))) ->
    exists pstar, (length pstar <= S d)%nat /\ forall X, peval pstar X = rnd g pre k X.
  Proof.
    intros g pre k d h.
    exact (is_poly_fsum d (fun b X => g (pre ++ X :: b)) (cube k) h).
  Qed.

  Lemma gmask_is_poly : forall (a0 : F) (cs : list (list F)) (pre b : list F) (d : nat),
    (length pre < length cs)%nat -> (length (nth (length pre) cs []) <= d)%nat ->
    is_poly d (fun X => gmask a0 cs (pre ++ X :: b)).
  Proof.
    intros a0 cs pre b d hlt hd.
    destruct (nth_split cs [] hlt) as (c1 & c2 & e & hl1).
    set (c := nth (length pre) cs []) in *.
    exists ((a0 + gtail c1 pre + gtail c2 b) :: c); split; [cbn; lia |].
    intro X. unfold SumcheckMask.gmask. rewrite e.
    rewrite (@gtail_app F zero one add mul sub div opp inv Hf c1 pre (c :: c2) (X :: b)) by lia.
    cbn. unfold SumcheckMask.uni. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Sumcheck A: the permutation *)

  Section SummandA.
    Variable ell : nat.
    Variables u uh sg h zh : list F -> F.
    Variables au auh asg ah : F.
    Variables alpha beta : F.
    Variable tc : list F.
    Variables k1 k2 k3 rhoA : F.
    Variable a0A : F.
    Variable csA : list (list F).

    Definition ustar (x : list F) : F := mstar ell u au x.
    Definition uhstar (x : list F) : F := mstar ell uh auh x.
    Definition sgstar (x : list F) : F := mstar ell sg asg x.
    Definition hstar (x : list F) : F := mstar ell h ah x.
    Definition hhstar (x : list F) : F := mle ell zh x + beta * sgstar x - alpha.

    Definition gA (x : list F) : F :=
      eqp x tc * (k1 * (ustar x * hstar x) + k2 * (uhstar x * hhstar x))
      + k3 * (ustar x - uhstar x) + rhoA * gmask a0A csA x.

    Definition degA (i : nat) : nat := if Nat.eqb (S i) ell then 5 else 3.

    Hypothesis HcsA : length csA = ell.
    Hypothesis HdegA : forall i, (i < ell)%nat -> (length (nth i csA []) <= degA i)%nat.

    Theorem certA : forall pre k, (length pre + S k = ell)%nat ->
      exists pstar, (length pstar <= S (degA (length pre)))%nat /\ forall X, peval pstar X = rnd gA pre k X.
    Proof.
      intros pre k e. apply rnd_is_poly. intros b hb.
      set (dk := lastdeg k).
      assert (hdk : (1 <= dk)%nat) by (unfold dk; destruct k; cbn; lia).
      assert (hD : degA (length pre) = (1 + (dk + dk))%nat).
      { unfold degA, dk. destruct k as [| k'].
        + replace (S (length pre)) with ell by lia. rewrite Nat.eqb_refl. reflexivity.
        + rewrite (proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
      assert (hstarp : forall T a, is_poly dk (fun X => mstar ell T a (pre ++ X :: b))).
      { intros T a. rewrite <-e. apply mstar_is_poly. exact hb. }
      assert (hhh : is_poly dk (fun X => hhstar (pre ++ X :: b))).
      { unfold hhstar, sgstar.
        apply (is_poly_mono (Nat.max (Nat.max 1 dk) 0)); [lia |].
        apply is_poly_sub; [| apply is_poly_const].
        apply is_poly_add; [rewrite <-e; apply mle_coord_poly | apply is_poly_scale; apply hstarp]. }
      unfold gA.
      apply (is_poly_mono (Nat.max (Nat.max (1 + Nat.max (dk + dk) (dk + dk)) (Nat.max dk dk)) (degA (length pre))));
        [lia |].
      apply is_poly_add; [apply is_poly_add |].
      + apply is_poly_mul; [apply eqp_coord_poly |].
        apply is_poly_add; apply is_poly_scale; apply is_poly_mul;
          first [apply hstarp | exact hhh].
      + apply is_poly_scale. apply is_poly_sub; apply hstarp.
      + apply is_poly_scale. apply gmask_is_poly; [lia | apply HdegA; lia].
    Qed.
  End SummandA.

  (* ------------------------------------------------------------------ *)
  (* Sumcheck B: the linearisation *)

  Section SummandB.
    Variables n1 ell : nat.                 (* log N and log tau *)
    Variables rp1 rp2 rp3 : list F -> F.    (* the three blocks of rho', as tables on the cube of size N *)
    Variables W1 W2 W3 : list F -> F.       (* the witness tables, n1 + ell variables, coefficient index first *)
    Variable r : list F.                    (* the end point of sumcheck A *)
    Variables cB rhoB : F.                  (* cB = a_h * Z(r) / N *)
    Variable a0B : F.
    Variable csB : list (list F).

    Definition gB (y : list F) : F :=
      mle n1 rp1 y * mle (n1 + ell) W1 (y ++ r)
      + mle n1 rp2 y * mle (n1 + ell) W2 (y ++ r)
      + mle n1 rp3 y * mle (n1 + ell) W3 (y ++ r)
      + cB + rhoB * gmask a0B csB y.

    Definition degB (i : nat) : nat := 2.

    Hypothesis HcsB : length csB = n1.
    Hypothesis HdegB : forall i, (i < n1)%nat -> (length (nth i csB []) <= 2)%nat.

    Theorem certB : forall pre k, (length pre + S k = n1)%nat ->
      exists pstar, (length pstar <= S (degB (length pre)))%nat /\ forall X, peval pstar X = rnd gB pre k X.
    Proof.
      intros pre k e. apply rnd_is_poly. intros b hb. unfold degB.
      assert (hterm : forall rp W, is_poly 2 (fun X => mle n1 rp (pre ++ X :: b) * mle (n1 + ell) W ((pre ++ X :: b) ++ r))).
      { intros rp W. apply (is_poly_mono (1 + 1)); [lia |].
        apply is_poly_mul.
        + rewrite <-e. apply mle_coord_poly.
        + apply (is_poly_ext _ (fun X => mle (length pre + S (k + ell)) W (pre ++ X :: (b ++ r)))).
          - intro X. replace (n1 + ell)%nat with (length pre + S (k + ell))%nat by lia.
            rewrite <-app_assoc. reflexivity.
          - apply mle_coord_poly. }
      unfold gB.
      apply (is_poly_mono (Nat.max (Nat.max (Nat.max (Nat.max 2 2) 2) 0) 2)); [lia |].
      apply is_poly_add; [apply is_poly_add; [apply is_poly_add; [apply is_poly_add |] |] |].
      + apply hterm.
      + apply hterm.
      + apply hterm.
      + apply is_poly_const.
      + apply is_poly_scale. apply gmask_is_poly; [lia | apply HdegB; lia].
    Qed.
  End SummandB.

  (* ------------------------------------------------------------------ *)
  (* Sumcheck C: shortness *)

  Section SummandC.
    Variable m : nat.
    Variables W1 W2 W3 : list F -> F.
    Variables aw1 aw2 aw3 : F.
    Variable tz : list F.
    Variables kc1 kc2 kc3 rhoC : F.
    Variable a0C : F.
    Variable csC : list (list F).

    Definition cube3 (w : F) : F := w * w * w - w.

    Definition wstar1 (x : list F) : F := mstar m W1 aw1 x.
    Definition wstar2 (x : list F) : F := mstar m W2 aw2 x.
    Definition wstar3 (x : list F) : F := mstar m W3 aw3 x.

    Definition gC (x : list F) : F :=
      eqp x tz * (kc1 * cube3 (wstar1 x) + kc2 * cube3 (wstar2 x) + kc3 * cube3 (wstar3 x))
      + rhoC * gmask a0C csC x.

    Definition degC (i : nat) : nat := if Nat.eqb (S i) m then 7 else 4.

    Hypothesis HcsC : length csC = m.
    Hypothesis HdegC : forall i, (i < m)%nat -> (length (nth i csC []) <= degC i)%nat.

    Theorem certC : forall pre k, (length pre + S k = m)%nat ->
      exists pstar, (length pstar <= S (degC (length pre)))%nat /\ forall X, peval pstar X = rnd gC pre k X.
    Proof.
      intros pre k e. apply rnd_is_poly. intros b hb.
      set (dk := lastdeg k).
      assert (hdk : (1 <= dk)%nat) by (unfold dk; destruct k; cbn; lia).
      assert (hD : degC (length pre) = (1 + (dk + dk + dk))%nat).
      { unfold degC, dk. destruct k as [| k'].
        + replace (S (length pre)) with m by lia. rewrite Nat.eqb_refl. reflexivity.
        + rewrite (proj2 (Nat.eqb_neq _ _)) by lia. reflexivity. }
      assert (hstarp : forall T a, is_poly dk (fun X => mstar m T a (pre ++ X :: b))).
      { intros T a. rewrite <-e. apply mstar_is_poly. exact hb. }
      assert (hc3 : forall T a, is_poly (dk + dk + dk) (fun X => cube3 (mstar m T a (pre ++ X :: b)))).
      { intros T a. unfold cube3.
        apply (is_poly_mono (Nat.max (dk + dk + dk) dk)); [lia |].
        apply is_poly_sub; [| apply hstarp].
        apply is_poly_mul; [apply is_poly_mul |]; apply hstarp. }
      unfold gC, wstar1, wstar2, wstar3.
      apply (is_poly_mono (Nat.max (1 + Nat.max (Nat.max (dk + dk + dk) (dk + dk + dk)) (dk + dk + dk))
                                   (degC (length pre)))); [lia |].
      apply is_poly_add.
      + apply is_poly_mul; [apply eqp_coord_poly |].
        apply is_poly_add; [apply is_poly_add |]; apply is_poly_scale; apply hc3.
      + apply is_poly_scale. apply gmask_is_poly; [lia | apply HdegC; lia].
    Qed.
  End SummandC.

End MixSummands.
