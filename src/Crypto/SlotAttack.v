(* The slot attack (paper, Sections 1 and 3; Bootle, Lyubashevsky and
   Merino-Gallardo, PKC 2025), as a theorem.

   slot_swap_products. Let X^N + 1 have N distinct roots in F. If f', g'
   are obtained from f, g by exchanging the values of some slots (the
   evaluations at some of the roots), then for every alpha in R

       (f - alpha) (g - alpha) = (f' - alpha) (g' - alpha)   in R.

   So a product test computed in the ring cannot tell {f, g} from
   {f', g'}, although they are different multisets as soon as one slot in
   which f and g differ is exchanged and another is not.

   The second part instantiates this over Z_17 with N = 4 and exhibits a
   projection rho that separates the two multisets. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith ZArith Znumtheory.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Utility Require Import Zpstar.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Negacyclic.
Import ListNotations.

Section SlotAttack.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation nmul := (@nmul F zero add mul opp).
  Local Notation peval := (@eval F zero add mul).
  Local Notation pw := (@pw F one mul).

  Definition psub (f alpha : list F) : list F := padd f (pscale (opp one) alpha).

  Lemma psub_eval : forall f alpha z, peval (psub f alpha) z = peval f z - peval alpha z.
  Proof. intros. unfold psub. rewrite eval_padd, eval_pscale. field. Qed.

  Lemma psub_length : forall f alpha, length f = length alpha -> length (psub f alpha) = length f.
  Proof. intros f alpha h. unfold psub. rewrite length_padd, length_pscale. lia. Qed.

  Theorem slot_swap_products : forall (N : nat) (zs f g f' g' alpha : list F),
    (0 < N)%nat -> NoDup zs -> length zs = N ->
    (forall z, In z zs -> pw z N = opp one) ->
    length f = N -> length g = N -> length f' = N -> length g' = N -> length alpha = N ->
    (forall z, In z zs ->
       (peval f' z = peval f z /\ peval g' z = peval g z) \/
       (peval f' z = peval g z /\ peval g' z = peval f z)) ->
    nmul (psub f alpha) (psub g alpha) = nmul (psub f' alpha) (psub g' alpha).
  Proof.
    intros N zs f g f' g' alpha hN hnd hzs hroots hf hg hf' hg' ha hslots.
    assert (hne : forall x y : list F, length x = N -> length y = N -> psub x y <> []).
    { intros x y hx hy e. apply (f_equal (@length F)) in e. rewrite psub_length in e by lia. cbn in e. lia. }
    apply (@poly_eq_of_evals F zero one add mul sub div opp inv Fdec Hf N zs); try assumption.
    + rewrite nmul_length by (apply hne; assumption). rewrite psub_length; lia.
    + rewrite nmul_length by (apply hne; assumption). rewrite psub_length; lia.
    + intros z hz.
      rewrite !(nmul_eval N z (hroots z hz)) by (rewrite psub_length; lia).
      rewrite !psub_eval.
      destruct (hslots z hz) as [[e1 e2] | [e1 e2]]; rewrite e1, e2; field.
  Qed.

End SlotAttack.

(* ---------------------------------------------------------------------- *)
(* The instance over Z_17 with N = 4 (the numbers of paper/tutorial.tex). *)

Section SlotAttack17.

  Lemma prime17 : prime 17.
  Proof.
    apply prime_intro; [lia |]. intros n hn.
    assert (h : (n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/
                 n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16)%Z) by lia.
    repeat (destruct h as [h | h]; [subst n; apply Zgcd_1_rel_prime; reflexivity |]).
    subst n; apply Zgcd_1_rel_prime; reflexivity.
  Qed.

  Local Notation F17 := (@Zpfield.Zp 17).
  Local Notation zero17 := (@Zpfield.zero 17 prime17).
  Local Notation one17 := (@Zpfield.one 17 prime17).
  Local Notation add17 := (@Zpfield.zp_add 17).
  Local Notation mul17 := (@Zpfield.zp_mul 17).
  Local Notation sub17 := (@Zpfield.zp_sub 17).
  Local Notation div17 := (@Zpfield.zp_div 17).
  Local Notation opp17 := (@Zpfield.zp_opp 17 prime17).
  Local Notation inv17 := (@Zpfield.zp_inv 17).
  Local Notation nmul17 := (@nmul F17 zero17 add17 mul17 opp17).
  Local Notation psub17 := (@psub F17 one17 add17 mul17 opp17).
  Local Notation dot17 := (@dot F17 zero17 add17 mul17).
  Local Notation peval17 := (@eval F17 zero17 add17 mul17).
  Local Notation pw17 := (@pw F17 one17 mul17).

  Definition z17 (n : Z) : F17 := Zpfield.mk_zp (n mod 17) (Zmod_mod n 17).

  Lemma zp_v_inj : forall x y : F17, Zpfield.v x = Zpfield.v y -> x = y.
  Proof. intros [x hx] [y hy] e. cbn in e. apply Zpfield.construct_zp; exact e. Qed.

  Definition f17 : list F17 := map z17 [1; 2; 3; 4]%Z.
  Definition g17 : list F17 := map z17 [5; 0; 7; 1]%Z.
  Definition f17' : list F17 := map z17 [16; 1; 11; 8]%Z.
  Definition g17' : list F17 := map z17 [7; 1; 16; 14]%Z.
  Definition roots17 : list F17 := map z17 [2; 8; 15; 9]%Z.
  Definition rho17 : list F17 := map z17 [3; 7; 1; 10]%Z.

  Ltac zp_eq := apply zp_v_inj; vm_compute; reflexivity.
  Ltac zp_neq := let e := fresh in intro e; apply (f_equal Zpfield.v) in e; vm_compute in e; discriminate.
  Ltac zpl_neq := let e := fresh in intro e; apply (f_equal (map Zpfield.v)) in e; vm_compute in e; discriminate.

  (* The ring-level product test accepts for every alpha. *)
  Theorem slot_attack_ring_test : forall alpha : list F17, length alpha = 4%nat ->
    nmul17 (psub17 f17 alpha) (psub17 g17 alpha) = nmul17 (psub17 f17' alpha) (psub17 g17' alpha).
  Proof.
    intros alpha ha.
    apply (@slot_swap_products F17 zero17 one17 add17 mul17 sub17 div17 opp17 inv17
             (@Zpfield.zp_dec 17) (@Zpfield.zp_field 17 prime17) 4 roots17); try reflexivity; try lia; try exact ha.
    + unfold roots17; cbn [map]. repeat constructor; cbn; intro h;
        repeat (destruct h as [h | h]; [revert h; zp_neq |]); exact h.
    + intros z hz. unfold roots17 in hz; cbn in hz.
      destruct hz as [<- | [<- | [<- | [<- | []]]]]; zp_eq.
    + intros z hz. unfold roots17 in hz; cbn in hz.
      destruct hz as [<- | [<- | [<- | [<- | []]]]];
        [right | left | left | left]; split; zp_eq.
  Qed.

  (* The lists are different multisets: f17 is neither f17' nor g17'. *)
  Theorem slot_attack_lists_differ : f17 <> f17' /\ f17 <> g17'.
  Proof. split; zpl_neq. Qed.

  (* The projection along rho17 separates them: 9 is neither 10 nor 14. *)
  Theorem slot_attack_projection_sees :
    dot17 rho17 f17 <> dot17 rho17 f17' /\ dot17 rho17 f17 <> dot17 rho17 g17'.
  Proof. split; zp_neq. Qed.

End SlotAttack17.
