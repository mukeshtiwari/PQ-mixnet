(* Zero knowledge of the opening (paper, Theorem 5.3, steps (4) and (5)).

   The prover's randomness in the opening is
     - for every data row i, its nq pads (data row: data symbols followed
       by pads, see ReedSolomon.v);
     - for every masked vector (one per slot, one per matrix for the
       proximity test), a uniform mask of length kk.

   What the verifier sees, apart from values that its own checks determine
   (mu, and the entries of the mask rows in the opened columns), is
     - the entries of every data row in the nq opened columns J;
     - the masked vectors  mask + shift, where the shifts
       (c * u_v, and sum_i gamma_i row_i) depend on the data and the pads
       in any way: they are given by an arbitrary function tfun of the pads.

   Theorems oview_inj and oview_surj: for nq distinct columns J below n,
   the map (pads, masks) |-> (opened entries, masked vectors) is a
   bijection between randomness of the right shape and views of the right
   shape. So the view is uniform, whatever the data. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks.
Import ListNotations.

Section ZkOpen.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Local Notation pw := (@pw F one mul).
  Local Notation padd := (@padd F add).
  Local Notation opened := (@opened F zero one add mul).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Variable omega : F.
  Variable n : nat.
  Hypothesis Hnodes : forall i j, (i < n)%nat -> (j < n)%nat -> pw omega i = pw omega j -> i = j.
  Hypothesis Homega : omega <> zero.

  Variable J : list nat.
  Hypothesis HJnd : NoDup J.
  Hypothesis HJ : forall j, In j J -> (j < n)%nat.

  (* one row: pads |-> opened entries is a bijection of F^nq *)
  Lemma row_surj : forall (data ys : list F), length ys = length J ->
    exists pads, length pads = length J /\ opened omega data pads J = ys.
  Proof.
    intros data ys hl.
    pose proof (@rs_hiding F zero one add mul sub div opp inv Fdec Hf omega n Hnodes Homega lf Hnd Hall data J HJnd HJ) as hp.
    assert (hin : In ys (all_lists lf (length J))).
    { apply all_lists_In. split; [exact hl | apply Forall_forall; intros y _; apply Hall]. }
    apply (Permutation_in _ (Permutation_sym hp)) in hin.
    apply in_map_iff in hin. destruct hin as (pads & e & hpads).
    apply all_lists_In in hpads. exists pads. split; [tauto | exact e].
  Qed.

  Fixpoint zipw {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B) : list C :=
    match la, lb with
    | a :: la', b :: lb' => f a b :: zipw f la' lb'
    | _, _ => []
    end.

  Definition lens (d : nat) (ls : list (list F)) : Prop := Forall (fun l => length l = d) ls.

  Lemma rows_inj : forall (datas pads pads' : list (list F)),
    length pads = length datas -> length pads' = length datas ->
    lens (length J) pads -> lens (length J) pads' ->
    zipw (fun d p => opened omega d p J) datas pads = zipw (fun d p => opened omega d p J) datas pads' ->
    pads = pads'.
  Proof.
    induction datas as [| d ds ih]; intros pads pads' hl hl' hs hs' e;
      destruct pads as [| p ps], pads' as [| p' ps']; cbn in hl, hl'; try lia; [reflexivity |].
    inversion hs as [| ? ? hp hps]; subst. inversion hs' as [| ? ? hp' hps']; subst.
    cbn [zipw] in e. inversion e as [[e1 e2]]. f_equal.
    + exact (@rs_hiding_inj F zero one add mul sub div opp inv Fdec Hf omega n Hnodes Homega d J p p' HJnd HJ hp hp' e1).
    + apply (ih ps ps'); [lia | lia | assumption | assumption | exact e2].
  Qed.

  Lemma rows_surj : forall (datas ys : list (list F)), length ys = length datas -> lens (length J) ys ->
    exists pads, length pads = length datas /\ lens (length J) pads /\
      zipw (fun d p => opened omega d p J) datas pads = ys.
  Proof.
    induction datas as [| d ds ih]; intros ys hl hs; destruct ys as [| y ys']; cbn in hl; try lia.
    + exists []; split; [reflexivity | split; [constructor | reflexivity]].
    + inversion hs as [| ? ? hy hys]; subst.
      destruct (ih ys' ltac:(lia) hys) as (ps & hpl & hps & e).
      destruct (row_surj d y hy) as (p & hp & ep).
      exists (p :: ps). split; [cbn; lia | split; [constructor; assumption |]].
      cbn [zipw]. rewrite ep, e. reflexivity.
  Qed.

  Lemma masks_inj : forall (ts ms ms' : list (list F)) (kk : nat),
    length ms = length ts -> length ms' = length ts -> lens kk ms -> lens kk ms' ->
    zipw padd ms ts = zipw padd ms' ts -> ms = ms'.
  Proof.
    induction ts as [| t ts ih]; intros ms ms' kk hl hl' hs hs' e;
      destruct ms as [| m0 ms1], ms' as [| m0' ms1']; cbn in hl, hl'; try lia; [reflexivity |].
    inversion hs as [| ? ? hm hms]; subst. inversion hs' as [| ? ? hm' hms']; subst.
    cbn [zipw] in e. inversion e as [[e1 e2]]. f_equal.
    + apply (@shift_list_inj F zero one add mul sub div opp inv Hf t m0 m0'); [lia | exact e1].
    + apply (ih ms1 ms1' (length m0)); [lia | lia | assumption | assumption | exact e2].
  Qed.

  Lemma masks_surj : forall (ts ys : list (list F)) (kk : nat),
    length ys = length ts -> lens kk ys -> Forall (fun t => (length t <= kk)%nat) ts ->
    exists ms, length ms = length ts /\ lens kk ms /\ zipw padd ms ts = ys.
  Proof.
    induction ts as [| t ts ih]; intros ys kk hl hs ht; destruct ys as [| y ys']; cbn in hl; try lia.
    + exists []; split; [reflexivity | split; [constructor | reflexivity]].
    + inversion hs as [| ? ? hy hys]; subst. inversion ht as [| ? ? htl hts]; subst.
      destruct (ih ys' (length y) ltac:(lia) hys hts) as (ms & hml & hms & e).
      destruct (@shift_list_surj F zero one add mul sub div opp inv Hf t y htl) as (m0 & hm0 & em).
      exists (m0 :: ms). split; [cbn; lia | split; [constructor; assumption |]].
      cbn [zipw]. rewrite em, e. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)

  Variable datas : list (list F).                       (* data symbols of the data rows *)
  Variable kk nm : nat.                                 (* length and number of the masked vectors *)
  Variable tfun : list (list F) -> list (list F).       (* the shifts, as a function of the pads *)
  Hypothesis Htlen : forall pads, length (tfun pads) = nm.
  Hypothesis Htk : forall pads, Forall (fun t => (length t <= kk)%nat) (tfun pads).

  Definition orand : Type := (list (list F) * list (list F))%type.

  Definition shaped_orand (x : orand) : Prop :=
    length (fst x) = length datas /\ lens (length J) (fst x) /\ length (snd x) = nm /\ lens kk (snd x).

  Definition oview (x : orand) : orand :=
    (zipw (fun d p => opened omega d p J) datas (fst x), zipw padd (snd x) (tfun (fst x))).

  Theorem oview_inj : forall x x', shaped_orand x -> shaped_orand x' -> oview x = oview x' -> x = x'.
  Proof.
    intros [pads ms] [pads' ms'] (h1 & h2 & h3 & h4) (h1' & h2' & h3' & h4') e. cbn [fst snd] in *.
    unfold oview in e. cbn [fst snd] in e. inversion e as [[e1 e2]].
    assert (ep : pads = pads') by (apply (rows_inj datas pads pads' h1 h1' h2 h2' e1)).
    subst pads'. f_equal.
    apply (masks_inj (tfun pads) ms ms' kk); try assumption; rewrite Htlen; assumption.
  Qed.

  Theorem oview_surj : forall v, shaped_orand v -> exists x, shaped_orand x /\ oview x = v.
  Proof.
    intros [ys zs] (h1 & h2 & h3 & h4). cbn [fst snd] in *.
    destruct (rows_surj datas ys h1 h2) as (pads & hpl & hps & e1).
    destruct (masks_surj (tfun pads) zs kk ltac:(rewrite Htlen; exact h3) h4 (Htk pads)) as (ms & hml & hms & e2).
    exists (pads, ms). split.
    + unfold shaped_orand. cbn [fst snd]. rewrite Htlen in hml. tauto.
    + unfold oview. cbn [fst snd]. rewrite e1, e2. reflexivity.
  Qed.

End ZkOpen.
