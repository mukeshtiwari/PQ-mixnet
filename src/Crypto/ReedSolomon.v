(* The Reed-Solomon row code of the paper (Section 4.1) as an instance of
   the abstract code of Proximity.v, and the hiding lemma (Lemma 4.4).

   The code has length n and messages of at most k coefficients. A message
   p is the polynomial with these coefficients, and column j of its
   codeword is p(omega^j). The only assumption on omega is that the nodes
   omega^0, .., omega^(n-1) are pairwise distinct (omega has order at
   least n); for hiding also omega <> 0.

   - rs_ext, rs_add, rs_scale, rs_dist: the code is linear with distance
     n - k + 1. These are exactly the hypotheses of Section Proximity.
   - rs_prox_affine: Lemma 4.2 (Delta = 3) for this code, given the line
     lemma for it.
   - rs_hiding_inj, rs_hiding: Lemma 4.4. For a row made of data symbols
     followed by nq pads, and any nq distinct columns, the map from the
     pads to the entries in these columns is a bijection of F^nq, whatever
     the data. So uniform pads give uniform opened entries, independent
     of the data. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity.
Import ListNotations.

Section ReedSolomon.

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
  Local Notation peval := (@eval F zero add mul).
  Local Notation pz := (@pzero F zero).
  Local Notation pw := (@pw F one mul).
  Local Notation pi := (@pi F zero add mul).
  Local Notation mul_nonzero := (@mul_nonzero F zero one add mul sub div opp inv Hf).

  Variable omega : F.
  Variables n k : nat.
  Hypothesis Hk : (k <= n)%nat.
  Hypothesis Hnodes : forall i j, (i < n)%nat -> (j < n)%nat -> pw omega i = pw omega j -> i = j.

  Definition rs_enc (p : list F) (j : nat) : F := peval p (pw omega j).

  Definition rs_code (c : nat -> F) : Prop :=
    exists p : list F, (length p <= k)%nat /\ forall j, (j < n)%nat -> c j = rs_enc p j.

  Lemma rs_ext : forall c c', (forall j, (j < n)%nat -> c j = c' j) -> rs_code c -> rs_code c'.
  Proof.
    intros c c' h (p & hp & hc). exists p; split; [exact hp |].
    intros j hj. rewrite <-(h j hj). exact (hc j hj).
  Qed.

  Lemma rs_add : forall c1 c2, rs_code c1 -> rs_code c2 -> rs_code (fun j => c1 j + c2 j).
  Proof.
    intros c1 c2 (p1 & hp1 & h1) (p2 & hp2 & h2). exists (padd p1 p2); split.
    + rewrite length_padd; lia.
    + intros j hj. unfold rs_enc. rewrite eval_padd, (h1 j hj), (h2 j hj). reflexivity.
  Qed.

  Lemma rs_scale : forall t c, rs_code c -> rs_code (fun j => t * c j).
  Proof.
    intros t c (p & hp & h). exists (pscale t p); split.
    + rewrite length_pscale; exact hp.
    + intros j hj. unfold rs_enc. rewrite eval_pscale, (h j hj). reflexivity.
  Qed.

  (* Distance n - k + 1. *)
  Theorem rs_dist : forall c1 c2 (E : list nat), rs_code c1 -> rs_code c2 ->
    (length E < n - k + 1)%nat ->
    (forall j, (j < n)%nat -> ~ In j E -> c1 j = c2 j) -> forall j, (j < n)%nat -> c1 j = c2 j.
  Proof.
    intros c1 c2 E (p1 & hp1 & h1) (p2 & hp2 & h2) hE hagree.
    set (df := padd p1 (pscale (opp one) p2)).
    assert (hdf : forall x, peval df x = peval p1 x - peval p2 x).
    { intro x. unfold df. rewrite eval_padd, eval_pscale. field. }
    assert (hlen : (length df <= k)%nat).
    { unfold df. rewrite length_padd, length_pscale. lia. }
    destruct (@pzero_dec F zero Fdec df) as [hz | hnz].
    + intros j hj. rewrite (h1 j hj), (h2 j hj). unfold rs_enc.
      pose proof (@eval_pzero F zero one add mul sub div opp inv Hf df (pw omega j) hz) as h0.
      rewrite hdf in h0.
      assert (e : peval p1 (pw omega j) = (peval p1 (pw omega j) - peval p2 (pw omega j)) + peval p2 (pw omega j)) by field.
      rewrite e, h0. field.
    + exfalso.
      set (J := filter (fun j => negb (memb j E)) (seq 0 n)).
      assert (hJn : forall j, In j J -> (j < n)%nat /\ ~ In j E).
      { intros j hj. apply filter_In in hj; destruct hj as [hj hm]. apply in_seq in hj. split; [lia |].
        intro i. apply memb_true in i. rewrite i in hm. discriminate. }
      assert (hJlen : (n <= length J + length E)%nat).
      { pose proof (filter_notin_length (seq 0 n) E (seq_NoDup n 0)) as h. rewrite length_seq in h. exact h. }
      assert (hnd : NoDup (map (pw omega) J)).
      { apply NoDup_map_NoDup_ForallPairs; [| apply NoDup_filter, seq_NoDup].
        intros i j hi hj e. apply Hnodes; [apply hJn; exact hi | apply hJn; exact hj | exact e]. }
      assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf (length df) df (le_n _) hnz
                (map (pw omega) J) hnd).
      assert (hr : forall r, In r (map (pw omega) J) -> peval df r = zero).
      { intros r hr. apply in_map_iff in hr; destruct hr as (j & <- & hj).
        destruct (hJn j hj) as [hjn hjE]. specialize (hagree j hjn hjE).
        rewrite (h1 j hjn), (h2 j hjn) in hagree. unfold rs_enc in hagree.
        rewrite hdf, hagree. field. }
      specialize (hlt hr). rewrite length_map in hlt. lia.
  Qed.

  (* Lemma 4.2, Delta = 3, for the Reed-Solomon code. *)
  Theorem rs_prox_affine : forall (lf : list F), NoDup lf -> (forall x, In x lf) ->
    forall e : nat, (2 * e < n - k + 1)%nat -> (e + 1 < length lf)%nat ->
    (forall (x y : nat -> F) (ts : list F), NoDup ts -> (e + 1 < length ts)%nat ->
       (forall t, In t ts -> close n e rs_code (fun j => x j + t * y j)) ->
       exists E cx cy, (length E <= e)%nat /\ rs_code cx /\ rs_code cy /\
         agree_out n E x cx /\ agree_out n E y cy) ->
    forall (m : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close n e rs_code (pi m rows g)) ->
    ((e + 2) * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= e)%nat /\ rs_code cm /\ agree_out n E m cm /\
      Forall2 (fun r c => rs_code c /\ agree_out n E r c) rows cs.
  Proof.
    intros lf hnd hall e he hq hline m rows cl hcl hmany.
    exact (@prox_affine F zero one add mul sub div opp inv Fdec Hf lf hnd hall n (n - k + 1) e rs_code
             rs_ext rs_add rs_scale rs_dist he hq hline m rows cl hcl hmany).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Hiding *)

  Hypothesis Homega : omega <> zero.

  Lemma pw_nonzero : forall x : F, x <> zero -> forall j, pw x j <> zero.
  Proof.
    intros x hx; induction j as [| j ih]; cbn.
    + intro e; exact (@zero_neq_one F eq zero one _ (eq_sym e)).
    + apply mul_nonzero; assumption.
  Qed.

  Definition opened (data pads : list F) (J : list nat) : list F :=
    map (fun j => rs_enc (data ++ pads) j) J.

  Theorem rs_hiding_inj : forall (data : list F) (J : list nat) (pads pads' : list F),
    NoDup J -> (forall j, In j J -> (j < n)%nat) ->
    length pads = length J -> length pads' = length J ->
    opened data pads J = opened data pads' J -> pads = pads'.
  Proof.
    intros data J pads pads' hnd hJ hl hl' e.
    apply (@poly_eq_of_evals F zero one add mul sub div opp inv Fdec Hf (length J) (map (pw omega) J));
      try assumption.
    + apply NoDup_map_NoDup_ForallPairs; [| exact hnd].
      intros i j hi hj e2. apply Hnodes; [apply hJ; exact hi | apply hJ; exact hj | exact e2].
    + apply length_map.
    + intros z hz. apply in_map_iff in hz; destruct hz as (j & <- & hj).
      assert (ej : rs_enc (data ++ pads) j = rs_enc (data ++ pads') j).
      { unfold opened in e.
        revert e hj. clear. induction J as [| a J ih]; intros e hj; [contradiction |].
        cbn in e. inversion e as [[e1 e2]]. destruct hj as [-> | hj]; [exact e1 | exact (ih e2 hj)]. }
      unfold rs_enc in ej. rewrite !peval_app in ej.
      set (x := pw omega j) in *.
      assert (hx : pw x (length data) <> zero) by (apply pw_nonzero, pw_nonzero; exact Homega).
      assert (h1 : pw x (length data) * peval pads x = pw x (length data) * peval pads' x).
      { assert (h2 : pw x (length data) * peval pads x
                     = (peval data x + pw x (length data) * peval pads x) - peval data x) by field.
        rewrite h2, ej. field. }
      assert (h3 : peval pads x = inv (pw x (length data)) * (pw x (length data) * peval pads x))
        by (field; exact hx).
      rewrite h3, h1. field. exact hx.
  Qed.

  (* Uniform pads give uniform opened entries: the map from pads to opened
     entries permutes F^nq. *)
  Theorem rs_hiding : forall (lf : list F), NoDup lf -> (forall x, In x lf) ->
    forall (data : list F) (J : list nat),
    NoDup J -> (forall j, In j J -> (j < n)%nat) ->
    Permutation (map (fun pads => opened data pads J) (all_lists lf (length J)))
                (all_lists lf (length J)).
  Proof.
    intros lf hnd hall data J hJnd hJ.
    apply map_self_perm.
    + apply all_lists_NoDup; exact hnd.
    + intros pads hp. apply all_lists_In. split.
      - unfold opened. apply length_map.
      - apply Forall_forall; intros y _; apply hall.
    + intros x y hx hy e.
      apply all_lists_In in hx; destruct hx as [hx _].
      apply all_lists_In in hy; destruct hy as [hy _].
      exact (rs_hiding_inj data J x y hJnd hJ hx hy e).
  Qed.

End ReedSolomon.
