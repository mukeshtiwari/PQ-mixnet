(* From the logarithmic-derivative identity to the shuffle relation (paper,
   proof of Theorem 5.2, paragraph "Multisets", and its first budget line).

   rr i is re-randomised input i, that is c_i + Enc_0(w_i) for the decoded
   witness; co j is output j; sg j is the decoded value of sigma at j, an
   arbitrary field element. A tagged ciphertext is the linear form

       form c tag = (-1) :: fst c ++ snd c ++ [tag],

   and at the point  alpha :: rho_u ++ rho_v ++ [beta]  it takes the value
   proj rho c + beta * tag - alpha  (dot_form), which is h_i for the
   inputs and hhat_j for the outputs.

   - perm_witness: if the tagged inputs and the tagged outputs are equal as
     multisets, there is a permutation pi of 0..tau-1 with
     co j = rr (pi j) and sg j = pi j for all j. So the decoded sigma is
     a permutation and the outputs are the re-randomised inputs in that
     order.
   - multiset_step: otherwise the logarithmic-derivative identity holds,
     with non-zero denominators, for at most (2 tau - 1) |F|^(2N+1) of the
     |F|^(2N+2) challenges (rho, alpha, beta). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Negacyclic Bgv.
Import ListNotations.

Section MixMultiset.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation nF := (@nF F zero one add).
  Local Notation proj := (@proj F zero add mul).
  Local Notation ctx := (@ctx F).

  Definition form (c : ctx) (tag : F) : list F := opp one :: (fst c ++ snd c ++ [tag]).

  Definition point (ru rv : list F) (alpha beta : F) : list F := alpha :: (ru ++ rv ++ [beta]).

  Lemma dot_form : forall (c : ctx) (tag : F) (ru rv : list F) (alpha beta : F),
    length (fst c) = length ru -> length (snd c) = length rv ->
    dot (form c tag) (point ru rv alpha beta) = proj ru rv c + beta * tag - alpha.
  Proof.
    intros c tag ru rv alpha beta hu hv. unfold form, point, Bgv.proj.
    cbn [LogDer.dot]. rewrite dot_app by exact hu. rewrite dot_app by exact hv.
    rewrite (dot_sym (fst c)), (dot_sym (snd c)). cbn. field.
  Qed.

  Lemma form_last : forall c tag, last (form c tag) zero = tag.
  Proof.
    intros c tag. unfold form. rewrite app_assoc, app_comm_cons. apply last_last.
  Qed.

  Lemma app_inj_len : forall (x x' y y' : list F), length x = length x' ->
    x ++ y = x' ++ y' -> x = x' /\ y = y'.
  Proof.
    induction x as [| a x ih]; intros x' y y' hl e; destruct x' as [| a' x']; cbn in hl; try lia.
    + split; [reflexivity | exact e].
    + cbn in e. inversion e as [[e1 e2]]. destruct (ih x' y y' ltac:(lia) e2) as [-> ->]. split; reflexivity.
  Qed.

  Lemma form_inj : forall c c' tag tag', length (fst c) = length (fst c') ->
    form c tag = form c' tag' -> c = c' /\ tag = tag'.
  Proof.
    intros [u v] [u' v'] tag tag' hl e. unfold form in e. cbn [fst snd] in *.
    inversion e as [e1]. destruct (app_inj_len u u' _ _ hl e1) as [-> e2].
    apply app_inj_tail in e2. destruct e2 as [-> ->]. split; reflexivity.
  Qed.

  Lemma choose_list : forall (n : nat) (R : nat -> nat -> Prop),
    (forall j, (j < n)%nat -> exists i, R j i) ->
    exists l, length l = n /\ forall j, (j < n)%nat -> R j (nth j l 0%nat).
  Proof.
    induction n as [| n ih]; intros R h.
    + exists []; split; [reflexivity | intros j hj; lia].
    + destruct (ih R (fun j hj => h j ltac:(lia))) as (l & hl & hR).
      destruct (h n ltac:(lia)) as (i & hi).
      exists (l ++ [i]); split; [rewrite length_app; cbn; lia |].
      intros j hj. destruct (Nat.eq_dec j n) as [-> | hne].
      - rewrite app_nth2 by lia. rewrite hl, Nat.sub_diag. exact hi.
      - rewrite app_nth1 by lia. apply hR; lia.
  Qed.

  Lemma map_nth_seq : forall (l : list nat), map (fun j => nth j l 0%nat) (seq 0 (length l)) = l.
  Proof.
    intro l. apply (nth_ext _ _ 0%nat 0%nat); [rewrite length_map, length_seq; reflexivity |].
    intros i hi. rewrite length_map, length_seq in hi.
    rewrite (nth_indep _ 0%nat (nth 0 l 0%nat)) by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth (fun j => nth j l 0%nat) (seq 0 (length l)) 0%nat i).
    rewrite seq_nth by exact hi. reflexivity.
  Qed.

  Variables (N tau : nat).
  Variables (rr co : nat -> ctx) (sg : nat -> F).

  Hypothesis Hchar : forall k, (0 < k <= tau)%nat -> nF k <> zero.
  Hypothesis Hrr : forall i, (i < tau)%nat -> length (fst (rr i)) = N /\ length (snd (rr i)) = N.
  Hypothesis Hco : forall j, (j < tau)%nat -> length (fst (co j)) = N /\ length (snd (co j)) = N.

  Definition Sin : list (list F) := map (fun i => form (rr i) (nF i)) (seq 0 tau).
  Definition Tout : list (list F) := map (fun j => form (co j) (sg j)) (seq 0 tau).

  Definition is_shuffle : Prop :=
    exists pi : list nat, Permutation pi (seq 0 tau) /\
      forall j, (j < tau)%nat -> co j = rr (nth j pi 0%nat) /\ sg j = nF (nth j pi 0%nat).

  Theorem perm_witness : Permutation Sin Tout -> is_shuffle.
  Proof.
    intro hp.
    assert (hpre : forall j, (j < tau)%nat -> exists i, (i < tau)%nat /\ co j = rr i /\ sg j = nF i).
    { intros j hj.
      assert (hin : In (form (co j) (sg j)) Sin).
      { apply (Permutation_in _ (Permutation_sym hp)). unfold Tout.
        apply (in_map (fun j0 => form (co j0) (sg j0))). apply in_seq; lia. }
      unfold Sin in hin. apply in_map_iff in hin. destruct hin as (i & e & hi). apply in_seq in hi.
      exists i; split; [lia |].
      destruct (form_inj (rr i) (co j) (nF i) (sg j)) as [e1 e2]; [| exact e | split; congruence].
      rewrite (proj1 (Hrr i ltac:(lia))), (proj1 (Hco j hj)). reflexivity. }
    destruct (choose_list tau _ hpre) as (pi & hlen & hpi).
    exists pi; split; [| intros j hj; destruct (hpi j hj) as (_ & h1 & h2); split; assumption].
    (* the tags of the two multisets *)
    assert (htags : Permutation (map nF (seq 0 tau)) (map nF pi)).
    { assert (h1 : map (fun x => last x zero) Sin = map nF (seq 0 tau)).
      { unfold Sin. rewrite map_map. apply map_ext. intro i. apply form_last. }
      assert (h2 : map (fun x => last x zero) Tout = map nF pi).
      { unfold Tout. rewrite map_map.
        transitivity (map nF (map (fun j => nth j pi 0%nat) (seq 0 (length pi)))); [| rewrite map_nth_seq; reflexivity].
        rewrite hlen, map_map.
        apply map_ext_in. intros j hj. apply in_seq in hj. rewrite form_last.
        exact (proj2 (proj2 (hpi j ltac:(lia)))). }
      rewrite <-h1, <-h2. apply Permutation_map. exact hp. }
    assert (hndF : NoDup (map nF (seq 0 tau))).
    { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
      intros i j hi hj e. apply in_seq in hi. apply in_seq in hj.
      apply (@nF_inj F zero one add mul sub div opp inv Hf tau Hchar); [lia | lia | exact e]. }
    assert (hnd : NoDup pi).
    { apply (NoDup_map_inv nF). apply (Permutation_NoDup htags). exact hndF. }
    apply NoDup_Permutation_bis; [exact hnd | rewrite length_seq; lia |].
    intros x hx. destruct (In_nth pi x 0%nat hx) as (j & hj & <-).
    apply in_seq. destruct (hpi j ltac:(lia)) as (h & _). lia.
  Qed.

  Theorem multiset_step : forall (lf : list F), NoDup lf -> (forall x, In x lf) ->
    ~ is_shuffle ->
    forall bad : list F -> bool,
    (forall p, bad p = true ->
       (forall a, In a (Sin ++ Tout) -> dot a p <> zero) /\
       fsum (map (fun a => inv (dot a p)) Sin) = fsum (map (fun a => inv (dot a p)) Tout)) ->
    (length (filter bad (all_lists lf (S (N + N + 1)))) <= (2 * tau - 1) * length lf ^ (N + N + 1))%nat.
  Proof.
    intros lf hnd hall hns bad hbad.
    apply (@logder_count F zero one add mul sub div opp inv Fdec Hf lf hnd hall (N + N + 1) tau Sin Tout bad).
    + unfold Sin. rewrite length_map, length_seq. reflexivity.
    + unfold Tout. rewrite length_map, length_seq. reflexivity.
    + intros a ha. apply in_app_or in ha. unfold Sin, Tout in ha.
      destruct ha as [ha | ha]; apply in_map_iff in ha; destruct ha as (i & <- & hi); apply in_seq in hi.
      - exists (fst (rr i) ++ snd (rr i) ++ [nF i]); split; [reflexivity |].
        rewrite !length_app. destruct (Hrr i ltac:(lia)) as [-> ->]. cbn. lia.
      - exists (fst (co i) ++ snd (co i) ++ [sg i]); split; [reflexivity |].
        rewrite !length_app. destruct (Hco i ltac:(lia)) as [-> ->]. cbn. lia.
    + exact Hchar.
    + intro hp. apply hns. apply perm_witness. exact hp.
    + exact hbad.
  Qed.

End MixMultiset.
