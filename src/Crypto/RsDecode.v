(* Decoding the Reed-Solomon row code by search, and the decoding
   hypotheses of open_sound.

   The decoder is not meant to be run: it enumerates all |F|^k messages.
   It exists so that "the decoded row" is a function of the committed word,
   which is what the extractor of Theorem 5.2 needs, and so that closeness
   to the code is a boolean.

     dist x p   number of columns j < n with x j <> enc p j
     dec x      the first message p of length k with dist x p <= e, if any
     closeb x   whether such a message exists

   - closeb_spec: closeb x = true exactly when x is within e of the code
     (in the sense close of Proximity.v);
   - dec_agree: if x agrees with some codeword outside a set E of at most e
     columns, then it agrees with enc (dec x) outside the same E, and
     dec x has length k. (Unique decoding: 2e < d.)
   - far_of_closeb, dec_many: the hypotheses HfarB/S and HdecB/S of
     open_sound for the rows rws of a matrix (xm is the proximity mask), P i = dec (X i) and
     clb g = closeb (the combination with coefficients g), from a
     proximity lemma Prox for this code. For Delta = 3, Prox with
     pn = e + 2 is rs_prox_affine. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon.
Import ListNotations.

Section RsDecode.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation peval := (@eval F zero add mul).
  Local Notation pw := (@pw F one mul).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation pi := (@pi F zero add mul).

  Variable lf : list F.
  Hypothesis Hall : forall x, In x lf.

  Variable omega : F.
  Variables n k e : nat.
  Hypothesis Hk : (k <= n)%nat.
  Hypothesis Hnodes : forall i j, (i < n)%nat -> (j < n)%nat -> pw omega i = pw omega j -> i = j.
  Hypothesis He : (2 * e < n - k + 1)%nat.

  Local Notation rs_enc := (@rs_enc F zero one add mul omega).
  Local Notation rs_code := (@rs_code F zero one add mul omega n k).

  Definition msgs : list (list F) := all_lists lf k.

  Definition diff (x : nat -> F) (p : list F) : list nat :=
    filter (fun j => negb (feqb (x j) (rs_enc p j))) (seq 0 n).

  Definition near (x : nat -> F) (p : list F) : bool := Nat.leb (length (diff x p)) e.

  Definition dec (x : nat -> F) : list F :=
    match find (near x) msgs with
    | Some p => p
    | None => []
    end.

  Definition closeb (x : nat -> F) : bool := existsb (near x) msgs.

  (* padding a message with zeros does not change its codeword *)
  Lemma peval_zeros : forall r x, peval (repeat zero r) x = zero.
  Proof. induction r as [| r ih]; intro x; cbn; [reflexivity | rewrite ih; field]. Qed.

  Lemma pad_msg : forall p : list F, (length p <= k)%nat ->
    exists p', In p' msgs /\ forall j, rs_enc p' j = rs_enc p j.
  Proof.
    intros p hp. exists (p ++ repeat zero (k - length p)). split.
    + unfold msgs. apply all_lists_In. split.
      - rewrite length_app, repeat_length. lia.
      - apply Forall_forall. intros y _. apply Hall.
    + intro j. unfold ReedSolomon.rs_enc.
      rewrite (@peval_app F zero one add mul sub div opp inv Hf), peval_zeros. field.
  Qed.

  Lemma diff_agree : forall x p E, incl (diff x p) E -> agree_out n E x (rs_enc p).
  Proof.
    intros x p E hincl j hj hn.
    destruct (feqb (x j) (rs_enc p j)) eqn:eb; [apply feqb_true; exact eb | exfalso].
    apply hn, hincl. unfold diff. apply filter_In. split; [apply in_seq; lia | rewrite eb; reflexivity].
  Qed.

  Lemma agree_diff : forall x p E, agree_out n E x (rs_enc p) -> incl (diff x p) E.
  Proof.
    intros x p E ha j hj. unfold diff in hj. apply filter_In in hj. destruct hj as [hs hb]. apply in_seq in hs.
    destruct (in_dec Nat.eq_dec j E) as [i | i]; [exact i | exfalso].
    specialize (ha j ltac:(lia) i). apply feqb_true in ha. rewrite ha in hb. discriminate.
  Qed.

  Lemma diff_NoDup : forall x p, NoDup (diff x p).
  Proof. intros. unfold diff. apply NoDup_filter, seq_NoDup. Qed.

  Lemma rs_code_enc' : forall p : list F, (length p <= k)%nat -> rs_code (rs_enc p).
  Proof. intros p hp. exists p; split; [exact hp | reflexivity]. Qed.

  Theorem closeb_spec : forall x, closeb x = true <-> close n e rs_code x.
  Proof.
    intro x. unfold closeb. rewrite existsb_exists. split.
    + intros (p & hp & hn). unfold near in hn. apply Nat.leb_le in hn.
      exists (rs_enc p), (diff x p). split; [| split; [exact hn | apply diff_agree; apply incl_refl]].
      apply rs_code_enc'. unfold msgs in hp. apply all_lists_In in hp. lia.
    + intros (c & E & (p0 & hp0 & hc) & hE & ha).
      destruct (pad_msg p0 hp0) as (p & hp & hpe). exists p. split; [exact hp |].
      unfold near. apply Nat.leb_le.
      assert (hincl : incl (diff x p) E).
      { apply agree_diff. intros j hj hn. rewrite (ha j hj hn), (hc j hj), hpe. reflexivity. }
      pose proof (NoDup_incl_length (diff_NoDup x p) hincl). lia.
  Qed.

  Corollary far_of_closeb : forall x, closeb x = false -> ~ close n e rs_code x.
  Proof. intros x hb hc. apply closeb_spec in hc. rewrite hc in hb. discriminate. Qed.

  Lemma dec_near : forall x, close n e rs_code x -> In (dec x) msgs /\ near x (dec x) = true.
  Proof.
    intros x hc. apply closeb_spec in hc. unfold closeb in hc. apply existsb_exists in hc.
    destruct hc as (p & hp & hn). unfold dec.
    destruct (find (near x) msgs) as [p' |] eqn:ef.
    + apply find_some in ef. exact ef.
    + exfalso. pose proof (find_none _ _ ef p hp) as h. rewrite h in hn. discriminate.
  Qed.

  (* Unique decoding. *)
  Theorem dec_agree : forall (x c : nat -> F) (E : list nat),
    rs_code c -> (length E <= e)%nat -> agree_out n E x c ->
    length (dec x) = k /\ agree_out n E x (rs_enc (dec x)).
  Proof.
    intros x c E hc hE ha.
    assert (hclose : close n e rs_code x) by (exists c, E; tauto).
    destruct (dec_near x hclose) as [hin hn].
    unfold msgs in hin. apply all_lists_In in hin. destruct hin as [hlen _].
    split; [exact hlen |].
    unfold near in hn. apply Nat.leb_le in hn.
    (* the two codewords agree outside E ++ diff, fewer than d columns *)
    assert (heq : forall j, (j < n)%nat -> rs_enc (dec x) j = c j).
    { apply (@rs_dist F zero one add mul sub div opp inv Fdec Hf omega n k Hk Hnodes
               (rs_enc (dec x)) c (E ++ diff x (dec x))).
      + apply rs_code_enc'. lia.
      + exact hc.
      + rewrite length_app. lia.
      + intros j hj hnot.
        assert (h1 : ~ In j E) by (intro i; apply hnot, in_or_app; left; exact i).
        assert (h2 : ~ In j (diff x (dec x))) by (intro i; apply hnot, in_or_app; right; exact i).
        rewrite <-(ha j hj h1). symmetry. exact (diff_agree x (dec x) _ (incl_refl _) j hj h2). }
    intros j hj hnj. rewrite (heq j hj). exact (ha j hj hnj).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The hypotheses of open_sound for one matrix *)

  Lemma Forall2_in_l : forall {A B : Type} (R : A -> B -> Prop) (l : list A) (l' : list B) (a : A),
    Forall2 R l l' -> In a l -> exists b, In b l' /\ R a b.
  Proof.
    intros A B R l l' a h; induction h as [| x y l l' hxy h ih]; intro hin; [contradiction |].
    destruct hin as [<- | hin]; [exists y; split; [left; reflexivity | exact hxy] |].
    destruct (ih hin) as (b & hb & hr). exists b; split; [right; exact hb | exact hr].
  Qed.

  Variable pn : nat.
  Hypothesis Prox : forall (m : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close n e rs_code (pi m rows g)) ->
    (pn * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= e)%nat /\ rs_code cm /\ agree_out n E m cm /\
      Forall2 (fun r c => rs_code c /\ agree_out n E r c) rows cs.

  Variable X : nat -> nat -> F.
  Variable xm : nat -> F.          (* the word of the proximity mask *)
  Variable rws : list nat.

  Definition clM (g : list F) : bool := closeb (pi xm (map X rws) g).

  Theorem far_M : forall g, clM g = false -> ~ close n e rs_code (pi xm (map X rws) g).
  Proof. intros g h. apply far_of_closeb. exact h. Qed.

  Theorem dec_many :
    (pn * length lf ^ length rws < length (filter clM (all_lists lf (length rws))) * length lf)%nat ->
    exists E, (length E <= e)%nat /\
      forall i, In i rws ->
        (length (dec (X i)) <= k)%nat /\ agree_out n E (X i) (rs_enc (dec (X i))).
  Proof.
    intro hmany.
    destruct (Prox xm (map X rws) clM) as (E & cm & cs & hE & hcm & hagm & hrows).
    + intros g hg. apply closeb_spec. exact hg.
    + rewrite length_map. exact hmany.
    + exists E. split; [exact hE |]. intros i hi.
      destruct (Forall2_in_l _ _ _ (X i) hrows (in_map X rws i hi)) as (c & _ & hc & hag).
      destruct (dec_agree (X i) c E hc hE hag) as [hl ha]. split; [lia | exact ha].
  Qed.

End RsDecode.
