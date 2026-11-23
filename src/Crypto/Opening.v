(* The opening protocol (paper, Section 4.2): its soundness, lemma by lemma.

   Model. A matrix is a family of committed words X i : nat -> F, one per
   row i. If the matrix decodes, row i has a message P i : list F (data
   symbols followed by pads) and X i agrees with the encoding of P i
   outside an error set E. A claim pairs rows with public vectors L; the
   inner product dot (P i) L uses the first length L coordinates of P i.

   After the batching challenge kappa, the claims have become, per slot s,
   a public vector sL s, a mask smr s (rows and weights) and a list scb s of pairs
   (row, weight). The prover sends mu, then, after c, one vector svec s per
   slot, which should be the message

       dm P (smr s) (scb s) c  =  sum_(i,w) in smr w * P i + c * sum_(i,w) in scb w * P i.

   The verifier checks  sum_s dot (svec s) (sL s) = mu + c * V  and, at each
   queried column j,

       enc (svec s) j  =  the same combination of the committed words X i at column j   (xw).

   Results, in the order of the error budget of Theorem 5.2:
   - batch_count      a false claim disappears in the batch for at most
                      |F|^(k-1) of the |F|^k challenges kappa;
   - c_count          the value check holds for a wrong V for at most one c;
   - slot_dichotomy   for a decoding matrix, either svec s is the decoded
                      combination, or at most n - d + |E| columns pass the
                      column check (Lemma 4.3 applied to the slot);
   - value_core       if every svec s is the decoded combination, the value
                      check reads mu + c V = mu' + c V' with mu', V'
                      computed from the decoded rows;
   - opening_values   the same for arbitrary slot vectors and masks, given
                      the batched true value;
   - batch_sum        for slots with a fixed vector, the batched true value
                      is <kappa, true values of the claims>;
   - all_pass_count (Counting.v)  t independent column queries all pass
                      for (number of passing columns)^t tuples.

   The proximity step (challenge gamma) is prox_affine with far_few_pass in
   Proximity.v. The slot lemma depends on the code; value_core does not,
   so a protocol with several matrices applies slot_dichotomy once per
   matrix and value_core once.

   Not here: the queries of the implementation are distinct columns; the
   count for sampling without replacement is not yet proven
   (all_pass_count is for independent queries). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon.
Import ListNotations.

Section Opening.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation vsub := (@vsub F sub).
  Local Notation allzero := (@allzero F zero Fdec).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation peval := (@eval F zero add mul).
  Local Notation pz := (@pzero F zero).
  Local Notation pw := (@pw F one mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).

  (* ------------------------------------------------------------------ *)
  (* Counting lemmas for the challenges kappa and c *)

  Lemma linear_form_zero_count : forall (lf : list F), NoDup lf ->
    forall (g : list F), allzero g = false ->
    (length (filter (fun kp => feqb (dot g kp) zero) (all_lists lf (length g))) <= length lf ^ (length g - 1))%nat.
  Proof.
    intros lf hnd; induction g as [| h t ih]; intro hnz; [cbn in hnz; discriminate |].
    cbn [length]. replace (S (length t) - 1)%nat with (length t) by lia.
    rewrite filter_all_lists_S. cbn beta.
    destruct (Fdec h zero) as [hh | hh].
    + (* h = 0: the first coordinate is free *)
      subst h. cbn in hnz. destruct (Fdec zero zero) as [_ | nn]; [| contradiction]. cbn in hnz.
      specialize (ih hnz).
      rewrite (nsum_map_ext _ (fun xs => if feqb (dot t xs) zero then length lf else 0%nat)).
      - rewrite nsum_map_ite.
        assert (hpos : (1 <= length t)%nat) by (destruct t; [cbn in hnz; discriminate | cbn; lia]).
        replace (length t) with (S (length t - 1)) at 2 by lia. cbn [Nat.pow].
        apply Nat.mul_le_mono_l. exact ih.
      - intros xs _.
        rewrite (filter_ext (fun x0 => feqb (dot (zero :: t) (x0 :: xs)) zero) (fun _ => feqb (dot t xs) zero)).
        * apply filter_const_length.
        * intro x0. cbn. f_equal. field.
    + (* h <> 0: at most one value of the first coordinate *)
      assert (hle : (nsum (map (fun xs => length (filter (fun x0 => feqb (dot (h :: t) (x0 :: xs)) zero) lf))
                       (all_lists lf (length t))) <= 1 * length (all_lists lf (length t)))%nat).
      { apply nsum_map_le; intros xs _.
        set (p := [dot t xs; h]).
        assert (hp : ~ pz p).
        { intro hz. inversion hz as [| ? ? _ h']. inversion h' as [| ? ? e0 _]. contradiction. }
        assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf 2 p (le_n _) hp
                  (filter (fun x0 => feqb (dot (h :: t) (x0 :: xs)) zero) lf) (NoDup_filter _ hnd)).
        assert (hr : forall r, In r (filter (fun x0 => feqb (dot (h :: t) (x0 :: xs)) zero) lf) -> peval p r = zero).
        { intros r hr. apply filter_In in hr; destruct hr as [_ hr]. apply feqb_true in hr.
          unfold p; cbn. cbn in hr. transitivity (h * r + dot t xs); [field | exact hr]. }
        specialize (hlt hr). change (length p) with 2%nat in hlt. lia. }
      rewrite all_lists_length in hle. lia.
  Qed.

  Theorem batch_count : forall (lf : list F), NoDup lf ->
    forall (vals tvs : list F), length vals = length tvs -> vals <> tvs ->
    (length (filter (fun kp => feqb (dot vals kp) (dot tvs kp)) (all_lists lf (length vals)))
     <= length lf ^ (length vals - 1))%nat.
  Proof.
    intros lf hnd vals tvs hl hne.
    pose proof (linear_form_zero_count lf hnd (vsub vals tvs) (vsub_nonzero vals tvs hl hne)) as h.
    rewrite vsub_length in h by exact hl.
    erewrite filter_ext; [exact h |].
    intro kp. cbn beta. rewrite dot_vsub by exact hl.
    unfold Mle.feqb.
    destruct (Fdec (dot vals kp) (dot tvs kp)) as [e | e];
      destruct (Fdec (dot vals kp - dot tvs kp) zero) as [e2 | e2]; try reflexivity; exfalso.
    + apply e2. rewrite e. field.
    + apply e. assert (hx : dot vals kp = (dot vals kp - dot tvs kp) + dot tvs kp) by field.
      rewrite hx, e2. field.
  Qed.

  Theorem c_count : forall (lf : list F), NoDup lf ->
    forall mu mu' V V' : F, V <> V' ->
    Nat.le (length (filter (fun c => feqb (mu + c * V) (mu' + c * V')) lf)) 1.
  Proof.
    intros lf hnd mu mu' V V' hne.
    set (p := [mu - mu'; V - V']).
    assert (hp : ~ pz p).
    { intro hz. inversion hz as [| ? ? _ h']. inversion h' as [| ? ? e0 _].
      apply hne. assert (hx : V = (V - V') + V') by field. rewrite hx, e0. field. }
    assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf 2 p (le_n _) hp
              (filter (fun c => feqb (mu + c * V) (mu' + c * V')) lf) (NoDup_filter _ hnd)).
    assert (hr : forall r, In r (filter (fun c => feqb (mu + c * V) (mu' + c * V')) lf) -> peval p r = zero).
    { intros r hr. apply filter_In in hr; destruct hr as [_ hr]. apply feqb_true in hr.
      unfold p; cbn. transitivity ((mu + r * V) - (mu' + r * V')); [field | rewrite hr; field]. }
    specialize (hlt hr). change (length p) with 2%nat in hlt. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Messages: combinations and inner products *)

  Lemma dot_nth_ext : forall (L a b : list F),
    (forall t, nth t a zero = nth t b zero) -> dot a L = dot b L.
  Proof.
    induction L as [| l L ih]; intros a b h.
    + rewrite !dot_nil_r. reflexivity.
    + destruct a as [| x a], b as [| y b].
      - reflexivity.
      - assert (e0 : y = zero) by (symmetry; exact (h 0%nat)).
        assert (e1 : dot [] L = dot b L).
        { apply ih. intro t. specialize (h (S t)). cbn in h. rewrite <-h. destruct t; reflexivity. }
        cbn. cbn in e1. rewrite <-e1, e0. field.
      - assert (e0 : x = zero) by (exact (h 0%nat)).
        assert (e1 : dot a L = dot [] L).
        { apply ih. intro t. specialize (h (S t)). cbn in h. rewrite h. destruct t; reflexivity. }
        cbn. cbn in e1. rewrite e1, e0. field.
      - assert (e0 : x = y) by (exact (h 0%nat)).
        cbn. rewrite e0, (ih a b); [reflexivity |]. intro t. exact (h (S t)).
  Qed.

  Fixpoint msum (P : nat -> list F) (cb : list (nat * F)) : list F :=
    match cb with
    | [] => []
    | iw :: cb' => padd (pscale (snd iw) (P (fst iw))) (msum P cb')
    end.

  Fixpoint vsum (P : nat -> list F) (cb : list (nat * F)) (L : list F) : F :=
    match cb with
    | [] => zero
    | iw :: cb' => snd iw * dot (P (fst iw)) L + vsum P cb' L
    end.

  Lemma dot_msum : forall P cb L, dot (msum P cb) L = vsum P cb L.
  Proof.
    intros P; induction cb as [| iw cb ih]; intro L; cbn [msum vsum].
    + reflexivity.
    + rewrite dot_padd_l, dot_pscale_l, ih. reflexivity.
  Qed.

  (* The decoded combination of a slot: the mask message, itself a
     combination mcb of rows (in the implementation an F-row stored as two
     rows with weights 1 and t), plus c times the batched rows. *)
  Definition dm (P : nat -> list F) (mcb cb : list (nat * F)) (c : F) : list F :=
    padd (msum P mcb) (pscale c (msum P cb)).

  Lemma dot_dm : forall P mcb cb c L, dot (dm P mcb cb c) L = vsum P mcb L + c * vsum P cb L.
  Proof. intros. unfold dm. rewrite dot_padd_l, dot_pscale_l, !dot_msum. reflexivity. Qed.

  Record slot : Type := mk_slot {
    sL : list F;               (* the public vector of the slot *)
    smr : list (nat * F);      (* its mask: rows and weights *)
    scb : list (nat * F);      (* rows and weights, after batching *)
    svec : list F              (* the vector sent by the prover *)
  }.

  (* The value check, when every sent vector is the decoded combination. *)
  Theorem value_core : forall (P : nat -> list F) (c : F) (sl : list slot),
    (forall s, In s sl -> forall t, nth t (svec s) zero = nth t (dm P (smr s) (scb s) c) zero) ->
    fsum (map (fun s => dot (svec s) (sL s)) sl) =
    fsum (map (fun s => vsum P (smr s) (sL s)) sl) + c * fsum (map (fun s => vsum P (scb s) (sL s)) sl).
  Proof.
    intros P c; induction sl as [| s sl ih]; intro h; cbn.
    + field.
    + rewrite (ih (fun s' hs' => h s' (or_intror hs'))).
      rewrite (dot_nth_ext (sL s) (svec s) (dm P (smr s) (scb s) c) (h s (or_introl eq_refl))).
      rewrite dot_dm. field.
  Qed.

  (* The opening equation for arbitrary slots. Lv, mcb, cbv are the vector,
     the mask and the batched rows of each slot, for the kappa at hand; T is
     the batched true value sum_v vsum P (cbv v) (Lv v). If every slot
     vector is the decoded combination and the value check passes, then
         mu + c * V = mu' + c * T,   mu' = sum_v vsum P (mcb v) (Lv v). *)
  Theorem opening_values : forall (P : nat -> list F) (Lv : nat -> list F)
    (mcb cbv : nat -> list (nat * F)) (ub : nat -> list F) (vs : list nat) (c mu V T : F),
    (forall v, In v vs -> forall t, nth t (ub v) zero = nth t (dm P (mcb v) (cbv v) c) zero) ->
    fsum (map (fun v => vsum P (cbv v) (Lv v)) vs) = T ->
    fsum (map (fun v => dot (ub v) (Lv v)) vs) = mu + c * V ->
    mu + c * V = fsum (map (fun v => vsum P (mcb v) (Lv v)) vs) + c * T.
  Proof.
    intros P Lv mcb cbv ub vs c mu V T hdec hT hcheck.
    rewrite <-hT, <-hcheck.
    pose proof (value_core P c (map (fun v => mk_slot (Lv v) (mcb v) (cbv v) (ub v)) vs)) as h.
    rewrite !map_map in h. cbn [svec sL smr scb] in h. apply h.
    intros s hs. apply in_map_iff in hs. destruct hs as (v & <- & hv). cbn. apply hdec; exact hv.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Claims and their batching *)

  (* A term (v, i, a) contributes a * dot (P i) (Ls v): row i, paired with
     the vector of slot v, with coefficient a. A claim is a list of terms
     (and a claimed value). *)
  Definition term : Type := (nat * nat * F)%type.

  Fixpoint tval (P : nat -> list F) (Ls : nat -> list F) (cl : list term) : F :=
    match cl with
    | [] => zero
    | t :: cl' => snd t * dot (P (snd (fst t))) (Ls (fst (fst t))) + tval P Ls cl'
    end.

  (* the terms of one claim that fall in slot v, scaled by k0 *)
  Fixpoint sel (k0 : F) (cl : list term) (v : nat) : list (nat * F) :=
    match cl with
    | [] => []
    | t :: cl' =>
        if Nat.eqb (fst (fst t)) v then (snd (fst t), k0 * snd t) :: sel k0 cl' v else sel k0 cl' v
    end.

  (* the batched weights of slot v *)
  Fixpoint batch (kp : list F) (cls : list (list term)) (v : nat) : list (nat * F) :=
    match kp, cls with
    | k0 :: kp', cl :: cls' => sel k0 cl v ++ batch kp' cls' v
    | _, _ => []
    end.

  Lemma vsum_app : forall P cb cb' L, vsum P (cb ++ cb') L = vsum P cb L + vsum P cb' L.
  Proof. intros P; induction cb as [| iw cb ih]; intros cb' L; cbn; [field | rewrite ih; field]. Qed.

  Lemma sel_sum : forall P Ls (vs : list nat) k0 cl, NoDup vs ->
    (forall t, In t cl -> In (fst (fst t)) vs) ->
    fsum (map (fun v => vsum P (sel k0 cl v) (Ls v)) vs) = k0 * tval P Ls cl.
  Proof.
    intros P Ls vs k0 cl hnd; induction cl as [| t cl ih]; intro hin.
    + cbn [sel tval]. rewrite fsum_map_zero_ext by (intros; reflexivity). field.
    + rewrite (fsum_map_ext _ (fun v => (if Nat.eq_dec (fst (fst t)) v then one else zero)
                                   * (k0 * snd t * dot (P (snd (fst t))) (Ls v))
                                 + vsum P (sel k0 cl v) (Ls v))).
      - rewrite fsum_map_add.
        rewrite (fsum_indicator Nat.eq_dec (fun v => k0 * snd t * dot (P (snd (fst t))) (Ls v)) (fst (fst t)) vs hnd
                   (hin t (or_introl eq_refl))).
        rewrite (ih (fun t' ht' => hin t' (or_intror ht'))). cbn [tval]. field.
      - intros v _. cbn [sel].
        destruct (Nat.eq_dec (fst (fst t)) v) as [e | e].
        * rewrite (proj2 (Nat.eqb_eq _ _) e). cbn [vsum fst snd]. field.
        * rewrite (proj2 (Nat.eqb_neq _ _) e). field.
  Qed.

  (* The batched claim is the kappa-combination of the claims. *)
  Theorem batch_sum : forall P Ls (vs : list nat), NoDup vs ->
    forall (cls : list (list term)) (kp : list F), length kp = length cls ->
    (forall cl, In cl cls -> forall t, In t cl -> In (fst (fst t)) vs) ->
    fsum (map (fun v => vsum P (batch kp cls v) (Ls v)) vs) = dot kp (map (tval P Ls) cls).
  Proof.
    intros P Ls vs hnd; induction cls as [| cl cls ih]; intros kp hl hin; destruct kp as [| k0 kp]; cbn in hl; try lia.
    + cbn [batch map]. rewrite fsum_map_zero_ext by (intros; reflexivity). reflexivity.
    + cbn [batch map].
      rewrite (fsum_map_ext _ (fun v => vsum P (sel k0 cl v) (Ls v) + vsum P (batch kp cls v) (Ls v)))
        by (intros; apply vsum_app).
      rewrite fsum_map_add, (sel_sum P Ls vs k0 cl hnd (hin cl (or_introl eq_refl))).
      rewrite (ih kp ltac:(lia) (fun cl' h' => hin cl' (or_intror h'))). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The column check for one slot of a Reed-Solomon matrix *)

  Variable omega : F.
  Variables n k : nat.
  Hypothesis Hk : (k <= n)%nat.
  Hypothesis Hnodes : forall i j, (i < n)%nat -> (j < n)%nat -> pw omega i = pw omega j -> i = j.

  Local Notation rs_enc := (@rs_enc F zero one add mul omega).
  Local Notation rs_code := (@rs_code F zero one add mul omega n k).

  Fixpoint wsum (X : nat -> nat -> F) (cb : list (nat * F)) (j : nat) : F :=
    match cb with
    | [] => zero
    | iw :: cb' => snd iw * X (fst iw) j + wsum X cb' j
    end.

  (* the committed combination, column by column *)
  Definition xw (X : nat -> nat -> F) (mcb cb : list (nat * F)) (c : F) (j : nat) : F :=
    wsum X mcb j + c * wsum X cb j.

  Lemma rs_enc_padd : forall p q j, rs_enc (padd p q) j = rs_enc p j + rs_enc q j.
  Proof. intros. unfold ReedSolomon.rs_enc. apply eval_padd. Qed.

  Lemma rs_enc_pscale : forall t p j, rs_enc (pscale t p) j = t * rs_enc p j.
  Proof. intros. unfold ReedSolomon.rs_enc. apply eval_pscale. Qed.

  Lemma rs_enc_msum : forall P cb j, rs_enc (msum P cb) j = wsum (fun i => rs_enc (P i)) cb j.
  Proof.
    intros P; induction cb as [| iw cb ih]; intro j; cbn [msum wsum].
    + reflexivity.
    + rewrite rs_enc_padd, rs_enc_pscale, ih. reflexivity.
  Qed.

  Lemma length_msum : forall P cb, (forall i, In i (map fst cb) -> (length (P i) <= k)%nat) ->
    (length (msum P cb) <= k)%nat.
  Proof.
    intros P cb; induction cb as [| iw cb ih]; intro h; cbn [msum]; [cbn; lia |].
    rewrite length_padd, length_pscale.
    pose proof (h (fst iw) (or_introl eq_refl)).
    pose proof (ih (fun i hi => h i (or_intror hi))). lia.
  Qed.

  Lemma length_dm : forall P mcb cb c,
    (forall i, In i (map fst mcb ++ map fst cb) -> (length (P i) <= k)%nat) ->
    (length (dm P mcb cb c) <= k)%nat.
  Proof.
    intros P mcb cb c h. unfold dm. rewrite length_padd, length_pscale.
    pose proof (length_msum P mcb (fun i hi => h i (in_or_app _ _ _ (or_introl hi)))).
    pose proof (length_msum P cb (fun i hi => h i (in_or_app _ _ _ (or_intror hi)))). lia.
  Qed.

  Lemma rs_code_enc : forall p, (length p <= k)%nat -> rs_code (rs_enc p).
  Proof. intros p hp. exists p; split; [exact hp | reflexivity]. Qed.

  (* Encoding is injective on messages, up to trailing zeros. *)
  Lemma rs_enc_inj_nth : forall p q : list F, (length p <= k)%nat -> (length q <= k)%nat ->
    (forall j, (j < n)%nat -> rs_enc p j = rs_enc q j) -> forall t, nth t p zero = nth t q zero.
  Proof.
    intros p q hp hq he t.
    set (df := padd p (pscale (opp one) q)).
    assert (hlen : (length df <= k)%nat) by (unfold df; rewrite length_padd, length_pscale; lia).
    assert (hz : pz df).
    { destruct (@pzero_dec F zero Fdec df) as [h | h]; [exact h | exfalso].
      assert (hnd : NoDup (map (pw omega) (seq 0 n))).
      { apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
        intros i j hi hj e. apply in_seq in hi. apply in_seq in hj. apply Hnodes; [lia | lia | exact e]. }
      assert (hlt := @roots_bound F zero one add mul sub div opp inv Fdec Hf (length df) df (le_n _) h
                (map (pw omega) (seq 0 n)) hnd).
      assert (hr : forall r, In r (map (pw omega) (seq 0 n)) -> peval df r = zero).
      { intros r hr. apply in_map_iff in hr; destruct hr as (j & <- & hj). apply in_seq in hj.
        unfold df. rewrite eval_padd, eval_pscale.
        specialize (he j ltac:(lia)). unfold ReedSolomon.rs_enc in he. rewrite he. field. }
      specialize (hlt hr). rewrite length_map, length_seq in hlt. lia. }
    pose proof (@pzero_nth F zero Fdec df t hz) as h. unfold df in h.
    rewrite nth_padd, nth_pscale in h.
    assert (e : nth t p zero = (nth t p zero + opp one * nth t q zero) + nth t q zero) by field.
    rewrite e, h. field.
  Qed.

  Lemma wsum_agree : forall (X : nat -> nat -> F) (P : nat -> list F) (E : list nat) cb j,
    (forall i, In i (map fst cb) -> agree_out n E (X i) (rs_enc (P i))) ->
    (j < n)%nat -> ~ In j E ->
    wsum X cb j = wsum (fun i => rs_enc (P i)) cb j.
  Proof.
    intros X P E cb j hag hj hn. induction cb as [| iw cb ih]; cbn [wsum]; [reflexivity |].
    rewrite (ih (fun i hi => hag i (or_intror hi))), (hag (fst iw) (or_introl eq_refl) j hj hn). reflexivity.
  Qed.

  Lemma comb_agree : forall (X : nat -> nat -> F) (P : nat -> list F) (E : list nat) mcb cb c,
    (forall i, In i (map fst mcb ++ map fst cb) -> agree_out n E (X i) (rs_enc (P i))) ->
    agree_out n E (xw X mcb cb c) (rs_enc (dm P mcb cb c)).
  Proof.
    intros X P E mcb cb c hag j hj hn. unfold xw, dm.
    rewrite rs_enc_padd, rs_enc_pscale, !rs_enc_msum.
    rewrite (wsum_agree X P E mcb j (fun i hi => hag i (in_or_app _ _ _ (or_introl hi))) hj hn).
    rewrite (wsum_agree X P E cb j (fun i hi => hag i (in_or_app _ _ _ (or_intror hi))) hj hn).
    reflexivity.
  Qed.

  (* Lemma 4.3 for a slot: the sent vector is the decoded combination, or
     few columns pass. *)
  Theorem slot_dichotomy : forall (X : nat -> nat -> F) (P : nat -> list F) (E : list nat) (s : slot) (c : F),
    (forall i, In i (map fst (smr s) ++ map fst (scb s)) -> (length (P i) <= k)%nat) ->
    (forall i, In i (map fst (smr s) ++ map fst (scb s)) -> agree_out n E (X i) (rs_enc (P i))) ->
    (length (svec s) <= k)%nat ->
    (forall t, nth t (svec s) zero = nth t (dm P (smr s) (scb s) c) zero) \/
    (length (filter (fun j => feqb (rs_enc (svec s) j) (xw X (smr s) (scb s) c j)) (seq 0 n)) + (n - k + 1)
     <= n + length E)%nat.
  Proof.
    intros X P E s c hP hag hub.
    pose proof (length_dm P (smr s) (scb s) c hP) as hdml.
    destruct (Exists_dec (fun j => rs_enc (svec s) j <> rs_enc (dm P (smr s) (scb s) c) j) (seq 0 n)) as [hex | hno].
    + intro j. destruct (Fdec (rs_enc (svec s) j) (rs_enc (dm P (smr s) (scb s) c) j)); [right | left]; tauto.
    + right. apply Exists_exists in hex. destruct hex as (j & hj & hne). apply in_seq in hj.
      apply (@consistency F Fdec n (n - k + 1) rs_code
               (@rs_dist F zero one add mul sub div opp inv Fdec Hf omega n k Hk Hnodes)
               (xw X (smr s) (scb s) c) (rs_enc (svec s)) (rs_enc (dm P (smr s) (scb s) c)) E).
      - apply rs_code_enc; exact hub.
      - apply rs_code_enc; exact hdml.
      - apply comb_agree; exact hag.
      - exists j; split; [lia | exact hne].
    + left. apply rs_enc_inj_nth; [exact hub | exact hdml |].
      intros j hj.
      destruct (Fdec (rs_enc (svec s) j) (rs_enc (dm P (smr s) (scb s) c) j)) as [e | e]; [exact e | exfalso].
      apply hno. apply Exists_exists. exists j; split; [apply in_seq; lia | exact e].
  Qed.

End Opening.
