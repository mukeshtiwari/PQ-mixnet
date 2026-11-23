(* Completeness, back end, step 4: the opening.

   The decoded rows of an honest prover are its committed rows (PF: the
   rows of the three batches, mapped to GF(q^2)). On them

     layout_targets   the nine claims of the opening evaluate (gtval) to the
                      nine values that xderive derives (targets of
                      ExecBackD.v), by the layout identity (MixLayout.v) and
                      the read-back lemmas of ExecRows.v;
     check0_complete  the batched value check of xaccO passes (batch_mixed);
     macc_complete    the column checks of both matrices pass: the
                      codeword of a combination of rows is the same
                      combination of the committed columns (linearity of
                      Reed-Solomon encoding). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field String.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex Sumcheck SumcheckMask LayoutLemmas RowLayout MixBridge Opening SlotKinds MaskedExt MixSummands MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecMerkle ExecProveBase ExecSerial ExecFold ExecFront ExecShape ExecDec ExecProve ExecRows ExecNtt ExecBack ExecBackD.
Import ListNotations.

Add Field fieldF2o : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation fsum := (@LogDer.fsum Fq2 fzero fadd).
Local Notation dot := (@LogDer.dot Fq2 fzero fadd fmul).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation gmask2 := (@gmask Fq2 fzero fadd fmul).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation nF2 := (@nF Fq2 fzero fone fadd).

(* ---------------------------------------------------------------------- *)
(* generic *)

Lemma nth_msgs : forall C (rows pads : list (list Z)) i, List.length rows = List.length pads -> (i < List.length rows)%nat ->
  nth i (map (fun p => padrow C (fst p) (snd p)) (combine rows pads)) [] = padrow C (nth i rows []) (nth i pads []).
Proof. intros C rows pads i hl hi. exact (nth_combine_map _ rows pads i [] [] [] hl hi). Qed.

Lemma nth_concat_uniform : forall (L : list (list Z)) n i y, (forall l, In l L -> List.length l = n) ->
  (y < n)%nat -> (i < List.length L)%nat -> nth (y + n * i) (List.concat L) 0%Z = nth y (nth i L []) 0%Z.
Proof.
  induction L as [| l L ih]; intros n i y h hy hi; [cbn in hi; lia |].
  cbn [List.concat]. destruct i as [| i].
  + rewrite Nat.mul_0_r, Nat.add_0_r, app_nth1 by (rewrite (h l (or_introl eq_refl)); exact hy). reflexivity.
  + rewrite app_nth2 by (rewrite (h l (or_introl eq_refl)); nia). rewrite (h l (or_introl eq_refl)).
    replace (y + n * S i - n)%nat with (y + n * i)%nat by nia. cbn [nth]. apply ih; [intros l' hl'; apply h; right; exact hl' | exact hy | cbn in hi; lia].
Qed.

Lemma nth_map_indep : forall {A B : Type} (f : A -> B) (l : list A) i d d', (i < List.length l)%nat ->
  nth i (map f l) d' = f (nth i l d).
Proof. intros A B f l i d d' h. rewrite (nth_indep _ d' (f d)) by (rewrite length_map; exact h). apply map_nth. Qed.

Lemma cons9 : forall {A : Type} (x1 x2 x3 x4 x5 x6 x7 x8 x9 y1 y2 y3 y4 y5 y6 y7 y8 y9 : A),
  x1 = y1 -> x2 = y2 -> x3 = y3 -> x4 = y4 -> x5 = y5 -> x6 = y6 -> x7 = y7 -> x8 = y8 -> x9 = y9 ->
  [x1; x2; x3; x4; x5; x6; x7; x8; x9] = [y1; y2; y3; y4; y5; y6; y7; y8; y9].
Proof. intros. subst. reflexivity. Qed.

(* integers mod q as base-field elements *)
Local Notation peval := (@eval Fq2 fzero fadd fmul).
Local Notation pw2 := (@pw Fq2 fone fmul).

Lemma idx_of_spec : forall js j k, In j js ->
  nth (idx_of js j k - k) js 0%nat = j /\ (k <= idx_of js j k < k + List.length js)%nat.
Proof.
  induction js as [| x js ih]; intros j k h; [contradiction |].
  cbn [idx_of]. destruct (Nat.eqb_spec x j) as [e | e].
  + rewrite Nat.sub_diag. cbn. split; [exact e | lia].
  + destruct h as [h | h]; [contradiction |]. destruct (ih j (S k) h) as [h1 h2].
    replace (idx_of js j (S k) - k)%nat with (S (idx_of js j (S k) - S k)) by lia. cbn [nth List.length].
    split; [exact h1 | lia].
Qed.

Lemma nth_idx_map : forall {B : Type} (f : nat -> B) (js : list nat) j d, In j js ->
  nth (idx_of js j 0) (map f js) d = f j.
Proof.
  intros B f js j d h. destruct (idx_of_spec js j 0 h) as [h1 h2]. rewrite Nat.sub_0_r in h1.
  rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map; lia). rewrite map_nth, h1. reflexivity.
Qed.

Section BackO.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable k : coins.
  Variable sigma : list nat.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation SO := (SOE n1 ell lo1).

  Local Notation uPx := (uP ell pplain a b cin wr we1 we2).
  Local Notation uhPx := (uhP cout sig).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).
  Local Notation cok := (coins_ok n1 ell lo1 lo2 nB nqB nS nqS k).
  Local Notation pok := (params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS).

  Local Notation bBx := (btB lo1 nB omB wr we1 we2 k).
  Local Notation b1x := (btS1 lo2 nS omS sig k).
  Definition b2x (T : ptrace) : batch :=
    btS2 ell lo2 nS omS pplain a b cin cout sig wr we1 we2 k (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T).
  Definition AMx (T : ptrace) : list (list Z) := allmsgs bBx b1x (b2x T).

  (* the honest decoded rows *)
  Definition PF (T : ptrace) (i : nat) : list F := map to_F (map bx (nth i (AMx T) [])).

  Lemma AM_eq : forall T, AMx T = msgsB lo1 wr we1 we2 k ++ msgsS1 lo2 sig k
                                  ++ msgsS2 ell lo2 pplain a b cin cout sig wr we1 we2 k (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T).
  Proof. reflexivity. Qed.

  Lemma rw_eq : rw = (2 ^ hiE m lo1)%nat.
  Proof. reflexivity. Qed.
  Lemma rs_eq : rs = (2 ^ hiE ell lo2)%nat.
  Proof. reflexivity. Qed.

  Lemma Wk_rows : wshape -> forall kk, (kk < 3)%nat ->
    List.length (nth kk (Wk wr we1 we2) []) = (2 ^ m)%nat /\ List.length (split_rows C1 (nth kk (Wk wr we1 we2) [])) = rw.
  Proof.
    intros hw kk hk.
    assert (hl : List.length (nth kk (Wk wr we1 we2) []) = (2 ^ m)%nat).
    { destruct kk as [| [| [| kk]]]; try lia; apply (Wk_length n1 ell cout sig wr we1 we2 hw); cbn; tauto. }
    split; [exact hl |]. rewrite (proj1 (split_rows_shape lo1 m _ hl)). reflexivity.
  Qed.

  (* the rows of the big matrix *)
  Lemma PF_W : wshape -> cok -> forall T kk t, (kk < 3)%nat -> (t < rw)%nat ->
    PF T (kk * rw + t) = map to_F (map bx (padrow C1 (nth t (split_rows C1 (nth kk (Wk wr we1 we2) [])) [])
                                                 (nth (kk * rw + t) (kpB k) []))).
  Proof.
    intros hw hk T kk t hkk ht. unfold PF. rewrite AM_eq.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hlB _].
    rewrite app_nth1 by nia.
    pose proof (Wk_rows hw 0%nat ltac:(lia)) as [_ r0]. pose proof (Wk_rows hw 1%nat ltac:(lia)) as [_ r1].
    pose proof (Wk_rows hw 2%nat ltac:(lia)) as [_ r2].
    destruct hk as (hfB & hpB & _). destruct hfB as [hfB _]. destruct hpB as [hpB _].
    unfold msgsB. rewrite nth_msgs.
    2: { unfold Wk, Wpol in *. cbn [map flat_map] in *. rewrite ?app_nil_r, !length_app, hfB, hpB. cbn [nth] in r0, r1, r2. lia. }
    2: { unfold Wk, Wpol in *. cbn [map flat_map] in *. rewrite ?app_nil_r, !length_app, hfB. cbn [nth] in r0, r1, r2. nia. }
    f_equal. f_equal. f_equal.
    unfold Wk, Wpol in *. cbn [map flat_map] in *. rewrite ?app_nil_r. cbn [nth] in r0, r1, r2.
    rewrite app_nth1 by (rewrite !length_app; nia).
    destruct kk as [| [| [| kk]]]; try lia.
    + rewrite app_nth1 by (rewrite r0; lia). f_equal; lia.
    + rewrite app_nth2 by (rewrite r0; lia). rewrite r0, app_nth1 by (rewrite r1; lia). f_equal; lia.
    + rewrite app_nth2 by (rewrite r0; lia). rewrite r0, app_nth2 by (rewrite r1; lia). rewrite r1. f_equal; lia.
  Qed.

  (* the rows of the small matrix *)
  Lemma sigZ_rows : wshape -> List.length (sigZ sig) = tau /\ List.length (split_rows C2 (sigZ sig)) = rs.
  Proof.
    intros (hs & _ & _). assert (hl : List.length (sigZ sig) = tau) by (unfold sigZ; rewrite length_map; exact hs).
    split; [exact hl |]. rewrite (proj1 (split_rows_shape lo2 ell _ hl)). reflexivity.
  Qed.

  Lemma PF_S1 : wshape -> cok -> forall T t, (t < rs)%nat ->
    PF T (SO + t) = map to_F (map bx (padrow C2 (nth t (split_rows C2 (sigZ sig)) []) (nth t (kpS1 k) []))).
  Proof.
    intros hw hk T t ht. unfold PF. rewrite AM_eq.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hlB _].
    destruct (msgsS1_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hl1 _].
    rewrite app_nth2 by (rewrite hlB; unfold SOE; lia). rewrite hlB.
    replace (SO + t - (3 * rw + 6))%nat with t by (unfold SOE; lia).
    rewrite app_nth1 by (rewrite hl1; lia).
    destruct (sigZ_rows hw) as [_ hr].
    destruct hk as (_ & _ & _ & hfS & hpS1 & _). destruct hfS as [hfS _]. destruct hpS1 as [hpS1 _].
    unfold msgsS1. rewrite nth_msgs by (rewrite length_app, hr, hfS, ?hpS1; lia).
    f_equal. f_equal. f_equal. rewrite app_nth1 by (rewrite hr; exact ht). reflexivity.
  Qed.

  Definition s2rows (T : ptrace) : list (list Z) :=
    let u := uPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T) in
    let uh := uhPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T) in
    [map fst u; map snd u; map fst uh; map snd uh].

  Lemma s2_rows : wshape -> forall T q, (q < 4)%nat ->
    List.length (nth q (s2rows T) []) = tau /\ List.length (split_rows C2 (nth q (s2rows T) [])) = rs.
  Proof.
    intros hw T q hq.
    assert (hl : List.length (nth q (s2rows T) []) = tau).
    { unfold s2rows. cbv zeta. pose proof (hhP_length n1 ell cout sig wr we1 we2 (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T) hw).
      destruct q as [| [| [| [| q]]]]; try lia; cbn [nth]; unfold uP, uhP; rewrite !length_map;
        first [apply hP_length | assumption]. }
    split; [exact hl |]. rewrite (proj1 (split_rows_shape lo2 ell _ hl)). reflexivity.
  Qed.

  Lemma PF_S2 : pok -> wshape -> cok -> forall T q t, (q < 4)%nat -> (t < rs)%nat ->
    PF T (SO + (rs + 6) + q * rs + t)
    = map to_F (map bx (padrow C2 (nth t (split_rows C2 (nth q (s2rows T) [])) []) (nth (q * rs + t) (kpS2 k) []))).
  Proof.
    intros hp hw hk T q t hq ht. unfold PF. rewrite AM_eq.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hlB _].
    destruct (msgsS1_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hl1 _].
    destruct (msgsS2_shape n1 ell lo1 lo2 kB nB nqB kS nS nqS pplain a b cin cout sig wr we1 we2 k (tru T) (trv T)
                (ExecProve.alT T) (ExecProve.beT T) hp hw hk) as [hl2 _].
    rewrite app_nth2 by (rewrite hlB; unfold SOE; lia). rewrite hlB.
    rewrite app_nth2 by (rewrite hl1; unfold SOE; nia). rewrite hl1.
    replace (SO + (rs + 6) + q * rs + t - (3 * rw + 6) - (rs + 6))%nat with (q * rs + t)%nat by (unfold SOE; lia).
    pose proof (s2_rows hw T 0%nat ltac:(lia)) as [_ r0]. pose proof (s2_rows hw T 1%nat ltac:(lia)) as [_ r1].
    pose proof (s2_rows hw T 2%nat ltac:(lia)) as [_ r2]. pose proof (s2_rows hw T 3%nat ltac:(lia)) as [_ r3].
    unfold s2rows in r0, r1, r2, r3. cbv zeta in r0, r1, r2, r3. cbn [nth] in r0, r1, r2, r3.
    destruct hk as (_ & _ & _ & _ & _ & _ & _ & hpS2 & _). destruct hpS2 as [hpS2 _].
    unfold msgsS2. cbv zeta.
    rewrite nth_msgs by (rewrite !length_app, r0, r1, r2, r3, ?hpS2; cbn; nia).
    f_equal. f_equal. f_equal. unfold s2rows. cbv zeta.
    destruct q as [| [| [| [| q]]]]; try lia; cbn [nth].
    + rewrite app_nth1 by (rewrite r0; lia). f_equal; lia.
    + rewrite app_nth2 by (rewrite r0; lia). rewrite r0, app_nth1 by (rewrite r1; lia). f_equal; lia.
    + rewrite app_nth2 by (rewrite r0; lia). rewrite r0, app_nth2 by (rewrite r1; lia). rewrite r1.
      rewrite app_nth1 by (rewrite r2; lia). f_equal; lia.
    + rewrite app_nth2 by (rewrite r0; lia). rewrite r0, app_nth2 by (rewrite r1; lia). rewrite r1.
      rewrite app_nth2 by (rewrite r2; lia). rewrite r2, app_nth1 by (rewrite r3; lia). f_equal; lia.
  Qed.

  Lemma PF_M : pok -> wshape -> cok -> forall T,
    PF T (SO + (rs + 6) + 4 * rs) = map to_F (map bx (padrow C2 (mrow (kmask k)) (nth (4 * rs) (kpS2 k) []))).
  Proof.
    intros hp hw hk T. unfold PF. rewrite AM_eq.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hlB _].
    destruct (msgsS1_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hl1 _].
    destruct (msgsS2_shape n1 ell lo1 lo2 kB nB nqB kS nS nqS pplain a b cin cout sig wr we1 we2 k (tru T) (trv T)
                (ExecProve.alT T) (ExecProve.beT T) hp hw hk) as [hl2 _].
    rewrite app_nth2 by (rewrite hlB; unfold SOE; lia). rewrite hlB.
    rewrite app_nth2 by (rewrite hl1; unfold SOE; nia). rewrite hl1.
    replace (SO + (rs + 6) + 4 * rs - (3 * rw + 6) - (rs + 6))%nat with (4 * rs)%nat by (unfold SOE; lia).
    pose proof (s2_rows hw T 0%nat ltac:(lia)) as [_ r0]. pose proof (s2_rows hw T 1%nat ltac:(lia)) as [_ r1].
    pose proof (s2_rows hw T 2%nat ltac:(lia)) as [_ r2]. pose proof (s2_rows hw T 3%nat ltac:(lia)) as [_ r3].
    unfold s2rows in r0, r1, r2, r3. cbv zeta in r0, r1, r2, r3. cbn [nth] in r0, r1, r2, r3.
    destruct hk as (_ & _ & _ & _ & _ & _ & _ & hpS2 & _). destruct hpS2 as [hpS2 _].
    unfold msgsS2. cbv zeta.
    rewrite nth_msgs by (rewrite !length_app, r0, r1, r2, r3, ?hpS2; cbn; nia).
    f_equal. f_equal. f_equal.
    rewrite app_nth2 by (rewrite r0; lia). rewrite r0, app_nth2 by (rewrite r1; lia). rewrite r1.
    rewrite app_nth2 by (rewrite r2; lia). rewrite r2, app_nth2 by (rewrite r3; lia). rewrite r3.
    replace (4 * rs - rs - rs - rs - rs)%nat with 0%nat by lia. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the tables read off the honest rows *)

  Local Notation rdt := (@rdtab Fq2 fzero fone Fq2_dec).

  Lemma W_tab : wshape -> cok -> forall T kk x, (kk < 3)%nat -> (x < 2 ^ m)%nat ->
    rdt (PF T) (MixLayout.rW n1 ell lo1 kk) m lo1 (pt2 m x) = to_F (bx (nth x (nth kk (Wk wr we1 we2) []) 0%Z)).
  Proof.
    intros hw hk T kk x hkk hx.
    apply (rdtab_list (PF T) _ m lo1 _ (fun t => nth (kk * rw + t) (kpB k) [])); [exact (proj1 (Wk_rows hw kk hkk)) | | exact hx].
    intros t ht. unfold MixLayout.rW. exact (PF_W hw hk T kk t hkk ht).
  Qed.

  Lemma sg_tab : wshape -> cok -> forall T x, (x < tau)%nat ->
    rdt (PF T) (MixLayout.rSg SO) ell lo2 (pt2 ell x) = to_F (nth x (map bx (sigZ sig)) xzero).
  Proof.
    intros hw hk T x hx.
    rewrite (rdtab_list (PF T) _ ell lo2 (sigZ sig) (fun t => nth t (kpS1 k) [])); [| exact (proj1 (sigZ_rows hw)) | | exact hx].
    + change xzero with (bx 0%Z). rewrite map_nth. reflexivity.
    + intros t ht. unfold MixLayout.rSg. exact (PF_S1 hw hk T t ht).
  Qed.

  Lemma s2_tab : pok -> wshape -> cok -> forall T q x, (q < 4)%nat -> (x < tau)%nat ->
    rdt (PF T) (SO + (rs + 6) + q * rs) ell lo2 (pt2 ell x) = to_F (bx (nth x (nth q (s2rows T) []) 0%Z)).
  Proof.
    intros hp hw hk T q x hq hx.
    apply (rdtab_list (PF T) _ ell lo2 _ (fun t => nth (q * rs + t) (kpS2 k) [])); [exact (proj1 (s2_rows hw T q hq)) | | exact hx].
    intros t ht. rewrite <-(PF_S2 hp hw hk T q t hq ht). f_equal; lia.
  Qed.

  Lemma u_tab : pok -> wshape -> cok -> forall T x, (x < tau)%nat ->
    @uT Fq2 fzero fone fadd fmul Fq2_dec (PF T) ftg ell lo2 SO (pt2 ell x)
    = to_F (nth x (uPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) xzero).
  Proof.
    intros hp hw hk T x hx. unfold uT, MixLayout.rU0, MixLayout.rU1.
    pose proof (s2_tab hp hw hk T 0%nat x ltac:(lia) hx) as e0. pose proof (s2_tab hp hw hk T 1%nat x ltac:(lia) hx) as e1.
    rewrite Nat.mul_0_l, Nat.add_0_r in e0. rewrite Nat.mul_1_l in e1.
    change (MixLayout.rs ell lo2) with rs. rewrite e0, e1. unfold s2rows. cbv zeta. cbn [nth].
    change 0%Z with (fst xzero) at 1. rewrite map_nth. change 0%Z with (snd xzero). rewrite map_nth.
    symmetry. apply to_F_split.
  Qed.

  Lemma uh_tab : pok -> wshape -> cok -> forall T x, (x < tau)%nat ->
    @uhT Fq2 fzero fone fadd fmul Fq2_dec (PF T) ftg ell lo2 SO (pt2 ell x)
    = to_F (nth x (uhPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) xzero).
  Proof.
    intros hp hw hk T x hx. unfold uhT, MixLayout.rUh0, MixLayout.rUh1.
    pose proof (s2_tab hp hw hk T 2%nat x ltac:(lia) hx) as e0. pose proof (s2_tab hp hw hk T 3%nat x ltac:(lia) hx) as e1.
    change (MixLayout.rs ell lo2) with rs. rewrite e0, e1. unfold s2rows. cbv zeta. cbn [nth].
    change 0%Z with (fst xzero) at 1. rewrite map_nth. change 0%Z with (snd xzero). rewrite map_nth.
    symmetry. apply to_F_split.
  Qed.

  (* the mask-table row *)
  Lemma Pm_eq : pok -> wshape -> cok -> forall T,
    @Pm Fq2 (PF T) ell lo2 SO = map to_F (map bx (padrow C2 (mrow (kmask k)) (nth (4 * rs) (kpS2 k) []))).
  Proof. intros hp hw hk T. unfold Pm, MixLayout.rM. exact (PF_M hp hw hk T). Qed.

  (* the witness table folded at r, as a table of the coefficient index *)
  Lemma Wpol_lens : wshape -> forall kk, (kk < 3)%nat ->
    List.length (nth kk (Wpol wr we1 we2) []) = tau /\ forall l, In l (nth kk (Wpol wr we1 we2) []) -> List.length l = N.
  Proof.
    intros (_ & _ & hw) kk hkk. rewrite Forall_forall in hw.
    assert (hin : In (nth kk [wr; we1; we2] []) [wr; we1; we2]) by (apply nth_In; cbn; lia).
    destruct (hw _ hin) as [h1 h2]. rewrite Forall_forall in h2.
    unfold Wpol. change (nth kk (map (map (map zm)) [wr; we1; we2]) []) with (nth kk (map (map (map zm)) [wr; we1; we2]) (map (map zm) [])).
    rewrite map_nth. split.
    + rewrite length_map. exact h1.
    + intros l hl. apply in_map_iff in hl. destruct hl as (q & <- & hq). rewrite length_map. apply h2, hq.
  Qed.

  Lemma W_fold : wshape -> cok -> forall T kk (rA ry : list xf), (kk < 3)%nat -> List.length rA = ell -> List.length ry = n1 ->
    mle2 m (rdt (PF T) (MixLayout.rW n1 ell lo1 kk) m lo1) (map to_F ry ++ map to_F rA)
    = to_F (xmle (nth kk (WpP wr we1 we2 rA) []) ry).
  Proof.
    intros hw hk T kk rA ry hkk hrA hry.
    destruct (Wpol_lens hw kk hkk) as [hlp hlq].
    assert (hWP : nth kk (WpP wr we1 we2 rA) []
                  = fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (nth kk (Wpol wr we1 we2) [])))).
    { set (g := fun pols => fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) pols))).
      unfold WpP. fold g. rewrite (nth_indep _ [] (g [])) by (unfold Wpol; rewrite !length_map; cbn; lia).
      exact (map_nth g (Wpol wr we1 we2) [] kk). }
    rewrite (@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell _ (map to_F ry) (map to_F rA))
      by (rewrite length_map; exact hry).
    apply (mle_list n1 _ (nth kk (WpP wr we1 we2 rA) []) ry); [| exact hry |].
    { rewrite hWP. apply comb_rows_length.
      + intro e. pose proof (f_equal (@List.length (xf * list Z)) e) as e'.
        rewrite length_combine, xeq_table_length, hlp, hrA in e'. cbn in e'. pose proof (Nat.pow_nonzero 2 ell ltac:(lia)). lia.
      + apply Forall_forall. intros [p1 p2] hp. apply in_combine_r in hp. apply hlq, hp. }
    intros y hy. cbv beta.
    rewrite (mle_list ell _ (map (fun i => bx (nth y (nth i (nth kk (Wpol wr we1 we2) []) []) 0%Z)) (seq 0 tau)) rA);
      [| rewrite length_map, length_seq; reflexivity | exact hrA |].
    - rewrite xmle_sum by (rewrite length_map, length_seq, hrA; reflexivity).
      rewrite to_F_nth, hWP, nth_comb_rows.
      rewrite (fsum_combine _ _ _ xzero []) by (rewrite xeq_table_length, hlp, hrA; reflexivity).
      rewrite xeq_table_length, hrA. apply fsum_seq_ext. intros i hi. cbn [fst snd].
      rewrite (nth_map_seq_any _ tau i xzero hi), to_F_nth. reflexivity.
    - intros i hi. rewrite <-pt_split by exact hy.
      rewrite (W_tab hw hk T kk (y + 2 ^ n1 * i) hkk) by (rewrite Nat.pow_add_r; nia).
      rewrite (nth_map_seq_any _ tau i xzero hi).
      unfold Wk. change (nth kk (map (@List.concat Z) (Wpol wr we1 we2)) []) with (nth kk (map (@List.concat Z) (Wpol wr we1 we2)) (@List.concat Z [])).
      rewrite map_nth.
      rewrite (nth_concat_uniform _ N i y hlq hy) by lia. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the layout identity on the honest rows *)

  Definition rpF (T : ptrace) (p : nat) : list F -> F := tabOf (map to_F (nth p (rpP pplain a b (tru T) (trv T)) [])).

  Lemma kmask_len : cok -> List.length (kmask k) = n_mask n1 ell.
  Proof. intros hk. destruct hk as (_ & _ & _ & _ & _ & _ & h & _). exact h. Qed.

  Lemma tablesB_rp : forall T p, (p < 3)%nat ->
    nth p (tablesB n1 pplain a b wr we1 we2 k (tru T) (trv T) (trA T)) [] = nth p (rpP pplain a b (tru T) (trv T)) [].
  Proof. intros T p hp. unfold tablesB. rewrite app_nth1 by (unfold rpP; cbn; lia). reflexivity. Qed.

  Lemma tablesB_W : forall T p, (p < 3)%nat ->
    nth (3 + p) (tablesB n1 pplain a b wr we1 we2 k (tru T) (trv T) (trA T)) [] = nth p (WpP wr we1 we2 (trA T)) [].
  Proof.
    intros T p hp. unfold tablesB. rewrite app_nth2 by (unfold rpP; cbn; lia).
    replace (3 + p - List.length (rpP pplain a b (tru T) (trv T)))%nat with p by (unfold rpP; cbn; lia).
    rewrite app_nth1 by (unfold WpP, Wpol; rewrite !length_map; cbn; lia). reflexivity.
  Qed.

  Theorem layout_targets : pok -> wshape -> cok -> stmt_ok n1 ell a b cin -> forall T,
    List.length (tru T) = N -> List.length (trv T) = N ->
    List.length (trA T) = ell -> List.length (try T) = n1 -> List.length (trz T) = m ->
    map (@gtval Fq2 fzero fadd fmul (PF T) kindM
               (@LtM Fq2 fzero fone fadd fmul fsub n1 ell lo1 lo2 (map to_F (trA T)) (map to_F (try T)) (map to_F (trz T))))
        (@claims9 Fq2 fzero fone fadd fmul fsub ftg (to_F (invNE n1)) n1 ell lo1 lo2 SO (dAE ell) (dBE n1) (dCE n1 ell)
                  (map to_F (trA T)) (map to_F (try T)) (map to_F (trz T)) (to_F (nth 0 (trhoB T) xzero))
                  (rpF T 0) (rpF T 1) (rpF T 2))
    = targets n1 ell pplain a b cin cout sig wr we1 we2 k T.
  Proof.
    intros hp hw hk hs T hu hv hrA hry hrz.
    pose proof (kmask_len hk) as hkm.
    pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    assert (hlr : forall l : list xf, List.length (map to_F l) = List.length l) by (intro; apply length_map).
    rewrite (@layout_identity Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field (PF T) ftg (to_F (invNE n1))
               n1 ell lo1 lo2 SO (dAE ell) (dBE n1) (dCE n1 ell) _ _ _ _ _ _ _
               ltac:(rewrite length_map; exact hrA) ltac:(rewrite length_map; exact hry) ltac:(rewrite length_map; exact hrz)
               (dA_len ell) (dB_len n1) (dC_len n1 ell)).
    assert (hnm : (n_mask n1 ell = 7 + (1 + list_sum (dAE ell)) + (1 + list_sum (dBE n1)) + (1 + list_sum (dCE n1 ell)))%nat)
      by reflexivity.
    pose proof (dsumL_list_sum (dAE ell)) as q1. pose proof (dsumL_list_sum (dBE n1)) as q2.
    pose proof (dsumL_list_sum (dCE n1 ell)) as q3.
    unfold targets. cbv zeta. apply cons9.
    - unfold mstar. rewrite (mle_list ell _ (uPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) (trA T)).
      + unfold auT. rewrite (Pm_eq hp hw hk T), ment_row by lia. reflexivity.
      + unfold uP. rewrite length_map. apply hP_length.
      + exact hrA.
      + intros x hx. apply (u_tab hp hw hk T x hx).
    - unfold mstar. rewrite (mle_list ell _ (uhPx (tru T) (trv T) (ExecProve.alT T) (ExecProve.beT T)) (trA T)).
      + unfold auhT. rewrite (Pm_eq hp hw hk T), ment_row by lia. reflexivity.
      + unfold uhP. rewrite length_map. apply (hhP_length n1 ell cout sig wr we1 we2 _ _ _ _ hw).
      + exact hrA.
      + intros x hx. apply (uh_tab hp hw hk T x hx).
    - unfold mstar, s_valP. rewrite to_F_add, to_F_mul, to_F_zval.
      rewrite (mle_list ell _ (map bx (sigZ sig)) (trA T)).
      + unfold asgT. rewrite (Pm_eq hp hw hk T), ment_row by lia. reflexivity.
      + rewrite length_map. exact (proj1 (sigZ_rows hw)).
      + exact hrA.
      + intros x hx. unfold sgT. apply (sg_tab hw hk T x hx).
    - unfold MixSummands.gB.
      assert (hrp : forall p, (p < 3)%nat -> mle2 n1 (rpF T p) (map to_F (try T))
                      = to_F (xmle (nth p (tablesB n1 pplain a b wr we1 we2 k (tru T) (trv T) (trA T)) []) (try T))).
      { intros p hp3. rewrite tablesB_rp by exact hp3. rewrite to_F_mle.
        + rewrite hry. reflexivity.
        + rewrite hry. pose proof (rpP_lengths n1 pplain a b (tru T) (trv T) ha hb hn1 hu hv) as hl.
          rewrite Forall_forall in hl. apply hl, nth_In. unfold rpP; cbn; lia. }
      rewrite (hrp 0%nat), (hrp 1%nat), (hrp 2%nat) by lia.
      unfold W1T, W2T, W3T.
      rewrite (W_fold hw hk T 0 (trA T) (try T)), (W_fold hw hk T 1 (trA T) (try T)), (W_fold hw hk T 2 (trA T) (try T)) by lia.
      rewrite <-(tablesB_W T 0), <-(tablesB_W T 1), <-(tablesB_W T 2) by lia. cbn [Nat.add].
      assert (hN : nF2 N <> fzero).
      { apply (Fq2_char_upto (N + tau)); [lia |]. split; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | lia]. }
      assert (hc6 : to_F (xmle (nth 6 (tablesB n1 pplain a b wr we1 we2 k (tru T) (trv T) (trA T)) []) (try T))
                    = fmul (fmul (to_F (a_h k)) (Zp2 (map to_F (trA T)))) (finv (nF2 N))).
      { unfold tablesB, rpP, WpP, Wpol. cbn [map app nth].
        rewrite xmle_sum by (rewrite repeat_length, hry; reflexivity).
        rewrite (fsum_seq_ext _ (fun i => fmul (nth i (map to_F (xeq_table (try T))) fzero) (to_F (cstP n1 k (trA T))))).
        + rewrite fsum_map_mul_r, eq_table_sum. unfold cstP. rewrite !to_F_mul, to_F_inv, to_F_xfint, to_F_zval. field; exact hN.
        + intros i hi. rewrite hry in hi. rewrite (nth_indep _ xzero (cstP n1 k (trA T))) by (rewrite repeat_length; exact hi).
          rewrite nth_repeat. reflexivity. }
      rewrite hc6.
      unfold ahT, a0BT, csBT, maskA0, offB, offA. rewrite (Pm_eq hp hw hk T).
      rewrite (ment_row _ _ _ 3) by lia. rewrite ment_row by lia. rewrite maskCs_row by lia.
      unfold ExecProve.gB, mask_of, dA. cbn [fst snd]. rewrite nth_skipn, Nat.add_0_r, q1.
      replace (7 + 1 + list_sum (dAE ell))%nat with (8 + list_sum (dAE ell))%nat by lia.
      unfold invNE. rewrite to_F_inv, to_F_xint_nat. unfold a_h. reflexivity.
    - unfold mstar, W1T. rewrite (mle_list m _ (map bx (nth 0 (Wk wr we1 we2) [])) (trz T)).
      + unfold aw1T. rewrite (Pm_eq hp hw hk T), ment_row by lia. reflexivity.
      + rewrite length_map. exact (proj1 (Wk_rows hw 0 ltac:(lia))).
      + exact hrz.
      + intros x hx. rewrite (W_tab hw hk T 0 x ltac:(lia) hx). change xzero with (bx 0%Z). rewrite map_nth. reflexivity.
    - unfold mstar, W2T. rewrite (mle_list m _ (map bx (nth 1 (Wk wr we1 we2) [])) (trz T)).
      + unfold aw2T. rewrite (Pm_eq hp hw hk T), ment_row by lia. reflexivity.
      + rewrite length_map. exact (proj1 (Wk_rows hw 1 ltac:(lia))).
      + exact hrz.
      + intros x hx. rewrite (W_tab hw hk T 1 x ltac:(lia) hx). change xzero with (bx 0%Z). rewrite map_nth. reflexivity.
    - unfold mstar, W3T. rewrite (mle_list m _ (map bx (nth 2 (Wk wr we1 we2) [])) (trz T)).
      + unfold aw3T. rewrite (Pm_eq hp hw hk T), ment_row by lia. reflexivity.
      + rewrite length_map. exact (proj1 (Wk_rows hw 2 ltac:(lia))).
      + exact hrz.
      + intros x hx. rewrite (W_tab hw hk T 2 x ltac:(lia) hx). change xzero with (bx 0%Z). rewrite map_nth. reflexivity.
    - unfold a0AT, csAT, maskA0, offA. rewrite (Pm_eq hp hw hk T). rewrite ment_row by lia. rewrite maskCs_row by lia.
      unfold gA, mask_of. cbn [fst snd]. rewrite nth_skipn, Nat.add_0_r. reflexivity.
    - unfold a0CT, csCT, maskA0, offC, offB, offA. rewrite (Pm_eq hp hw hk T). rewrite ment_row by lia.
      rewrite maskCs_row by lia.
      unfold gC, mask_of, dA, dB. cbn [fst snd]. rewrite nth_skipn, Nat.add_0_r. rewrite q1, q2.
      replace (7 + 1 + list_sum (dAE ell) + 1 + list_sum (dBE n1))%nat with (9 + list_sum (dAE ell) + list_sum (dBE n1))%nat by lia.
      reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the batched value check *)

  Local Notation fpreT := (fpre n1 ell sig k).
  Local Notation clsPT := (clsP n1 ell lo1 lo2 pplain a b sig k).

  Lemma comb_msum : forall T cb, map to_F (comb bBx b1x (b2x T) cb) = @msum Fq2 fadd fmul (PF T) (map pairF cb).
  Proof.
    intros T cb. unfold comb. induction cb as [| [i w] cb ih]; [reflexivity |].
    cbn [fold_right map Opening.msum fst snd]. rewrite to_F_padd, to_F_pscale, ih. reflexivity.
  Qed.

  Lemma Lk_ext : forall (kind : nat -> bool) (Lt Lt' : nat -> list F) kp cls v, (forall v', Lt v' = Lt' v') ->
    @Lk Fq2 fadd fmul kind Lt kp cls v = @Lk Fq2 fadd fmul kind Lt' kp cls v.
  Proof. intros kind Lt Lt' kp cls v h. unfold Lk. destruct (kind v); [reflexivity | apply h]. Qed.

  Lemma LtE_F : forall T, List.length (trA T) = ell -> List.length (try T) = n1 -> List.length (trz T) = m ->
    forall v, map to_F (LtE lo1 lo2 (fpreT T) v)
              = @LtM Fq2 fzero fone fadd fmul fsub n1 ell lo1 lo2 (map to_F (trA T)) (map to_F (try T)) (map to_F (trz T)) v.
  Proof.
    intros T hrA hry hrz v. unfold LtE, LtM, fpre. cbn [frA fry frz].
    destruct (Nat.eqb v 1); [| destruct (Nat.eqb v 2)]; rewrite to_F_lo_vec.
    + rewrite length_app, hry, hrA, map_app. reflexivity.
    + rewrite hrz. reflexivity.
    + rewrite hrA. reflexivity.
  Qed.

  Lemma clsF_eq : forall T, List.length (tru T) = N -> List.length (trv T) = N ->
    List.length (trA T) = ell -> List.length (try T) = n1 -> List.length (trz T) = m -> stmt_ok n1 ell a b cin ->
    map (map ExecClaims.tF) (clsPT T)
    = @claims9 Fq2 fzero fone fadd fmul fsub ftg (to_F (invNE n1)) n1 ell lo1 lo2 SO (dAE ell) (dBE n1) (dCE n1 ell)
               (map to_F (trA T)) (map to_F (try T)) (map to_F (trz T)) (to_F (nth 0 (trhoB T) xzero))
               (rpF T 0) (rpF T 1) (rpF T 2).
  Proof.
    intros T hu hv hrA hry hrz hs. pose proof hs as (ha & hb & _ & hn1 & _).
    pose proof (rpP_lengths n1 pplain a b (tru T) (trv T) ha hb hn1 hu hv) as hl. unfold rpP in hl.
    repeat rewrite Forall_cons_iff in hl. destruct hl as (l1 & l2 & l3 & _).
    unfold clsP, clsE, fpre. cbn [frA fry frz frhoB fru frv].
    apply to_F_claims9; [exact hrA | exact hry | exact hrz | | |];
      unfold rpF, rpP, rp1E, rp2E, rp3E; cbn [nth fru frv]; rewrite to_F_mle, hry by (rewrite hry; assumption);
      reflexivity.
  Qed.

  Theorem batch_honest : pok -> wshape -> cok -> stmt_ok n1 ell a b cin -> forall T,
    List.length (tru T) = N -> List.length (trv T) = N ->
    List.length (trA T) = ell -> List.length (try T) = n1 -> List.length (trz T) = m -> List.length (tkp T) = 9%nat ->
    fsum (map (fun v => dot (map to_F (usP n1 ell lo1 lo2 pplain a b sig k bBx b1x (b2x T) T v))
                            (map to_F (LP n1 ell lo1 lo2 pplain a b sig k T v))) [1; 2; 3; 4]%nat)
    = dot (map to_F (tkp T)) (targets n1 ell pplain a b cin cout sig wr we1 we2 k T).
  Proof.
    intros hp hw hk hs T hu hv hrA hry hrz hkp.
    set (LtMT := @LtM Fq2 fzero fone fadd fmul fsub n1 ell lo1 lo2 (map to_F (trA T)) (map to_F (try T)) (map to_F (trz T))).
    set (clsF := map (map ExecClaims.tF) (clsPT T)).
    transitivity (fsum (map (fun v => @vsum Fq2 fzero fadd fmul (PF T) (@cbk Fq2 fone fmul kindM (frowM ell lo2 SO) (map to_F (tkp T)) clsF v)
                                         (@Lk Fq2 fadd fmul kindM LtMT (map to_F (tkp T)) clsF v)) [1; 2; 3; 4]%nat)).
    { apply (@fsum_map_ext Fq2 fzero fadd). intros v _.
      unfold usP, LP. rewrite comb_msum, to_F_cbk, to_F_Lk.
      rewrite (@dot_msum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
      f_equal. apply Lk_ext. intro v'. apply LtE_F; assumption. }
    rewrite (@batch_mixed Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field (PF T) kindM LtMT (frowM ell lo2 SO)
               [1; 2; 3; 4]%nat clsF (map to_F (tkp T))).
    - f_equal. unfold clsF. rewrite (clsF_eq T hu hv hrA hry hrz hs).
      apply (layout_targets hp hw hk hs T hu hv hrA hry hrz).
    - repeat constructor; cbn; intuition discriminate.
    - unfold clsF, clsP, clsE, xclaims9. rewrite !length_map. cbn. exact hkp.
    - intros cl hcl t ht. unfold clsF in hcl. rewrite (clsF_eq T hu hv hrA hry hrz hs) in hcl.
      destruct (@claims9_terms Fq2 fzero fone fadd fmul fsub ftg _ n1 ell lo1 lo2 SO (dAE ell) (dBE n1) (dCE n1 ell)
                  _ _ _ _ _ _ _ ltac:(rewrite length_map; exact hrA) ltac:(rewrite length_map; exact hry)
                  ltac:(rewrite length_map; exact hrz) (dA_len ell) (dB_len n1) (dC_len n1 ell) cl t hcl ht)
        as [[e _] | [[e _] | [[e _] | [e _]]]]; rewrite e; cbn; tauto.
    - intros cl hcl t ht hkd. unfold clsF in hcl. rewrite (clsF_eq T hu hv hrA hry hrz hs) in hcl.
      destruct (@claims9_terms Fq2 fzero fone fadd fmul fsub ftg _ n1 ell lo1 lo2 SO (dAE ell) (dBE n1) (dCE n1 ell)
                  _ _ _ _ _ _ _ ltac:(rewrite length_map; exact hrA) ltac:(rewrite length_map; exact hry)
                  ltac:(rewrite length_map; exact hrz) (dA_len ell) (dB_len n1) (dC_len n1 ell) cl t hcl ht)
        as [[e _] | [[e _] | [[e _] | [e er]]]]; rewrite e in hkd |- *; cbn in hkd; try discriminate.
      exact er.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the opened columns are the codewords of the honest rows *)

  Local Notation fTx := (fT n1 ell lo1 lo2).
  Local Notation partsT := (fun T => parts_of n1 ell lo1 lo2 pplain a b sig k bBx b1x (b2x T) T).

  Lemma XeB : wshape -> cok -> forall T i j, In j (map Z.to_nat (tJB T)) -> (j < nB)%nat -> (i < SO)%nat ->
    to_F (fXe (fTx (partsT T) T) i j) = peval (PF T i) (pw2 (to_F (bx omB)) j).
  Proof.
    intros hw hk T i j hj hjn hi.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hlB _].
    unfold fT, front_mk. cbv zeta. cbn [fXe].
    destruct (Nat.ltb_spec i (SOE n1 ell lo1)) as [_ | h]; [| lia].
    cbn [parts_of qcB]. rewrite map_map. rewrite nth_idx_map by exact hj. cbn [flat_map fst bitem]. rewrite app_nil_r.
    unfold btB. rewrite commit_col by exact hjn.
    rewrite (nth_map_indep _ _ i []) by (rewrite hlB; unfold SOE in hi; lia).
    rewrite zenc_F by exact hjn.
    unfold PF. rewrite AM_eq, app_nth1 by (rewrite hlB; unfold SOE in hi; lia). reflexivity.
  Qed.

  Lemma XeS : pok -> wshape -> cok -> forall T i j, In j (map Z.to_nat (tJS T)) -> (j < nS)%nat ->
    (SO <= i < SO + (rs + 6) + (4 * rs + 1))%nat ->
    to_F (fXe (fTx (partsT T) T) i j) = peval (PF T i) (pw2 (to_F (bx omS)) j).
  Proof.
    intros hp hw hk T i j hj hjn hi.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hlB _].
    destruct (msgsS1_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 k hw hk) as [hl1 _].
    destruct (msgsS2_shape n1 ell lo1 lo2 kB nB nqB kS nS nqS pplain a b cin cout sig wr we1 we2 k (tru T) (trv T)
                (ExecProve.alT T) (ExecProve.beT T) hp hw hk) as [hl2 _].
    unfold fT, front_mk. cbv zeta. cbn [fXe].
    destruct (Nat.ltb_spec i (SOE n1 ell lo1)) as [h | _]; [unfold SOE in *; lia |].
    cbn [parts_of qcS]. rewrite map_map. rewrite nth_idx_map by exact hj. cbn [flat_map fst bitem]. rewrite app_nil_r.
    unfold btS1, b2x, btS2. rewrite !commit_col by exact hjn. rewrite <-map_app.
    rewrite (nth_map_indep _ _ (i - SOE n1 ell lo1) []) by (rewrite length_app, hl1, hl2; unfold SOE in *; lia).
    rewrite zenc_F by exact hjn.
    unfold PF. rewrite AM_eq, (app_nth2 (msgsB lo1 wr we1 we2 k)) by (rewrite hlB; unfold SOE in *; lia). rewrite hlB. reflexivity.
  Qed.

  (* the codeword of a combination of rows, at an opened column *)
  Lemma enc_comb : forall (Xe : nat -> nat -> xf) (om : xf) (J : list nat) (PFx : nat -> list F) (cb : list (nat * xf)),
    (forall iw, In iw cb -> forall j, In j J -> to_F (Xe (fst iw) j) = peval (PFx (fst iw)) (pw2 (to_F om) j)) ->
    forall j, In j J -> peval (@msum Fq2 fadd fmul PFx (map pairF cb)) (pw2 (to_F om) j) = to_F (xwsum Xe cb j).
  Proof.
    intros Xe om J PFx cb h j hj. induction cb as [| [i w] cb ih].
    { cbn [map Opening.msum xwsum PolyRoots.eval]. symmetry. exact to_F_zero. }
    cbn [map Opening.msum xwsum pairF fst snd].
    rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
            (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite ih by (intros iw hiw; apply h; right; exact hiw).
    pose proof (h (i, w) (or_introl eq_refl) j hj) as e. cbn [fst] in e.
    rewrite to_F_add, to_F_mul, e. reflexivity.
  Qed.

  Lemma xwsum_combine : forall (Xe : nat -> nat -> xf) (rws : list nat) (gam : list xf) j,
    to_F (xwsum Xe (combine rws gam) j) = to_F (xdot gam (map (fun i => Xe i j) rws)).
  Proof.
    intros Xe rws; induction rws as [| i rws ih]; intros gam j; destruct gam as [| g gam]; try reflexivity.
    cbn [combine xwsum map xdot fst snd]. rewrite !to_F_add, ih. reflexivity.
  Qed.

  Lemma xeval_reduced : forall p x, reduced (xeval p x).
  Proof. intros [| c p] x; [exact xzero_reduced | apply xadd_reduced]. Qed.

  (* the rows that the compiled slots and the slot masks use *)
  Lemma cb_rows : forall T, List.length (trA T) = ell -> List.length (try T) = n1 -> List.length (trz T) = m ->
    forall v iw, In iw (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsPT T) v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < SO)%nat) /\ ((v = 3 \/ v = 4)%nat -> (SO <= fst iw < SO + (rs + 6) + (4 * rs + 1))%nat).
  Proof.
    intros T hrA hry hrz v iw h. unfold xcbk, kindE in h. destruct (Nat.eqb_spec v 4) as [e | e].
    + subst v. destruct h as [<- | []]. cbn [fst]. unfold frowE, MixLayout.rM. change (MixLayout.rs ell lo2) with rs.
      split; intro hv; [lia | lia].
    + destruct (xgbatch_rows _ _ _ _ h) as (cl & t & h1 & h2 & h3 & h4).
      assert (hr : row_ok n1 ell lo1 lo2 SO t).
      { unfold clsP, clsE in h1. exact (xclaims9_rows n1 ell lo1 lo2 SO _ _ _ _ _ _ _ _ _ _ _ hrA hry hrz cl t h1 h2). }
      destruct hr as (hs & hb & hsm). rewrite h4. split; intro hv.
      * assert (trowx t < 3 * MixLayout.rw n1 ell lo1)%nat by (apply hb; lia). unfold SOE, rwE. lia.
      * apply hsm. lia.
  Qed.

  Lemma mcb_rows : forall v iw, In iw (mcbE n1 ell lo1 lo2 v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < SO)%nat) /\ ((v = 3 \/ v = 4)%nat -> (SO <= fst iw < SO + (rs + 6) + (4 * rs + 1))%nat).
  Proof.
    intros v iw h. split; intro hv.
    + destruct hv as [-> | ->]; cbn in h; destruct h as [<- | [<- | []]]; cbn [fst]; unfold SOE; lia.
    + destruct hv as [-> | ->]; cbn in h; destruct h as [<- | [<- | []]]; cbn [fst]; unfold SOE; lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* step 4: the opening accepts *)

  Local Notation vecPT := (fun T => vecP n1 ell lo1 lo2 pplain a b sig k bBx b1x (b2x T) T).
  Local Notation msPT := (fun T => msP n1 ell lo1 lo2 bBx b1x (b2x T)).
  Local Notation usPT := (fun T => usP n1 ell lo1 lo2 pplain a b sig k bBx b1x (b2x T) T).
  Local Notation LPT := (fun T => LP n1 ell lo1 lo2 pplain a b sig k T).

  Lemma eval_vec : forall T om n J (Xe : nat -> nat -> xf) v (R : nat -> Prop),
    (forall i j, R i -> In j J -> to_F (Xe i j) = peval (PF T i) (pw2 (to_F om) j)) ->
    (forall iw, In iw (mcbE n1 ell lo1 lo2 v) -> R (fst iw)) ->
    (forall iw, In iw (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsPT T) v) -> R (fst iw)) ->
    forall j, In j J ->
    xeqb (xenc_at om n (xencv (fst om) n (vecPT T v)) (vecPT T v) j)
         (xxw Xe (mcbE n1 ell lo1 lo2 v) (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsPT T) v) (nth 0 (tcl T) xzero) j) = true.
  Proof.
    intros T om n J Xe v R hX hm hc j hj.
    apply xeqb_spec; [apply xenc_at_reduced | apply xadd_reduced |].
    rewrite (to_F_enc_at om n _ _ j eq_refl). unfold ReedSolomon.rs_enc, vecP, msP, usP.
    rewrite to_F_padd, to_F_pscale, !comb_msum.
    rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
            (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (enc_comb Xe om J (PF T) (mcbE n1 ell lo1 lo2 v)), (enc_comb Xe om J (PF T) (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsPT T) v));
      try exact hj; try (intros iw hiw j' hj'; apply hX; [first [apply hm; exact hiw | apply hc; exact hiw] | exact hj']).
    unfold xxw. rewrite to_F_add, to_F_mul. reflexivity.
  Qed.

  Theorem open_complete : pok -> wshape -> cok -> stmt_ok n1 ell a b cin -> forall T,
    List.length (tru T) = N -> List.length (trv T) = N ->
    List.length (trA T) = ell -> List.length (try T) = n1 -> List.length (trz T) = m -> List.length (tkp T) = 9%nat ->
    (forall j, In j (map Z.to_nat (tJB T)) -> (j < nB)%nat) -> (forall j, In j (map Z.to_nat (tJS T)) -> (j < nS)%nat) ->
    wf_parts n1 ell lo1 lo2 kB nB nqB kS nS nqS (partsT T) ->
    forall vals, map to_F vals = targets n1 ell pplain a b cin cout sig wr we1 we2 k T ->
    openE n1 ell lo1 lo2 kB nB kS nS omB omS pplain a b (fTx (partsT T) T) vals = true.
  Proof.
    intros hp hw hk hs T hu hv hrA hry hrz hkp hJB hJS hwf vals hvals.
    destruct hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hv1 & hv2 & hv3 & hv4 & hpB & hpS & _).
    cbn [parts_of qv1 qv2 qv3 qv4 qpvB qpvS] in hv1, hv2, hv3, hv4, hpB, hpS.
    unfold openE, xaccO. rewrite !andb_true_iff. split; [split |].
    - (* the batched value check *)
      apply xeqb_spec; [apply xfsum_reduced | apply xadd_reduced |].
      rewrite to_F_fsum, map_map, to_F_add, to_F_mul, to_F_dot, hvals.
      transitivity (fsum (map (fun v => fadd (dot (map to_F (msPT T v)) (map to_F (LPT T v)))
                                              (fmul (to_F (nth 0 (tcl T) xzero)) (dot (map to_F (usPT T v)) (map to_F (LPT T v)))))
                              [1; 2; 3; 4]%nat)).
      { apply (@fsum_map_ext Fq2 fzero fadd). intros v hv'.
        replace (fub (fTx (partsT T) T) v) with (vecPT T v)
          by (cbn in hv'; destruct hv' as [<- | [<- | [<- | [<- | []]]]]; reflexivity).
        change (xLk kindE (LtE lo1 lo2 (fTx (partsT T) T)) (fkp (fTx (partsT T) T)) (clsE n1 ell lo1 lo2 pplain a b (fTx (partsT T) T)) v)
          with (LPT T v).
        unfold vecP. rewrite to_F_dot, to_F_padd, to_F_pscale.
        rewrite (@dot_padd_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
                (@dot_pscale_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). reflexivity. }
      rewrite <-ExecFold.fsum_map_add, (@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
      rewrite (batch_honest hp hw hk hs T hu hv hrA hry hrz hkp).
      assert (hmu : to_F (fmu (fTx (partsT T) T))
                    = fsum (map (fun v => dot (map to_F (msPT T v)) (map to_F (LPT T v))) [1; 2; 3; 4]%nat)).
      { unfold fT, front_mk. cbv zeta. cbn [fmu parts_of qmu]. unfold muP. rewrite to_F_fsum, map_map.
        apply (@fsum_map_ext Fq2 fzero fadd). intros v _. apply to_F_dot. }
      rewrite hmu. reflexivity.
    - (* the big matrix *)
      unfold xmacc. cbv zeta. rewrite !andb_true_iff. split; [split |].
      + apply Nat.leb_le. destruct hpB as [e _]. exact (Nat.eq_le_incl _ _ e).
      + apply forallb_forall. intros j hj. apply xeqb_spec; [apply xenc_at_reduced | apply xadd_reduced |].
        replace (fpvB (fTx (partsT T) T)) with (pvBP n1 ell lo1 bBx b1x (b2x T) T) by reflexivity.
        replace (fgB (fTx (partsT T) T)) with (firstn (3 * rw + 4) (tgB T)) by reflexivity.
        rewrite (to_F_enc_at _ _ _ _ j eq_refl). unfold ReedSolomon.rs_enc, pvBP. rewrite to_F_padd, !comb_msum.
        rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
        assert (hX : forall i j', (i < SO)%nat -> In j' (map Z.to_nat (tJB T)) ->
                       to_F (fXe (fTx (partsT T) T) i j') = peval (PF T i) (pw2 (to_F (bx omB)) j'))
          by (intros i j' hi hj'; apply XeB; [exact hw | exact hk | exact hj' | apply hJB, hj' | exact hi]).
        rewrite (enc_comb (fXe (fTx (partsT T) T)) (bx omB) (map Z.to_nat (tJB T)) (PF T)
                   [((3 * rw + 4)%nat, xone); ((3 * rw + 5)%nat, xtg)]) by
          (first [exact hj | intros iw hiw j' hj'; apply hX; [cbn in hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; unfold SOE; lia | exact hj']]).
        rewrite (enc_comb (fXe (fTx (partsT T) T)) (bx omB) (map Z.to_nat (tJB T)) (PF T)
                   (combine (rwsBE n1 ell lo1) (firstn (3 * rw + 4) (tgB T)))) by
          (first [exact hj | intros [i w] hiw j' hj'; apply hX; [apply in_combine_l in hiw; unfold rwsBE in hiw; apply in_seq in hiw; cbn [fst]; unfold SOE; lia | exact hj']]).
        unfold xpi, xmpBE. rewrite xwsum_combine. cbn [xwsum fst snd].
        rewrite !to_F_add, !to_F_mul, to_F_one, to_F_zero. field.
      + apply forallb_forall. intros v hv'. apply andb_true_iff. split.
        * apply Nat.leb_le. cbn in hv'. destruct hv' as [<- | [<- | []]];
            [destruct hv1 as [e _] | destruct hv2 as [e _]]; exact (Nat.eq_le_incl _ _ e).
        * apply forallb_forall. intros j hj.
          replace (fub (fTx (partsT T) T) v) with (vecPT T v) by (cbn in hv'; destruct hv' as [<- | [<- | []]]; reflexivity).
          apply (eval_vec T (bx omB) nB (map Z.to_nat (tJB T)) (fXe (fTx (partsT T) T)) v (fun i => (i < SO)%nat)); [| | | exact hj].
          -- intros i j' hi hj'. apply XeB; [exact hw | exact hk | exact hj' | apply hJB, hj' | exact hi].
          -- intros iw hiw. apply (mcb_rows v iw hiw). cbn in hv'. lia.
          -- intros iw hiw. apply (cb_rows T hrA hry hrz v iw hiw). cbn in hv'. lia.
    - (* the small matrix *)
      unfold xmacc. cbv zeta. rewrite !andb_true_iff. split; [split |].
      + apply Nat.leb_le. destruct hpS as [e _]. exact (Nat.eq_le_incl _ _ e).
      + apply forallb_forall. intros j hj. apply xeqb_spec; [apply xenc_at_reduced | apply xadd_reduced |].
        replace (fpvS (fTx (partsT T) T)) with (pvSP n1 ell lo1 lo2 bBx b1x (b2x T) T) by reflexivity.
        replace (fgS (fTx (partsT T) T)) with (firstn (rs + 4) (tgS T) ++ skipn (rs + 6) (tgS T)) by reflexivity.
        rewrite (to_F_enc_at _ _ _ _ j eq_refl). unfold ReedSolomon.rs_enc, pvSP. rewrite to_F_padd, !comb_msum.
        rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
        assert (hX : forall i j', (SO <= i < SO + (rs + 6) + (4 * rs + 1))%nat -> In j' (map Z.to_nat (tJS T)) ->
                       to_F (fXe (fTx (partsT T) T) i j') = peval (PF T i) (pw2 (to_F (bx omS)) j'))
          by (intros i j' hi hj'; apply XeS; [exact hp | exact hw | exact hk | exact hj' | apply hJS, hj' | exact hi]).
        rewrite (enc_comb (fXe (fTx (partsT T) T)) (bx omS) (map Z.to_nat (tJS T)) (PF T)
                   [((SO + rs + 4)%nat, xone); ((SO + rs + 5)%nat, xtg)]) by
          (first [exact hj | intros iw hiw j' hj'; apply hX; [cbn [In] in hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; lia | exact hj']]).
        rewrite (enc_comb (fXe (fTx (partsT T) T)) (bx omS) (map Z.to_nat (tJS T)) (PF T)
                   (combine (rwsSE n1 ell lo1 lo2) (firstn (rs + 4) (tgS T) ++ skipn (rs + 6) (tgS T)))) by
          (first [exact hj | intros [i w] hiw j' hj'; apply hX;
                    [apply in_combine_l in hiw; unfold rwsSE in hiw; apply in_map_iff in hiw; destruct hiw as (i0 & <- & hi0);
                     apply in_app_or in hi0; destruct hi0 as [hi0 | hi0]; apply in_seq in hi0; cbn [fst]; lia | exact hj']]).
        unfold xpi, xmpSE. rewrite xwsum_combine. cbn [xwsum fst snd].
        rewrite !to_F_add, !to_F_mul, to_F_one, to_F_zero. field.
      + apply forallb_forall. intros v hv'. apply andb_true_iff. split.
        * apply Nat.leb_le. cbn in hv'. destruct hv' as [<- | [<- | []]];
            [destruct hv3 as [e _] | destruct hv4 as [e _]]; exact (Nat.eq_le_incl _ _ e).
        * apply forallb_forall. intros j hj.
          replace (fub (fTx (partsT T) T) v) with (vecPT T v) by (cbn in hv'; destruct hv' as [<- | [<- | []]]; reflexivity).
          apply (eval_vec T (bx omS) nS (map Z.to_nat (tJS T)) (fXe (fTx (partsT T) T)) v
                   (fun i => (SO <= i < SO + (rs + 6) + (4 * rs + 1))%nat)); [| | | exact hj].
          -- intros i j' hi hj'. apply XeS; [exact hp | exact hw | exact hk | exact hj' | apply hJS, hj' | exact hi].
          -- intros iw hiw. apply (mcb_rows v iw hiw). cbn in hv'. lia.
          -- intros iw hiw. apply (cb_rows T hrA hry hrz v iw hiw). cbn in hv'. lia.
  Qed.

End BackO.
