(* Completeness, back end (stage P5, steps 3 and 4): for a valid witness,
   the verifier's back end accepts the record that its front end builds
   from the prover's output.

   Valid witness (valid): sig is the permutation sigma, and over GF(q^2)
   the outputs are the inputs permuted by sigma and re-randomised with
   ternary (r, e1, e2), i.e. Rmix of Bgv.v holds for the field images of
   the public key, the ciphertexts and the witness.

   Step 3 (this part): the three sumchecks start from their true sums.
     sumA  csum of the summand of A over the cube is kA0 + kA1: u h = 1 and
           uhat hhat = 1 on the cube, and the two sums of inverses agree
           because hhat_j = h_(sigma j) (proj_rerand) and sigma is a
           permutation;
     sumB  the summand of B sums to Hd - zpub(r) - beta idx(r) + alpha, by the
           definition of h;
     sumC  the summand of C sums to 0 (w^3 = w for ternary w). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex LayoutLemmas RowLayout MixBridge Opening SlotKinds MaskedExt MixSummands MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecMerkle ExecProveBase ExecSerial ExecFold ExecFront ExecShape ExecDec ExecProve ExecRows.
Import ListNotations.

Add Field fieldF2b : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation fsum := (@LogDer.fsum Fq2 fzero fadd).
Local Notation dot := (@LogDer.dot Fq2 fzero fadd fmul).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation nF2 := (@nF Fq2 fzero fone fadd).

(* ---------------------------------------------------------------------- *)
(* sums over seq *)

Lemma nth_map_seq_F : forall (f : nat -> F) n i, (i < n)%nat -> nth i (map f (seq 0 n)) fzero = f i.
Proof.
  intros f n i hi. rewrite (nth_indep _ fzero (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
  rewrite map_nth, seq_nth by exact hi. reflexivity.
Qed.

Lemma fsum_seq_ext : forall (f g : nat -> F) n, (forall i, (i < n)%nat -> f i = g i) ->
  fsum (map f (seq 0 n)) = fsum (map g (seq 0 n)).
Proof.
  intros f g n h. apply (@fsum_map_ext Fq2 fzero fadd). intros i hi. apply in_seq in hi. apply h. lia.
Qed.

Lemma nth_map_seq_any : forall {A : Type} (f : nat -> A) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros A f n i d hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
  rewrite map_nth, seq_nth by exact hi. reflexivity.
Qed.

Lemma nth_ctxF : forall (cs : list (list Z * list Z)) i, nth i (map ctxF (cinX cs)) ([], []) = ctxF (nth i (cinX cs) ([], [])).
Proof. intros cs i. exact (map_nth ctxF (cinX cs) ([], []) i). Qed.

Lemma xnz_all : forall l, existsb (fun x => negb (xnz x)) l = false ->
  forall i, (i < List.length l)%nat -> to_F (nth i l xzero) <> fzero.
Proof.
  intros l h i hi. apply xnz_sound. destruct (xnz (nth i l xzero)) eqn:e; [reflexivity |]. exfalso.
  assert (ht : existsb (fun x => negb (xnz x)) l = true).
  { apply existsb_exists. exists (nth i l xzero). split; [apply nth_In; exact hi | rewrite e; reflexivity]. }
  congruence.
Qed.

Lemma nth_inv_F : forall l i, (i < List.length l)%nat -> nth i (map to_F (map xinv l)) fzero = finv (to_F (nth i l xzero)).
Proof.
  intros l i hi. rewrite <-to_F_nth, <-to_F_inv. f_equal.
  rewrite (nth_indep _ xzero (xinv xzero)) by (rewrite length_map; exact hi). apply map_nth.
Qed.

(* sums: inner products, combine, the rows of WpP *)
Lemma dot_len : forall (u v : list F), dot u v = fsum (map (fun y => fmul (nth y u fzero) (nth y v fzero)) (seq 0 (List.length u))).
Proof.
  induction u as [| x u ih]; intro v; [reflexivity |].
  destruct v as [| y v].
  + cbn [LogDer.dot]. symmetry. apply (@fsum_map_zero_ext Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    intros i _. destruct i; cbn [nth]; field.
  + cbn [LogDer.dot List.length seq map LogDer.fsum nth]. rewrite ih, <-seq_shift, map_map. reflexivity.
Qed.

Lemma fsum_combine : forall {A B : Type} (f : A * B -> F) (l1 : list A) (l2 : list B) d1 d2,
  List.length l1 = List.length l2 ->
  fsum (map f (combine l1 l2)) = fsum (map (fun i => f (nth i l1 d1, nth i l2 d2)) (seq 0 (List.length l1))).
Proof.
  intros A B f l1; induction l1 as [| x l1 ih]; intros l2 d1 d2 h; destruct l2 as [| y l2]; cbn in h; try lia;
    [reflexivity |].
  cbn [combine map List.length seq LogDer.fsum nth]. rewrite (ih l2 d1 d2) by lia. rewrite <-seq_shift, map_map.
  reflexivity.
Qed.

Lemma nth_comb_rows : forall (l : list (xf * list Z)) y,
  nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) l))) fzero
  = fsum (map (fun p => fmul (to_F (fst p)) (to_F (bx (nth y (snd p) 0%Z)))) l).
Proof.
  induction l as [| p l ih]; intro y.
  + cbn [map fold_right LogDer.fsum]. destruct y; reflexivity.
  + cbn [map fold_right LogDer.fsum]. rewrite to_F_padd.
    rewrite (@LogDer.nth_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite to_F_pscale, (@LogDer.nth_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite nth_row_F, ih. reflexivity.
Qed.

Lemma eq_idr_sum : forall r,
  fsum (map (fun i => fmul (nth i (map to_F (xeq_table r)) fzero) (nF2 i)) (seq 0 (2 ^ List.length r)))
  = @idr Fq2 fzero fone fadd fmul (map to_F r).
Proof.
  intro r. rewrite to_F_eq_table. unfold RowLayout.eqvec.
  rewrite <-(@mle_idr Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field (List.length r) (map to_F r))
    by apply length_map.
  rewrite (@mle_seq Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). apply fsum_seq_ext. intros i hi.
  rewrite nth_map_seq_F by exact hi.
  rewrite (@idr_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field (List.length r) i hi). field.
Qed.

Lemma xmle_sum : forall tbl r, List.length tbl = (2 ^ List.length r)%nat ->
  to_F (xmle tbl r)
  = fsum (map (fun i => fmul (nth i (map to_F (xeq_table r)) fzero) (to_F (nth i tbl xzero))) (seq 0 (2 ^ List.length r))).
Proof.
  intros tbl r hl. unfold xmle. rewrite to_F_dot, dot_len, length_map, hl.
  apply fsum_seq_ext. intros i hi. rewrite to_F_nth. field.
Qed.

Lemma fsum_map_mul_r : forall {A : Type} (c : F) (g : A -> F) (l : list A),
  fsum (map (fun x => fmul (g x) c) l) = fmul (fsum (map g l)) c.
Proof. intros A c g l. induction l as [| x l ih]; cbn; [field | rewrite ih; field]. Qed.

(* the eq table at r sums to one *)
Lemma eq_table_sum : forall r, fsum (map (fun i => nth i (map to_F (xeq_table r)) fzero) (seq 0 (2 ^ List.length r))) = fone.
Proof.
  intro r. rewrite to_F_eq_table. unfold RowLayout.eqvec.
  rewrite (fsum_seq_ext _ (fun i => fmul fone (eqp2 (pt2 (List.length r) i) (map to_F r))))
    by (intros i hi; rewrite (nth_map_seq_F _ _ _ hi); field).
  rewrite <-(@mle_seq Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field (List.length r) (fun _ => fone)).
  apply (@mle_const_one Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). apply length_map.
Qed.

(* a sum over a permutation *)
Lemma fsum_sigma : forall (f : nat -> F) (sigma : list nat) n, Permutation sigma (seq 0 n) ->
  fsum (map (fun j => f (nth j sigma 0%nat)) (seq 0 n)) = fsum (map f (seq 0 n)).
Proof.
  intros f sigma n hp.
  assert (hl : List.length sigma = n) by (rewrite (Permutation_length hp), length_seq; reflexivity).
  rewrite <-(map_map (fun j => nth j sigma 0%nat) f).
  replace (map (fun j => nth j sigma 0%nat) (seq 0 n)) with sigma.
  + apply (@fsum_perm Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). apply Permutation_map. exact hp.
  + rewrite <-hl. symmetry. rewrite (map_nth_seq_list (fun x => x) 0%nat sigma). apply map_id.
Qed.

Section Back.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable k : coins.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.

  Local Notation hPx := (hP ell pplain a b cin wr we1 we2).
  Local Notation hhPx := (hhP cout sig).
  Local Notation uPx := (uP ell pplain a b cin wr we1 we2).
  Local Notation uhPx := (uhP cout sig).
  Local Notation tablesAx := (tablesA ell pplain a b cin cout sig wr we1 we2).

  (* ------------------------------------------------------------------ *)
  (* the statement and the witness *)

  Definition stmt_ok : Prop :=
    List.length a = N /\ List.length b = N /\ List.length cin = tau /\ (1 <= n1)%nat /\ (1 <= ell)%nat
    /\ (Z.of_nat (N + tau) < Q)%Z.

  Variable sigma : list nat.

  Definition wsF : list (@rand Fq2) :=
    map (fun i => (map to_F (map bx (nth i wr [])), map to_F (map bx (nth i we1 [])), map to_F (map bx (nth i we2 []))))
        (seq 0 tau).

  Definition valid : Prop :=
    sig = map Z.of_nat sigma
    /\ @Rmix Fq2 fzero fone fadd fmul fopp (map to_F (aX a)) (map to_F (aX b)) (to_F (bx pplain)) N tau
             (map ctxF (cinX cin)) (map ctxF (cinX cout)) sigma wsF.

  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).

  Lemma wsF_nth : forall i, (i < tau)%nat ->
    nth i wsF ([], [], []) = (map to_F (map bx (nth i wr [])), map to_F (map bx (nth i we1 [])), map to_F (map bx (nth i we2 []))).
  Proof.
    intros i hi. unfold wsF.
    exact (nth_map_seq_any (fun i => (map to_F (map bx (nth i wr [])), map to_F (map bx (nth i we1 [])),
                                       map to_F (map bx (nth i we2 [])))) tau i ([], [], []) hi).
  Qed.

  Lemma Wpol_nth : forall (w : list (list Z)) i, map to_F (map bx (nth i (map (map zm) w) [])) = map to_F (map bx (nth i w [])).
  Proof.
    intros w i. change (nth i (map (map zm) w) []) with (nth i (map (map zm) w) (map zm [])).
    rewrite (map_nth (map zm) w [] i), !map_map. apply map_ext. intro z. apply to_F_bx_zm.
  Qed.

  Lemma w_len : wshape -> forall w i, In w [wr; we1; we2] -> (i < tau)%nat -> List.length (nth i w []) = N.
  Proof.
    intros (_ & _ & hw) w i hin hi. rewrite Forall_forall in hw. destruct (hw w hin) as [h1 h2].
    rewrite Forall_forall in h2. apply h2. apply nth_In. lia.
  Qed.

  (* the entries of h and hhat as field elements *)
  Lemma hP_F : forall ru rv al be i, List.length cin = tau -> (i < tau)%nat ->
    to_F (nth i (hPx ru rv al be) xzero)
    = fsub (fadd (fadd (@proj F fzero fadd fmul (map to_F ru) (map to_F rv) (ctxF (nth i (cinX cin) ([], []))))
                       (@wdot F fzero fadd fmul fopp (map to_F (aX a)) (map to_F (aX b)) (to_F (bx pplain))
                              (map to_F ru) (map to_F rv) (nth i wsF ([], [], []))))
                 (fmul (to_F be) (nF2 i))) (to_F al).
  Proof.
    intros ru rv al be i hci hi. unfold hP. cbv zeta. rewrite (nth_map_seq_any _ _ _ xzero hi).
    rewrite (wsF_nth i hi).
    unfold zpubP. rewrite (nth_indep _ xzero (xproj ru rv ([], []))) by (unfold cinX; rewrite !length_map; lia).
    rewrite map_nth.
    unfold rpP, Wpol, xfsum. cbn [combine map fold_right fst snd].
    rewrite to_F_sub, !to_F_add, to_F_mul, to_F_xfint, to_F_proj, ?to_F_zero, !to_F_dot, !Wpol_nth.
    rewrite to_F_rho_r, !to_F_rho_e. unfold wdot, Bgv.rho_e1, Bgv.rho_e2. field.
  Qed.

  Lemma to_F_bx_nat : forall n, to_F (bx (Z.of_nat n)) = nF2 n.
  Proof. intro n. rewrite <-to_F_bx_zm. exact (to_F_xint_nat n). Qed.

  Lemma hhP_F : forall ru rv al be j, wshape -> (j < tau)%nat ->
    to_F (nth j (hhPx ru rv al be) xzero)
    = fsub (fadd (@proj F fzero fadd fmul (map to_F ru) (map to_F rv) (ctxF (nth j (cinX cout) ([], []))))
                 (fmul (to_F be) (to_F (bx (nth j sig 0%Z))))) (to_F al).
  Proof.
    intros ru rv al be j (hs & hc & _) hj. unfold hhP.
    rewrite (nth_combine_map _ _ _ j xzero 0%Z xzero)
      by (unfold zhatP, sigZ, cinX; rewrite ?length_map; lia).
    cbn [fst snd]. unfold zhatP, sigZ.
    rewrite (nth_indep _ xzero (xproj ru rv ([], []))) by (unfold cinX; rewrite !length_map; lia).
    rewrite map_nth. rewrite (nth_indep _ 0%Z (zm 0%Z)) by (rewrite length_map; lia). rewrite map_nth.
    rewrite to_F_sub, to_F_add, to_F_mul, to_F_proj, to_F_bx_zm. reflexivity.
  Qed.

  (* hhat_j = h_(sigma j): the shuffle relation, projected *)
  Theorem hh_eq_h : forall ru rv al be, valid -> wshape -> List.length cin = tau ->
    List.length ru = N -> List.length rv = N -> forall j, (j < tau)%nat ->
    to_F (nth j (hhPx ru rv al be) xzero) = to_F (nth (nth j sigma 0%nat) (hPx ru rv al be) xzero).
  Proof.
    intros ru rv al be [hs hR] hw hci hu hv j hj.
    destruct hR as (_ & _ & _ & hperm & _ & hout).
    assert (hsj : (nth j sigma 0%nat < tau)%nat).
    { assert (hl : List.length sigma = tau) by (rewrite (Permutation_length hperm), length_seq; reflexivity).
      pose proof (Permutation_in _ hperm (nth_In sigma 0%nat (eq_ind_r (fun x => (j < x)%nat) hj hl))) as hin.
      apply in_seq in hin. lia. }
    rewrite (hhP_F ru rv al be j hw hj), (hP_F ru rv al be (nth j sigma 0%nat) hci hsj).
    specialize (hout j hj). rewrite !nth_ctxF in hout. rewrite hout.
    rewrite (wsF_nth _ hsj).
    rewrite (@proj_rerand Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field)
      by (rewrite !length_map, (w_len hw wr _ ltac:(cbn; tauto) hsj); lia).
    rewrite hs. change (nth j (map Z.of_nat sigma) 0%Z) with (nth j (map Z.of_nat sigma) (Z.of_nat 0)).
    rewrite (map_nth Z.of_nat sigma 0%nat j), to_F_bx_nat. field.
  Qed.

  Lemma hP_length : forall ru rv al be, List.length (hPx ru rv al be) = tau.
  Proof. intros. unfold hP. cbv zeta. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma hhP_length : forall ru rv al be, wshape -> List.length (hhPx ru rv al be) = tau.
  Proof.
    intros ru rv al be (hs & hc & _). unfold hhP, zhatP, sigZ, cinX.
    rewrite length_map, length_combine, !length_map. lia.
  Qed.

  (* sumcheck A starts from its true sum *)
  Theorem sumA : forall ru rv al be tc kA, valid -> wshape -> List.length cin = tau ->
    List.length ru = N -> List.length rv = N -> List.length tc = ell ->
    existsb (fun x => negb (xnz x)) (hPx ru rv al be ++ hhPx ru rv al be) = false ->
    csum (map sF (termsA kA)) (tF (tablesAx ru rv al be tc)) tau
    = fadd (to_F (nth 0 kA xzero)) (to_F (nth 1 kA xzero)).
  Proof.
    intros ru rv al be tc kA hv hw hci hu hrv htc hnz.
    pose proof (hP_length ru rv al be) as hlh. pose proof (hhP_length ru rv al be hw) as hlhh.
    set (H := fun i => to_F (nth i (hPx ru rv al be) xzero)).
    assert (hH : forall i, (i < tau)%nat -> H i <> fzero).
    { intros i hi. unfold H. rewrite <-(app_nth1 _ (hhPx ru rv al be)) by lia.
      apply (xnz_all _ hnz). rewrite length_app. lia. }
    assert (hperm : Permutation sigma (seq 0 tau)) by (destruct hv as (_ & _ & _ & _ & hp & _); exact hp).
    assert (hsj : forall j, (j < tau)%nat -> (nth j sigma 0%nat < tau)%nat).
    { intros j hj. assert (hl : List.length sigma = tau) by (rewrite (Permutation_length hperm), length_seq; reflexivity).
      pose proof (Permutation_in _ hperm (nth_In sigma 0%nat (eq_ind_r (fun x => (j < x)%nat) hj hl))) as hin.
      apply in_seq in hin. lia. }
    assert (hHH : forall j, (j < tau)%nat -> to_F (nth j (hhPx ru rv al be) xzero) = H (nth j sigma 0%nat)).
    { intros j hj. unfold H. apply hh_eq_h; assumption. }
    set (c01 := fadd (to_F (nth 0 kA xzero)) (to_F (nth 1 kA xzero))).
    set (E := fun i => nth i (map to_F (xeq_table tc)) fzero).
    unfold csum.
    rewrite (fsum_seq_ext _ (fun i => fadd (fmul c01 (E i))
                                           (fsub (fmul (to_F (nth 2 kA xzero)) (finv (H i)))
                                                 (fmul (to_F (nth 2 kA xzero)) (finv (H (nth i sigma 0%nat))))))).
    2: { intros i hi.
         unfold tablesA, tF, colF, termsA, termsF, termF, sF, uP, uhP. cbn [map fold_left fst snd LogDer.fsum].
         rewrite !nth_inv_F by lia. rewrite <-!to_F_nth, (hHH i hi). fold (H i). fold (E i).
         rewrite to_F_neg. unfold c01. pose proof (hH i hi). pose proof (hH _ (hsj i hi)).
         cbn [nth]. unfold E. rewrite <-to_F_nth. field. auto. }
    rewrite <-ExecFold.fsum_map_add.
    rewrite (@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (@LogDer.fsum_map_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite !(@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (fsum_sigma (fun i => finv (H i)) sigma tau hperm).
    unfold E. rewrite <-htc, eq_table_sum. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* sumcheck C *)

  Lemma Wk_length : wshape -> forall t, In t [wr; we1; we2] -> List.length (List.concat (map (map zm) t)) = (2 ^ m)%nat.
  Proof.
    intros (hs & hc & hw) t hin. rewrite Forall_forall in hw. destruct (hw t hin) as [h1 h2].
    rewrite (length_concat_uniform _ N), length_map, h1.
    - rewrite Nat.pow_add_r. lia.
    - intros l hl. apply in_map_iff in hl. destruct hl as (p & <- & hp). rewrite length_map.
      rewrite Forall_forall in h2. apply h2, hp.
  Qed.

  Local Notation tern2 := (@tern Fq2 fzero fone fopp).

  Lemma tern_rows : valid -> wshape -> forall t, In t [wr; we1; we2] ->
    Forall (fun z => tern2 (to_F (bx z))) (List.concat (map (map zm) t)).
  Proof.
    intros [_ hR] (hs & hc & hw) t hin. destruct hR as (_ & _ & _ & _ & hws & _).
    apply Forall_concat. apply Forall_map. apply Forall_forall. intros p hp.
    rewrite Forall_forall in hw. destruct (hw t hin) as [h1 _].
    destruct (In_nth t p [] hp) as (i & hi & <-). rewrite h1 in hi.
    assert (hin' : In (nth i wsF ([], [], [])) wsF) by (apply nth_In; unfold wsF; rewrite length_map, length_seq; exact hi).
    rewrite (wsF_nth i hi) in hin'.
    destruct (hws _ _ _ hin') as (_ & _ & _ & t1 & t2 & t3).
    assert (ht : Forall tern2 (map to_F (map bx (nth i t [])))).
    { cbn in hin. destruct hin as [<- | [<- | [<- | []]]]; assumption. }
    apply Forall_map. rewrite !Forall_map in ht. eapply Forall_impl; [| exact ht].
    intros z hz. cbv beta in *. rewrite to_F_bx_zm. exact hz.
  Qed.

  Lemma cube_of_tern : forall x, tern2 x -> fmul (fmul x x) x = x.
  Proof. intros x h. exact (proj2 (@cube_ternary Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field x) h). Qed.

  (* sumcheck C starts from its true sum: 0 *)
  Theorem sumC : forall tz kC, valid -> wshape ->
    csum (map sF (termsC kC)) (tF (tablesC wr we1 we2 tz)) (2 ^ m) = fzero.
  Proof.
    intros tz kC hv hw.
    assert (ht : forall t i, In t [wr; we1; we2] -> (i < 2 ^ m)%nat ->
              fmul (fmul (nth i (map to_F (map bx (List.concat (map (map zm) t)))) fzero)
                         (nth i (map to_F (map bx (List.concat (map (map zm) t)))) fzero))
                   (nth i (map to_F (map bx (List.concat (map (map zm) t)))) fzero)
              = nth i (map to_F (map bx (List.concat (map (map zm) t)))) fzero).
    { intros t i hin hi. apply cube_of_tern. rewrite nth_row_F.
      pose proof (tern_rows hv hw t hin) as h. rewrite Forall_forall in h. apply h, nth_In.
      rewrite (Wk_length hw t hin). exact hi. }
    unfold csum. rewrite (fsum_seq_ext _ (fun _ => fzero)).
    + apply (@fsum_map_zero Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    + intros i hi. unfold tablesC, Wk, Wpol, tF, colF, termsC, termsF, termF, sF.
      cbn [map fold_left fst snd LogDer.fsum nth].
      rewrite !to_F_neg.
      pose proof (ht wr i ltac:(cbn; tauto) hi) as e1. pose proof (ht we1 i ltac:(cbn; tauto) hi) as e2.
      pose proof (ht we2 i ltac:(cbn; tauto) hi) as e3.
      set (w1 := nth i (map to_F (map bx (List.concat (map (map zm) wr)))) fzero) in *.
      set (w2 := nth i (map to_F (map bx (List.concat (map (map zm) we1)))) fzero) in *.
      set (w3 := nth i (map to_F (map bx (List.concat (map (map zm) we2)))) fzero) in *.
      set (E := nth i (map to_F (xeq_table tz)) fzero).
      set (c0 := to_F (nth 0 kC xzero)). set (c1 := to_F (nth 1 kC xzero)). set (c2 := to_F (nth 2 kC xzero)).
      transitivity (fadd (fmul (fmul c0 E) (fsub (fmul (fmul w1 w1) w1) w1))
                     (fadd (fmul (fmul c1 E) (fsub (fmul (fmul w2 w2) w2) w2))
                           (fmul (fmul c2 E) (fsub (fmul (fmul w3 w3) w3) w3)))); [field |].
      rewrite e1, e2, e3. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* sumcheck B *)

  Local Notation tablesBx := (tablesB n1 pplain a b wr we1 we2 k).

  (* sum over the coefficients of rho'_p times the folded witness table *)
  Lemma sum_RW : forall (rp : list xf) (w : list (list Z)) (rA : list xf),
    List.length rp = N -> List.length w = tau -> List.length rA = ell ->
    fsum (map (fun y => fmul (nth y (map to_F rp) fzero)
                             (nth y (map to_F (fold_right xpadd []
                                     (map (fun p => xpscale (fst p) (map bx (snd p)))
                                          (combine (xeq_table rA) (map (map zm) w))))) fzero)) (seq 0 N))
    = fsum (map (fun i => fmul (nth i (map to_F (xeq_table rA)) fzero)
                               (dot (map to_F rp) (map to_F (map bx (nth i w []))))) (seq 0 tau)).
  Proof.
    intros rp w rA hrp hw hrA.
    assert (hle : List.length (xeq_table rA) = tau) by (rewrite xeq_table_length, hrA; reflexivity).
    rewrite (fsum_seq_ext _ (fun y => fsum (map (fun i => fmul (nth y (map to_F rp) fzero)
                 (fmul (nth i (map to_F (xeq_table rA)) fzero) (nth y (map to_F (map bx (nth i w []))) fzero))) (seq 0 tau)))).
    2: { intros y hy. rewrite nth_comb_rows.
         rewrite (fsum_combine _ _ _ xzero []) by (rewrite length_map; lia). rewrite hle.
         rewrite <-(@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). apply fsum_seq_ext.
         intros i hi. cbn [fst snd]. rewrite to_F_nth, <-nth_row_F, Wpol_nth. reflexivity. }
    rewrite (@fsum_swap Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    apply fsum_seq_ext. intros i hi.
    rewrite dot_len, length_map, hrp.
    rewrite <-(@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). apply fsum_seq_ext.
    intros y hy. field.
  Qed.

  Lemma zpub_F : forall ru rv i, List.length cin = tau -> (i < tau)%nat ->
    to_F (nth i (zpubP cin ru rv) xzero) = @proj F fzero fadd fmul (map to_F ru) (map to_F rv) (ctxF (nth i (cinX cin) ([], []))).
  Proof.
    intros ru rv i hci hi. unfold zpubP.
    rewrite (nth_indep _ xzero (xproj ru rv ([], []))) by (unfold cinX; rewrite !length_map; lia).
    rewrite map_nth. apply to_F_proj.
  Qed.

  Lemma rpP_lengths : forall ru rv, List.length a = N -> List.length b = N -> (1 <= n1)%nat ->
    List.length ru = N -> List.length rv = N -> Forall (fun p => List.length p = N) (rpP pplain a b ru rv).
  Proof.
    intros ru rv ha hb hn hu hv.
    assert (hpos : (0 < N)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    unfold rpP, xrho_r, xrho_e, xpscale. repeat constructor.
    + rewrite xpadd_length, !xnadj_length, hu, hv; [lia | |]; unfold aX; destruct b, a; cbn in *; try discriminate; lia.
    + rewrite length_map. exact hu.
    + rewrite length_map. exact hv.
  Qed.

  (* sumcheck B starts from its true sum *)
  Theorem sumB : forall ru rv al be rA, wshape -> stmt_ok ->
    List.length ru = N -> List.length rv = N -> List.length rA = ell ->
    csum (map sF termsB) (tF (tablesBx ru rv rA)) N
    = fadd (fsub (fsub (fadd (to_F (xmle (hPx ru rv al be) rA)) (fmul (to_F (a_h k)) (to_F (xzval rA))))
                       (to_F (xmle (zpubP cin ru rv) rA)))
                 (fmul (to_F be) (@idr Fq2 fzero fone fadd fmul (map to_F rA))))
           (to_F al).
  Proof.
    intros ru rv al be rA hw (ha & hb & hci & hn & hl & hQ) hu hv hrA.
    pose proof (rpP_lengths ru rv ha hb hn hu hv) as hrp.
    unfold rpP in hrp. repeat rewrite Forall_cons_iff in hrp. destruct hrp as (l1 & l2 & l3 & _).
    assert (hlw : forall w, In w [wr; we1; we2] -> List.length w = tau).
    { intros w hin. destruct hw as (_ & _ & hw'). rewrite Forall_forall in hw'. exact (proj1 (hw' w hin)). }
    set (cst := cstP n1 k rA).
    set (e := fun i => nth i (map to_F (xeq_table rA)) fzero).
    set (D := fun (rp : list xf) (w : list (list Z)) i => dot (map to_F rp) (map to_F (map bx (nth i w [])))).
    set (rp1 := xrho_r (aX a) (aX b) ru rv). set (rp2 := xrho_e (bx pplain) ru). set (rp3 := xrho_e (bx pplain) rv).
    unfold csum.
    (* the summand, entry by entry *)
    rewrite (fsum_seq_ext _
      (fun y => fadd (fadd (fadd
         (fmul (nth y (map to_F rp1) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) wr))))) fzero))
         (fmul (nth y (map to_F rp2) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) we1))))) fzero)))
         (fmul (nth y (map to_F rp3) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) we2))))) fzero)))
         (to_F cst))).
    2: { intros y hy. unfold tablesB, rpP, WpP, Wpol, tF, colF, termsB, termsF, termF, sF.
         cbn [map app fold_left fst snd LogDer.fsum nth]. rewrite to_F_one.
         replace (nth y (map to_F (repeat (cstP n1 k rA) N)) fzero) with (to_F cst)
           by (rewrite map_repeat, (nth_indep _ fzero (to_F cst)) by (rewrite repeat_length; exact hy);
               rewrite nth_repeat; reflexivity).
         fold rp1 rp2 rp3. field. }
    rewrite <-!ExecFold.fsum_map_add.
    rewrite (MixIdentities.fsum_const (Hf := Fq2_field)), length_seq.
    rewrite !sum_RW by (first [assumption | apply hlw; cbn; tauto]).
    rewrite !ExecFold.fsum_map_add.
    (* the folded witness, through h *)
    rewrite (fsum_seq_ext _ (fun i => fsub (fsub (fadd (fsub (fmul (e i) (to_F (nth i (hPx ru rv al be) xzero)))
                                                                (fmul (e i) (to_F (nth i (zpubP cin ru rv) xzero))))
                                                          (fmul (e i) (to_F al)))
                                                    (fmul (to_F be) (fmul (e i) (nF2 i)))) fzero)).
    2: { intros i hi. rewrite (hP_F ru rv al be i hci hi), (zpub_F ru rv i hci hi), (wsF_nth i hi).
         unfold wdot, e. fold rp1. unfold Bgv.rho_e1, Bgv.rho_e2.
         rewrite <-to_F_rho_r, <-!to_F_pscale. fold rp1. unfold rp2, rp3, xrho_e. field. }
    rewrite !(@LogDer.fsum_map_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite <-!ExecFold.fsum_map_add.
    rewrite !(@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite fsum_map_mul_r.
    rewrite (@LogDer.fsum_map_zero Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    unfold e. rewrite <-hrA. rewrite eq_table_sum, eq_idr_sum.
    rewrite !xmle_sum by (first [unfold hP; cbv zeta; rewrite length_map, length_seq; reflexivity
                                | unfold zpubP, cinX; rewrite !length_map, hrA; exact hci]).
    rewrite (@LogDer.fsum_map_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    (* the constant table *)
    assert (hN : nF2 N <> fzero).
    { apply (Fq2_char_upto (N + tau)); [lia |]. split; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | lia]. }
    unfold cst, cstP. rewrite !to_F_mul, to_F_inv, to_F_xfint. field. exact hN.
  Qed.

  (* the part of sumcheck B without the constant table: the folded witness against rho' *)
  Theorem sumB_core : forall ru rv al be rA, wshape -> stmt_ok ->
    List.length ru = N -> List.length rv = N -> List.length rA = ell ->
    fsum (map (fun y => fadd (fadd
         (fmul (nth y (map to_F (xrho_r (aX a) (aX b) ru rv)) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) wr))))) fzero))
         (fmul (nth y (map to_F (xrho_e (bx pplain) ru)) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) we1))))) fzero)))
         (fmul (nth y (map to_F (xrho_e (bx pplain) rv)) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) we2))))) fzero)))
       (seq 0 N))
    = fadd (fsub (fsub (to_F (xmle (hPx ru rv al be) rA)) (to_F (xmle (zpubP cin ru rv) rA)))
                 (fmul (to_F be) (@idr Fq2 fzero fone fadd fmul (map to_F rA))))
           (to_F al).
  Proof.
    intros ru rv al be rA hw (ha & hb & hci & hn & hl & hQ) hu hv hrA.
    pose proof (rpP_lengths ru rv ha hb hn hu hv) as hrp.
    unfold rpP in hrp. repeat rewrite Forall_cons_iff in hrp. destruct hrp as (l1 & l2 & l3 & _).
    assert (hlw : forall w, In w [wr; we1; we2] -> List.length w = tau).
    { intros w hin. destruct hw as (_ & _ & hw'). rewrite Forall_forall in hw'. exact (proj1 (hw' w hin)). }
    set (e := fun i => nth i (map to_F (xeq_table rA)) fzero).
    set (rp1 := xrho_r (aX a) (aX b) ru rv). set (rp2 := xrho_e (bx pplain) ru). set (rp3 := xrho_e (bx pplain) rv).
    rewrite <-!ExecFold.fsum_map_add.
    rewrite !sum_RW by (first [assumption | apply hlw; cbn; tauto]).
    rewrite !ExecFold.fsum_map_add.
    rewrite (fsum_seq_ext _ (fun i => fsub (fsub (fadd (fsub (fmul (e i) (to_F (nth i (hPx ru rv al be) xzero)))
                                                                (fmul (e i) (to_F (nth i (zpubP cin ru rv) xzero))))
                                                          (fmul (e i) (to_F al)))
                                                    (fmul (to_F be) (fmul (e i) (nF2 i)))) fzero)).
    2: { intros i hi. rewrite (hP_F ru rv al be i hci hi), (zpub_F ru rv i hci hi), (wsF_nth i hi).
         unfold wdot, e. fold rp1. unfold Bgv.rho_e1, Bgv.rho_e2.
         rewrite <-to_F_rho_r, <-!to_F_pscale. fold rp1. unfold rp2, rp3, xrho_e. field. }
    rewrite !(@LogDer.fsum_map_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite <-!ExecFold.fsum_map_add.
    rewrite !(@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite fsum_map_mul_r.
    rewrite (@LogDer.fsum_map_zero Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    unfold e. rewrite <-hrA. rewrite eq_table_sum, eq_idr_sum.
    rewrite !xmle_sum by (first [unfold hP; cbv zeta; rewrite length_map, length_seq; reflexivity
                                | unfold zpubP, cinX; rewrite !length_map, hrA; exact hci]).
    rewrite (@LogDer.fsum_map_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    field.
  Qed.

End Back.
