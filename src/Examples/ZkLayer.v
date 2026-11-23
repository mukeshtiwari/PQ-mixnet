(* Zero knowledge, step Z3: the sumcheck layer of the shuffle proof with the
   honest prover instantiated (paper, Theorem 5.3, steps (1) to (3)).

   ZkTranscript.layer_zk takes the honest prover through hypotheses: the
   unmasked summands fA, fB, fC, coefficient lists pfA, pfB, pfC of their
   round functions, and the verifier's unmasked claims cA, cB, cC equal to
   the true sums. Here they are given for the shuffle proof, at GF(q^2):

     tables     those of the extracted prover (ExecProve.v: u, uhat, sigma,
                h, zhat, rho', W), read as functions on the cube (tabOf);
     specs      the seven masked evaluations u*(r), uhat*(r), s*(r), h*(r),
                w_k*(r_z) (the mask coefficients avs are the first seven
                entries of the mask table);
     fA, fB, fC the summands gA, gB, gC of MixSummands.v without the mask
                term (rho = 0, empty masks);
     pfX        the Lagrange interpolants of the round functions at
                0 .. d (certA, certB, certC give the degree bounds);
     cA, cB, cC kA0 + kA1;  H*(r) - zpub(r) - beta idx(r) + alpha;  0.

   Theorem mix_layer_zk: for a valid witness and good challenges, the
   honest transcripts of the layer over all prover coins are a permutation
   of the simulated transcripts over all simulator coins. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex Sumcheck SumcheckMask MaskedExt PolyFun MixSummands Interp ZkBlocks ZkSumcheck ZkMix ZkTranscript LayoutLemmas RowLayout MixBridge. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecDerive ExecVerify ExecProveBase ExecFold ExecDec ExecProve ExecRows ExecBack ExecBackD ExecBackO.
Import ListNotations.

Add Field fieldF2z : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation fsum := (@LogDer.fsum Fq2 fzero fadd).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation cube2 := (@cube Fq2 fzero fone).
Local Notation mstar2 := (@mstar Fq2 fzero fone fadd fmul fsub).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation tsum2 := (fun g => @tsum Fq2 fzero fone fadd g).
Local Notation rnd2 := (fun g => @rnd Fq2 fzero fone fadd g).
Local Notation nF2 := (@nF Fq2 fzero fone fadd).
Local Notation lagr2 := (@lagr Fq2 fzero fone fadd fmul fsub fopp finv).
Local Notation tabOf := ExecPublic.tabOf.

(* sums over the cube as sums over indices *)
Lemma tsum_seq : forall (g : list F -> F) k, tsum2 g [] k = fsum (map (fun i => g (pt2 k i)) (seq 0 (2 ^ k))).
Proof.
  intros g k. cbv beta. unfold Sumcheck.tsum. cbn [app].
  apply (@cube_sum_seq Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field k g).
Qed.

Lemma tab_cube : forall k (l : list xf) (a : F) i, (1 <= k)%nat -> (i < 2 ^ k)%nat ->
  mstar2 k (tabOf (map to_F l)) a (pt2 k i) = to_F (nth i l xzero).
Proof.
  intros k l a i hk hi.
  rewrite (@mstar_cube_pos Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field) by (try exact hk; apply pt_cube).
  rewrite tabOf_pt by exact hi. rewrite to_F_nth. reflexivity.
Qed.

Lemma mle_tab_cube : forall k (l : list xf) i, (i < 2 ^ k)%nat ->
  mle2 k (tabOf (map to_F l)) (pt2 k i) = to_F (nth i l xzero).
Proof.
  intros k l i hi. rewrite (@mle_cube Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field) by apply pt_cube.
  rewrite tabOf_pt by exact hi. rewrite to_F_nth. reflexivity.
Qed.

Lemma eqp_table_pt : forall (tc : list xf) i, (i < 2 ^ List.length tc)%nat ->
  eqp2 (pt2 (List.length tc) i) (map to_F tc) = nth i (map to_F (xeq_table tc)) fzero.
Proof.
  intros tc i hi. rewrite to_F_eq_table. unfold RowLayout.eqvec. rewrite nth_map_seq_F by exact hi. reflexivity.
Qed.

Section Layer.

  Variables n1 ell lo1 lo2 : nat.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable sigma : list nat.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.

  (* the fixed challenges *)
  Variables ru rv : list xf.
  Variables al be : xf.
  Variables tc kA : list xf.
  Variables rhoA rhoB rhoC : xf.
  Variables rA ry tz kC rz : list xf.

  Local Notation hPx := (hP ell pplain a b cin wr we1 we2 ru rv al be).
  Local Notation hhPx := (hhP cout sig ru rv al be).
  Local Notation uPx := (uP ell pplain a b cin wr we1 we2 ru rv al be).
  Local Notation uhPx := (uhP cout sig ru rv al be).
  Local Notation validx := (valid n1 ell pplain a b cin cout sig wr we1 we2 sigma).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).

  (* the tables *)
  Definition TU : list F -> F := tabOf (map to_F uPx).
  Definition TUh : list F -> F := tabOf (map to_F uhPx).
  Definition TS : list F -> F := tabOf (map to_F (map bx (sigZ sig))).
  Definition TH : list F -> F := tabOf (map to_F hPx).
  Definition TZh : list F -> F := tabOf (map to_F (zhatP cout ru rv)).
  Definition TW (k : nat) : list F -> F := tabOf (map to_F (map bx (nth k (Wk wr we1 we2) []))).
  Definition TRP (k : nat) : list F -> F := tabOf (map to_F (nth k (rpP pplain a b ru rv) [])).

  Local Notation rAF := (map to_F rA).
  Local Notation rzF := (map to_F rz).
  Local Notation kk := (fun (l : list xf) i => to_F (nth i l xzero)).

  Definition specsL : list (@evspec F) :=
    [(ell, TU, rAF); (ell, TUh, rAF); (ell, TS, rAF); (ell, TH, rAF); (m, TW 0, rzF); (m, TW 1, rzF); (m, TW 2, rzF)].

  Local Notation av := (fun (avs : list F) i => nth i avs fzero).

  (* the unmasked summands *)
  Definition fA (avs : list F) : list F -> F :=
    @MixSummands.gA Fq2 fzero fone fadd fmul fsub ell TU TUh TS TH TZh (av avs 0) (av avs 1) (av avs 2) (av avs 3)
        (to_F al) (to_F be) (map to_F tc) (kk kA 0) (kk kA 1) (kk kA 2) fzero fzero (repeat [] ell).

  Definition cBv (avs : list F) : F := fmul (fmul (av avs 3) (Zp2 rAF)) (finv (nF2 N)).

  Definition fB (avs : list F) : list F -> F :=
    @MixSummands.gB Fq2 fzero fone fadd fmul fsub n1 ell (TRP 0) (TRP 1) (TRP 2) (TW 0) (TW 1) (TW 2) rAF
        (cBv avs) fzero fzero (repeat [] n1).

  Definition fC (avs : list F) : list F -> F :=
    @MixSummands.gC Fq2 fzero fone fadd fmul fsub m (TW 0) (TW 1) (TW 2) (av avs 4) (av avs 5) (av avs 6)
        (map to_F tz) (kk kC 0) (kk kC 1) (kk kC 2) fzero fzero (repeat [] m).

  (* the verifier's unmasked claims, from the masked evaluations ys *)
  Definition cA (ys : list F) : F := fadd (kk kA 0) (kk kA 1).
  Definition cB (ys : list F) : F :=
    fadd (fsub (fsub (nth 3 ys fzero) (to_F (xmle (zpubP cin ru rv) rA))) (fmul (to_F be) (@idr Fq2 fzero fone fadd fmul rAF)))
         (to_F al).
  Definition cC (ys : list F) : F := fzero.

  (* ------------------------------------------------------------------ *)
  (* the true sums *)

  Theorem HcA_true : validx -> wshape -> stmt_ok n1 ell a b cin -> List.length ru = N -> List.length rv = N ->
    List.length tc = ell -> List.length kA = 3%nat ->
    existsb (fun x => negb (xnz x)) (hPx ++ hhPx) = false ->
    forall avs, tsum2 (fA avs) [] ell = cA (@evs Fq2 fzero fone fadd fmul fsub specsL avs).
  Proof.
    intros hv hw hs hu hrv htc hkA hnz avs. pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    rewrite tsum_seq. unfold cA.
    rewrite <-(sumA n1 ell pplain a b cin cout sig wr we1 we2 sigma ru rv al be tc kA hv hw hci hu hrv htc hnz).
    unfold csum. apply fsum_seq_ext. intros i hi.
    unfold fA, MixSummands.gA, ustar, uhstar, sgstar, hstar, hhstar, TU, TUh, TS, TH, TZh.
    rewrite !tab_cube by lia.
    rewrite (@mle_tab_cube ell (zhatP cout ru rv) i hi).
    rewrite <-htc, eqp_table_pt by (rewrite htc; exact hi). rewrite htc.
    unfold tablesA, tF, colF, termsA, termsF, termF, sF. cbn [map fold_left fst snd LogDer.fsum nth].
    rewrite <-!to_F_nth, to_F_neg.
    rewrite (hhP_entry n1 ell cout sig wr we1 we2 hw ru rv al be i hi). field.
  Qed.


  (* the witness table at (y, r): the folded table of the prover *)
  Lemma W_mle : wshape -> forall w y, In w [wr; we1; we2] -> (y < N)%nat -> List.length rA = ell ->
    mle2 m (tabOf (map to_F (map bx (List.concat (map (map zm) w))))) (pt2 n1 y ++ rAF)
    = nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p)))
                                                  (combine (xeq_table rA) (map (map zm) w))))) fzero.
  Proof.
    intros hw w y hin hy hrA.
    destruct hw as (_ & _ & hw'). rewrite Forall_forall in hw'. destruct (hw' w hin) as [hlw hlp].
    rewrite Forall_forall in hlp.
    assert (hlq : forall l, In l (map (map zm) w) -> List.length l = N).
    { intros l hl. apply in_map_iff in hl. destruct hl as (q & <- & hq). rewrite length_map. apply hlp, hq. }
    rewrite (@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell _ (pt2 n1 y) rAF)
      by apply (@pt_length Fq2 fzero fone).
    rewrite (@mle_cube Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field) by apply pt_cube.
    rewrite (mle_list ell _ (map (fun i => bx (nth y (nth i (map (map zm) w) []) 0%Z)) (seq 0 tau)) rA);
      [| rewrite length_map, length_seq; reflexivity | exact hrA |].
    - rewrite xmle_sum by (rewrite length_map, length_seq, hrA; reflexivity).
      rewrite nth_comb_rows.
      rewrite (fsum_combine _ _ _ xzero []) by (rewrite xeq_table_length, length_map, hlw, hrA; reflexivity).
      rewrite xeq_table_length, hrA. apply fsum_seq_ext. intros i hi. cbn [fst snd].
      rewrite (nth_map_seq_any _ tau i xzero hi), to_F_nth. reflexivity.
    - intros i hi. rewrite <-pt_split by exact hy.
      rewrite tabOf_pt by (rewrite Nat.pow_add_r; nia).
      rewrite nth_row_F, (nth_map_seq_any _ tau i xzero hi).
      rewrite (nth_concat_uniform _ N i y hlq hy) by (rewrite length_map; lia). reflexivity.
  Qed.

  Lemma TW_concat : forall k, (k < 3)%nat ->
    TW k = tabOf (map to_F (map bx (List.concat (map (map zm) (nth k [wr; we1; we2] []))))).
  Proof. intros k hk. destruct k as [| [| [| k]]]; try lia; reflexivity. Qed.

  Theorem HcB_true : wshape -> stmt_ok n1 ell a b cin -> List.length ru = N -> List.length rv = N ->
    List.length rA = ell ->
    forall avs, List.length avs = List.length specsL ->
      tsum2 (fB avs) [] n1 = cB (@evs Fq2 fzero fone fadd fmul fsub specsL avs).
  Proof.
    intros hw hs hu hrv hrA avs hl. pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    pose proof (rpP_lengths n1 pplain a b ru rv ha hb hn1 hu hrv) as hrp. unfold rpP in hrp.
    repeat rewrite Forall_cons_iff in hrp. destruct hrp as (l1 & l2 & l3 & _).
    rewrite tsum_seq. unfold fB, MixSummands.gB.
    rewrite (fsum_seq_ext _ (fun y => fadd (fadd (fadd
         (fmul (nth y (map to_F (xrho_r (aX a) (aX b) ru rv)) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) wr))))) fzero))
         (fmul (nth y (map to_F (xrho_e (bx pplain) ru)) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) we1))))) fzero)))
         (fmul (nth y (map to_F (xrho_e (bx pplain) rv)) fzero) (nth y (map to_F (fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) (map (map zm) we2))))) fzero)))
         (cBv avs))).
    2: { intros y hy. unfold TRP. rewrite !(@mle_tab_cube n1 _ y hy), <-!to_F_nth.
         rewrite !TW_concat by lia. cbn [nth].
         rewrite !(W_mle hw) by (first [exact hy | exact hrA | cbn; tauto]).
         unfold rpP. cbn [nth]. rewrite <-!to_F_nth. unfold SumcheckMask.gmask. field. }
    rewrite <-ExecFold.fsum_map_add. rewrite (MixIdentities.fsum_const (Hf := Fq2_field)), length_seq.
    rewrite (sumB_core n1 ell pplain a b cin cout sig wr we1 we2 ru rv al be rA hw hs hu hrv hrA).
    unfold cB.
    do 7 (destruct avs as [| ? avs]; [cbn in hl; lia |]).
    cbn [evs nth specsL]. unfold ev. cbn [fst snd]. unfold MaskedExt.mstar, TH.
    replace (mle2 ell (tabOf (map to_F hPx)) rAF) with (to_F (xmle hPx rA))
      by (rewrite to_F_mle, hrA; [reflexivity | rewrite hrA; unfold hP; cbv zeta; rewrite length_map, length_seq; reflexivity]).
    unfold cBv. cbn [nth].
    assert (hN : nF2 N <> fzero).
    { apply (Fq2_char_upto (N + tau)); [lia |]. split; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | lia]. }
    field. exact hN.
  Qed.

  Theorem HcC_true : validx -> wshape -> stmt_ok n1 ell a b cin ->
    forall avs, tsum2 (fC avs) [] m = cC (@evs Fq2 fzero fone fadd fmul fsub specsL avs).
  Proof.
    intros hv hw hs avs. pose proof hs as (ha & hb & hci & hn1 & hl1 & hQ).
    rewrite tsum_seq. unfold cC. apply (@fsum_map_zero_ext Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    intros i hi. apply in_seq in hi.
    assert (hc : forall k, (k < 3)%nat -> forall x, @MixSummands.cube3 Fq2 fmul fsub (mstar2 m (TW k) x (pt2 m i)) = fzero).
    { intros k hk x. rewrite TW_concat by exact hk. rewrite tab_cube by lia.
      unfold cube3. rewrite cube_of_tern; [field |].
      change xzero with (bx 0%Z). rewrite map_nth.
      pose proof (tern_rows n1 ell pplain a b cin cout sig wr we1 we2 sigma hv hw (nth k [wr; we1; we2] []))
        as ht. rewrite Forall_forall in ht. apply ht.
      - apply nth_In. cbn. lia.
      - apply nth_In. rewrite (Wk_length n1 ell cout sig wr we1 we2 hw) by (apply nth_In; cbn; lia). lia. }
    unfold fC, MixSummands.gC, wstar1, wstar2, wstar3. rewrite !hc by lia. unfold SumcheckMask.gmask. field.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the round functions as coefficient lists *)

  Local Notation dgA := (MixSummands.degA ell).
  Local Notation dgC := (MixSummands.degC m).
  Definition dgB (i : nat) : nat := 2%nat.

  Definition rvals (f : list F -> F) (mm d : nat) (pre : list F) : list F :=
    map (fun i => rnd2 f pre (mm - 1 - List.length pre) (nF2 i)) (seq 0 (S d)).

  Definition pfA (avs pre : list F) : list F := lagr2 (rvals (fA avs) ell (dgA (List.length pre)) pre).
  Definition pfB (avs pre : list F) : list F := lagr2 (rvals (fB avs) n1 (dgB (List.length pre)) pre).
  Definition pfC (avs pre : list F) : list F := lagr2 (rvals (fC avs) m (dgC (List.length pre)) pre).

  Lemma char8 : forall k, (0 < k <= 8)%nat -> nF2 k <> fzero.
  Proof. apply Fq2_char_upto. vm_compute. reflexivity. Qed.

  (* a round function with a certificate of degree d <= 7 is the interpolant of its values at 0 .. d *)
  Lemma pf_interp : forall (f : list F -> F) mm d pre X, (d <= 7)%nat -> (List.length pre < mm)%nat ->
    (exists pstar, (List.length pstar <= S d)%nat /\ forall Y, @eval Fq2 fzero fadd fmul pstar Y = rnd2 f pre (mm - 1 - List.length pre) Y) ->
    @eval Fq2 fzero fadd fmul (lagr2 (rvals f mm d pre)) X = rnd2 f pre (mm - 1 - List.length pre) X.
  Proof.
    intros f mm d pre X hd hl (ps & hps & hev).
    rewrite (@lagr_eval Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (@interp_unique Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field 8 char8 _ ps).
    - apply hev.
    - unfold rvals. rewrite length_map, length_seq. lia.
    - unfold rvals. rewrite length_map, length_seq. exact hps.
    - intros k hk. unfold rvals in *. rewrite length_map, length_seq in hk.
      rewrite nth_map_seq_F by exact hk. symmetry. apply hev.
  Qed.

  Lemma rvals_lagr_len : forall f mm d pre, (List.length (tl (lagr2 (rvals f mm d pre))) <= d)%nat.
  Proof.
    intros f mm d pre. pose proof (@lagr_length Fq2 fzero fone fadd fmul fsub fopp finv (rvals f mm d pre)) as h.
    assert (hl : List.length (rvals f mm d pre) = S d) by (unfold rvals; rewrite length_map, length_seq; reflexivity).
    rewrite hl in h. destruct (lagr2 (rvals f mm d pre)); cbn in *; lia.
  Qed.

  Lemma firstn_len : forall (l : list F) j, (j <= List.length l)%nat -> List.length (firstn j l) = j.
  Proof. intros l j h. rewrite length_firstn. lia. Qed.

  Theorem HpfA : List.length rA = ell -> forall avs j X, (j < ell)%nat ->
    @eval Fq2 fzero fadd fmul (pfA avs (firstn j rAF)) X = rnd2 (fA avs) (firstn j rAF) (ell - 1 - j) X.
  Proof.
    intros hr avs j X hj. unfold pfA.
    assert (hfl : List.length (firstn j rAF) = j) by (apply firstn_len; rewrite length_map; lia).
    replace (ell - 1 - j)%nat with (ell - 1 - List.length (firstn j rAF))%nat by (rewrite hfl; reflexivity).
    apply pf_interp; [unfold MixSummands.degA; destruct (Nat.eqb _ _); lia | lia |].
    rewrite hfl.
    destruct (@certA Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field ell TU TUh TS TH TZh
                (nth 0 avs fzero) (nth 1 avs fzero) (nth 2 avs fzero) (nth 3 avs fzero) (to_F al) (to_F be) (map to_F tc)
                (to_F (nth 0 kA xzero)) (to_F (nth 1 kA xzero)) (to_F (nth 2 kA xzero)) fzero fzero (repeat [] ell)
                (repeat_length _ _) ltac:(intros i hi; rewrite nth_repeat; cbn; lia)
                (firstn j rAF) (ell - 1 - j) ltac:(rewrite hfl; lia)) as (ps & h1 & h2).
    exists ps. rewrite hfl in h1. split; [exact h1 | exact h2].
  Qed.

  Theorem HpfB : List.length ry = n1 -> forall avs j X, (j < n1)%nat ->
    @eval Fq2 fzero fadd fmul (pfB avs (firstn j (map to_F ry))) X = rnd2 (fB avs) (firstn j (map to_F ry)) (n1 - 1 - j) X.
  Proof.
    intros hr avs j X hj. unfold pfB.
    assert (hfl : List.length (firstn j (map to_F ry)) = j) by (apply firstn_len; rewrite length_map; lia).
    replace (n1 - 1 - j)%nat with (n1 - 1 - List.length (firstn j (map to_F ry)))%nat by (rewrite hfl; reflexivity).
    apply pf_interp; [unfold dgB; lia | lia |].
    rewrite hfl.
    destruct (@certB Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell (TRP 0) (TRP 1) (TRP 2) (TW 0) (TW 1) (TW 2)
                rAF (cBv avs) fzero fzero (repeat [] n1)
                (repeat_length _ _) ltac:(intros i hi; rewrite nth_repeat; cbn; lia)
                (firstn j (map to_F ry)) (n1 - 1 - j) ltac:(rewrite hfl; lia)) as (ps & h1 & h2).
    exists ps. split; [exact h1 | exact h2].
  Qed.

  Theorem HpfC : List.length rz = m -> forall avs j X, (j < m)%nat ->
    @eval Fq2 fzero fadd fmul (pfC avs (firstn j rzF)) X = rnd2 (fC avs) (firstn j rzF) (m - 1 - j) X.
  Proof.
    intros hr avs j X hj. unfold pfC.
    assert (hfl : List.length (firstn j rzF) = j) by (apply firstn_len; rewrite length_map; lia).
    replace (m - 1 - j)%nat with (m - 1 - List.length (firstn j rzF))%nat by (rewrite hfl; reflexivity).
    apply pf_interp; [unfold MixSummands.degC; destruct (Nat.eqb _ _); lia | lia |].
    rewrite hfl.
    destruct (@certC Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field m (TW 0) (TW 1) (TW 2)
                (nth 4 avs fzero) (nth 5 avs fzero) (nth 6 avs fzero) (map to_F tz)
                (to_F (nth 0 kC xzero)) (to_F (nth 1 kC xzero)) (to_F (nth 2 kC xzero)) fzero fzero (repeat [] m)
                (repeat_length _ _) ltac:(intros i hi; rewrite nth_repeat; cbn; lia)
                (firstn j rzF) (m - 1 - j) ltac:(rewrite hfl; lia)) as (ps & h1 & h2).
    exists ps. rewrite hfl in h1. split; [exact h1 | exact h2].
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the parameters of the masked round messages *)

  Local Notation okp := (@okparams Fq2 fzero).
  Local Notation prm := (@params Fq2 fone fadd fmul).

  Lemma two_nz : fadd fone fone <> fzero.
  Proof. intro e. apply (char8 2); [lia |]. etransitivity; [| exact e]. cbn [LogDer.nF]. field. Qed.

  Lemma ok_params : forall (dg : nat -> nat) mm (pf : list F -> list F) rho (rs : list F),
    List.length rs = mm -> rho <> fzero ->
    (forall pre, (List.length (tl (pf pre)) <= dg (List.length pre))%nat) ->
    okp (map dg (seq 0 mm)) (prm mm pf rho rs).
  Proof.
    intros dg mm pf rho rs hl hr hd. unfold ZkSumcheck.params, ZkSumcheck.okparams.
    assert (h2 : (@two Fq2 fone fadd) <> fzero) by exact two_nz.
    assert (gen : forall s k, (s + k <= mm)%nat ->
              Forall2 (fun d ts => (List.length (fst ts) <= d)%nat /\ snd ts <> fzero) (map dg (seq s k))
                      (map (fun j => (tl (pf (firstn j rs)), fmul rho (@p2 Fq2 fone fadd fmul (mm - 1 - j)))) (seq s k))).
    { intros s k. revert s. induction k as [| k ih]; intros s hk; [constructor |].
      cbn [seq map]. constructor; [| apply ih; lia]. cbn [fst snd]. split.
      + pose proof (hd (firstn s rs)) as h. rewrite length_firstn in h. replace (Nat.min s (List.length rs)) with s in h by lia.
        exact h.
      + apply (@mul_nonzero Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field); [exact hr |].
        apply (@p2_nonzero Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field h2). }
    apply gen. lia.
  Qed.

  Local Notation dsA := (map dgA (seq 0 ell)).
  Local Notation dsB := (map dgB (seq 0 n1)).
  Local Notation dsC := (map dgC (seq 0 m)).
  Local Notation ryF := (map to_F ry).

  (* Theorem 5.3 for the sumcheck layer of the shuffle proof *)
  Theorem mix_layer_zk : validx -> wshape -> stmt_ok n1 ell a b cin ->
    List.length ru = N -> List.length rv = N -> List.length tc = ell -> List.length kA = 3%nat ->
    List.length rA = ell -> List.length ry = n1 -> List.length rz = m ->
    existsb (fun x => negb (xnz x)) (hPx ++ hhPx) = false ->
    @goodspecs Fq2 fzero fone fmul fsub specsL ->
    to_F rhoA <> fzero -> to_F rhoB <> fzero -> to_F rhoC <> fzero ->
    Permutation
      (map (@honL Fq2 fzero fone fadd fmul fsub specsL ell n1 m pfA pfB pfC (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF)
           (@RL Fq2 lf2 specsL dsA dsB dsC))
      (map (@simL Fq2 fzero fone fadd fmul fsub finv (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF cA cB cC)
           (@RL Fq2 lf2 specsL dsA dsB dsC)).
  Proof.
    intros hv hw hs hu hrv htc hkA hrA hry hrz hnz hgood hA hB hC.
    apply (@layer_zk Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field lf2 lf2_NoDup lf2_all specsL hgood
             two_nz ell n1 m fA fB fC pfA pfB pfC (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF dsA dsB dsC).
    - rewrite length_map. exact hrA.
    - rewrite length_map. exact hry.
    - rewrite length_map. exact hrz.
    - rewrite length_map, length_seq. reflexivity.
    - rewrite length_map, length_seq. reflexivity.
    - rewrite length_map, length_seq. reflexivity.
    - intro avs. apply ok_params; [rewrite length_map; exact hrA | exact hA | intro pre; apply rvals_lagr_len].
    - intro avs. apply ok_params; [rewrite length_map; exact hry | exact hB | intro pre; apply rvals_lagr_len].
    - intro avs. apply ok_params; [rewrite length_map; exact hrz | exact hC | intro pre; apply rvals_lagr_len].
    - intros avs j X hj. apply HpfA; assumption.
    - intros avs j X hj. apply HpfB; assumption.
    - intros avs j X hj. apply HpfC; assumption.
    - intros avs _. apply HcA_true; assumption.
    - intros avs hl. apply HcB_true; assumption.
    - intros avs _. apply HcC_true; assumption.
  Qed.

  Definition honLx := @honL Fq2 fzero fone fadd fmul fsub specsL ell n1 m pfA pfB pfC
                        (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF.
  Definition simLx := @simL Fq2 fzero fone fadd fmul fsub finv (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF cA cB cC.
  Definition VwLx := @View Fq2 fzero fone fadd fmul fsub specsL ell n1 m pfA pfB pfC
                       (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF.
  (* a notation, not a definition: a kernel conversion that has to unfold a constant standing for
     this list goes into the enumeration of GF(q^2) (lf2) and takes minutes *)
  Local Notation RLx := (@RL Fq2 lf2 specsL dsA dsB dsC).


  (* the pieces of mix_layer_zk, for the composition with the opening *)
  Theorem mix_layer_parts : validx -> wshape -> stmt_ok n1 ell a b cin ->
    List.length ru = N -> List.length rv = N -> List.length tc = ell -> List.length kA = 3%nat ->
    List.length rA = ell -> List.length ry = n1 -> List.length rz = m ->
    existsb (fun x => negb (xnz x)) (hPx ++ hhPx) = false ->
    @goodspecs Fq2 fzero fone fmul fsub specsL ->
    to_F rhoA <> fzero -> to_F rhoB <> fzero -> to_F rhoC <> fzero ->
    NoDup RLx
    /\ (forall x, In x RLx -> In (VwLx x) RLx)
    /\ (forall x x', In x RLx -> In x' RLx -> VwLx x = VwLx x' -> x = x')
    /\ (forall v, In v RLx -> exists x, In x RLx /\ VwLx x = v)
    /\ (forall x, In x RLx -> honLx x = simLx (VwLx x)).
  Proof.
    intros hv hw hs hu hrv htc hkA hrA hry hrz hnz hgood hA hB hC.
    unfold honLx, simLx, VwLx.
    apply (@layer_parts Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field lf2 lf2_NoDup lf2_all specsL hgood
             two_nz ell n1 m fA fB fC pfA pfB pfC (to_F rhoA) (to_F rhoB) (to_F rhoC) rAF ryF rzF dsA dsB dsC).
    - rewrite length_map. exact hrA.
    - rewrite length_map. exact hry.
    - rewrite length_map. exact hrz.
    - rewrite length_map, length_seq. reflexivity.
    - rewrite length_map, length_seq. reflexivity.
    - rewrite length_map, length_seq. reflexivity.
    - intro avs. apply ok_params; [rewrite length_map; exact hrA | exact hA | intro pre; apply rvals_lagr_len].
    - intro avs. apply ok_params; [rewrite length_map; exact hry | exact hB | intro pre; apply rvals_lagr_len].
    - intro avs. apply ok_params; [rewrite length_map; exact hrz | exact hC | intro pre; apply rvals_lagr_len].
    - intros avs j X hj. apply HpfA; assumption.
    - intros avs j X hj. apply HpfB; assumption.
    - intros avs j X hj. apply HpfC; assumption.
    - intros avs _. apply HcA_true; assumption.
    - intros avs hl. apply HcB_true; assumption.
    - intros avs _. apply HcC_true; assumption.
  Qed.

End Layer.
