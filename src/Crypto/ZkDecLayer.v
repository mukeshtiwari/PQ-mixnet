(* Zero knowledge of the decryption proof, the sumcheck layer (paper,
   Theorem 7.1, zero-knowledge part; the argument of Theorem 5.3).

   ZkTranscript.layer2_zk with the honest prover of dec_proof.py:
     tables      the digit tables dts (m = n1 + ell variables) and the
                 tables stab, etab of the key share and its noise (n1
                 variables);
     specs       the masked evaluations sent: each digit table at r_z (the
                 end point of sumcheck G), stab and etab at r_t (end point
                 of sumcheck T); the mask coefficients avs are the first
                 kd + 2 entries of the mask table;
     fG, fT      the zero-test summands gZ of ZeroTest.v without mask
                 (rho = 0), for phi = rangep base and phi = w^3 - w;
     pfG, pfT    the Lagrange interpolants of their round functions at
                 0 .. d (certZ gives the degree bounds);
     cG, cT      the verifier's unmasked claims, 0: for a witness the true
                 sums are 0 (dec_HcG_true, dec_HcT_true).

   Theorem dec_layer_zk: for a witness and good challenges, the honest
   transcripts of the layer over all prover coins are a permutation of the
   simulated transcripts over all simulator coins. The field needs
   1, .., Nmax non-zero for the interpolation nodes (Hchar). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Sumcheck SumcheckMask MaskedExt PolyFun Interp ZkBlocks ZkSumcheck ZkMix
  ZkTranscript ZeroTest DecSound.
Import ListNotations.

Section DecLayer.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field fieldDL : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation peval := (@eval F zero add mul).
  Local Notation cube := (@cube F zero one).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation rnd := (@rnd F zero one add).
  Local Notation nF := (@nF F zero one add).
  Local Notation lagr := (@lagr F zero one add mul sub opp inv).
  Local Notation gZ := (@gZ F zero one add mul sub).
  Local Notation okparams := (@okparams F zero).
  Local Notation params := (@params F one add mul).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Variables n1 ell base : nat.
  Hypothesis Hn1 : (1 <= n1)%nat.
  Local Notation m := (n1 + ell)%nat.

  (* interpolation nodes 0 .. Nmax are distinct *)
  Local Notation Nmax := (Nat.max (2 * base + 2) 8).
  Hypothesis Hchar : forall k, (0 < k <= Nmax)%nat -> nF k <> zero.

  (* the witness tables *)
  Variable dts : list (list F -> F).
  Variables stab etab : list F -> F.
  Local Notation kd := (length dts).
  Local Notation phiR := (@rangep F zero one add mul opp base).
  Local Notation phi3 := (@phi3 F zero one opp).
  Hypothesis Hdig : forall T, In T dts -> forall b, In b (cube m) -> peval phiR (T b) = zero.
  Hypothesis Htern : forall b, In b (cube n1) -> peval phi3 (stab b) = zero /\ peval phi3 (etab b) = zero.

  (* the fixed challenges *)
  Variables tz kG rz : list F.
  Variables tt kT rt : list F.
  Variables rhoG rhoT : F.
  Hypothesis Hrz : length rz = m.
  Hypothesis Hrt : length rt = n1.

  Definition specsD : list (@evspec F) := map (fun T => (m, T, rz)) dts ++ [(n1, stab, rt); (n1, etab, rt)].

  (* the unmasked summands, given the mask coefficients *)
  Definition fG (avs : list F) : list F -> F := gZ m phiR kG dts (firstn kd avs) tz zero zero (repeat [] m).
  Definition fT (avs : list F) : list F -> F := gZ n1 phi3 kT [stab; etab] (skipn kd avs) tt zero zero (repeat [] n1).

  Definition cGD (ys : list F) : F := zero.
  Definition cTD (ys : list F) : F := zero.

  (* ------------------------------------------------------------------ *)
  (* the true sums are zero *)

  Lemma innerT_zero : forall (phi : list F) b ks Ts, (forall T, In T Ts -> peval phi (T b) = zero) ->
    @innerT F zero add mul phi ks Ts b = zero.
  Proof.
    intros phi b; induction ks as [| k ks ih]; intros Ts h; [reflexivity |].
    destruct Ts as [| T Ts]; [reflexivity |]. cbn [innerT].
    rewrite (h T (or_introl eq_refl)), ih by (intros T' hT'; apply h; right; exact hT'). field.
  Qed.

  Lemma tsum_zero : forall (g : list F -> F) k, (forall b, In b (cube k) -> g b = zero) -> tsum g [] k = zero.
  Proof.
    intros g k h. unfold Sumcheck.tsum. apply (@fsum_map_zero_ext F zero one add mul sub div opp inv Hf).
    intros b hb. cbn [app]. apply h, hb.
  Qed.

  Theorem dec_HcG_true : forall avs, length avs = length specsD -> tsum (fG avs) [] m = cGD (@evs F zero one add mul sub specsD avs).
  Proof.
    intros avs hl. unfold cGD. apply tsum_zero. intros b hb. unfold fG, ZeroTest.gZ.
    assert (hlen : length (firstn kd avs) = kd)
      by (rewrite length_firstn; unfold specsD in hl; rewrite length_app, length_map in hl; cbn in hl; lia).
    rewrite (@inner_cube F zero one add mul sub div opp inv Hf m ltac:(lia) phiR base (@rangep_length F zero one add mul opp base) kG dts (firstn kd avs) b hlen hb).
    rewrite (innerT_zero phiR b kG dts (fun T hT => Hdig T hT b hb)). field.
  Qed.

  Theorem dec_HcT_true : forall avs, length avs = length specsD -> tsum (fT avs) [] n1 = cTD (@evs F zero one add mul sub specsD avs).
  Proof.
    intros avs hl. unfold cTD. apply tsum_zero. intros b hb. unfold fT, ZeroTest.gZ.
    assert (hlen : length (skipn kd avs) = 2%nat)
      by (rewrite length_skipn; unfold specsD in hl; rewrite length_app, length_map in hl; cbn in hl; lia).
    rewrite (@inner_cube F zero one add mul sub div opp inv Hf n1 Hn1 phi3 3 ltac:(reflexivity) kT [stab; etab] (skipn kd avs) b hlen hb).
    rewrite (innerT_zero phi3 b kT [stab; etab]).
    + field.
    + intros T [<- | [<- | []]]; [exact (proj1 (Htern b hb)) | exact (proj2 (Htern b hb))].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the round functions as coefficient lists *)

  Definition rvals (f : list F -> F) (mm d : nat) (pre : list F) : list F :=
    map (fun i => rnd f pre (mm - 1 - length pre) (nF i)) (seq 0 (S d)).

  Definition pfG (avs pre : list F) : list F := lagr (rvals (fG avs) m (degZ m base (length pre)) pre).
  Definition pfT (avs pre : list F) : list F := lagr (rvals (fT avs) n1 (degZ n1 3 (length pre)) pre).

  Lemma nth_rvals : forall f mm d pre k, (k < S d)%nat ->
    nth k (rvals f mm d pre) zero = rnd f pre (mm - 1 - length pre) (nF k).
  Proof.
    intros f mm d pre k hk. unfold rvals.
    rewrite (nth_indep _ zero (rnd f pre (mm - 1 - length pre) (nF 0))) by (rewrite length_map, length_seq; exact hk).
    rewrite (map_nth (fun i => rnd f pre (mm - 1 - length pre) (nF i))), seq_nth by exact hk. reflexivity.
  Qed.

  Lemma pf_interp : forall (f : list F -> F) mm d pre X, (d < Nmax)%nat ->
    (exists pstar, (length pstar <= S d)%nat /\ forall Y, peval pstar Y = rnd f pre (mm - 1 - length pre) Y) ->
    peval (lagr (rvals f mm d pre)) X = rnd f pre (mm - 1 - length pre) X.
  Proof.
    intros f mm d pre X hd (ps & hps & hev).
    rewrite (@lagr_eval F zero one add mul sub div opp inv Hf).
    rewrite (@interp_unique F zero one add mul sub div opp inv Fdec Hf Nmax Hchar _ ps).
    - apply hev.
    - unfold rvals. rewrite length_map, length_seq. lia.
    - unfold rvals. rewrite length_map, length_seq. exact hps.
    - intros k hk. unfold rvals in hk. rewrite length_map, length_seq in hk.
      rewrite nth_rvals by exact hk. symmetry. apply hev.
  Qed.

  Lemma rvals_lagr_len : forall f mm d pre, (length (tl (lagr (rvals f mm d pre))) <= d)%nat.
  Proof.
    intros f mm d pre. pose proof (@lagr_length F zero one add mul sub opp inv (rvals f mm d pre)) as h.
    assert (hl : length (rvals f mm d pre) = S d) by (unfold rvals; rewrite length_map, length_seq; reflexivity).
    rewrite hl in h. destruct (lagr (rvals f mm d pre)); cbn in *; lia.
  Qed.

  Theorem dec_HpfG : forall avs j X, (j < m)%nat ->
    peval (pfG avs (firstn j rz)) X = rnd (fG avs) (firstn j rz) (m - 1 - j) X.
  Proof.
    intros avs j X hj. unfold pfG.
    assert (hfl : length (firstn j rz) = j) by (rewrite length_firstn; lia).
    replace (m - 1 - j)%nat with (m - 1 - length (firstn j rz))%nat by (rewrite hfl; reflexivity).
    apply pf_interp.
    { unfold degZ. destruct (Nat.eqb _ _); lia. }
    rewrite hfl.
    destruct (@certZ F zero one add mul sub div opp inv Hf m ltac:(lia) phiR base
                (@rangep_length F zero one add mul opp base)
                kG dts (firstn kd avs) tz zero zero (repeat [] m)
                (repeat_length _ _) ltac:(intros i hi; rewrite nth_repeat; cbn; lia)
                (firstn j rz) (m - 1 - j) ltac:(rewrite hfl; lia)) as (ps & h1 & h2).
    exists ps. rewrite hfl in h1. split; [exact h1 | exact h2].
  Qed.

  Theorem dec_HpfT : forall avs j X, (j < n1)%nat ->
    peval (pfT avs (firstn j rt)) X = rnd (fT avs) (firstn j rt) (n1 - 1 - j) X.
  Proof.
    intros avs j X hj. unfold pfT.
    assert (hfl : length (firstn j rt) = j) by (rewrite length_firstn; lia).
    replace (n1 - 1 - j)%nat with (n1 - 1 - length (firstn j rt))%nat by (rewrite hfl; reflexivity).
    apply pf_interp.
    { unfold degZ. destruct (Nat.eqb _ _); lia. }
    rewrite hfl.
    destruct (@certZ F zero one add mul sub div opp inv Hf n1 Hn1 phi3 3 ltac:(reflexivity)
                kT [stab; etab] (skipn kd avs) tt zero zero (repeat [] n1)
                (repeat_length _ _) ltac:(intros i hi; rewrite nth_repeat; cbn; lia)
                (firstn j rt) (n1 - 1 - j) ltac:(rewrite hfl; lia)) as (ps & h1 & h2).
    exists ps. rewrite hfl in h1. split; [exact h1 | exact h2].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the parameters of the masked round messages *)

  Lemma two_nz : add one one <> zero.
  Proof. intro e. apply (Hchar 2); [lia |]. etransitivity; [| exact e]. cbn [LogDer.nF]. field. Qed.

  Lemma ok_params : forall (dg : nat -> nat) mm (pf : list F -> list F) rho (rs : list F),
    length rs = mm -> rho <> zero ->
    (forall pre, (length (tl (pf pre)) <= dg (length pre))%nat) ->
    okparams (map dg (seq 0 mm)) (params mm pf rho rs).
  Proof.
    intros dg mm pf rho rs hl hr hd. unfold ZkSumcheck.params, ZkSumcheck.okparams.
    assert (h2 : (@two F one add) <> zero) by exact two_nz.
    assert (gen : forall s k, (s + k <= mm)%nat ->
              Forall2 (fun d ts => (length (fst ts) <= d)%nat /\ snd ts <> zero) (map dg (seq s k))
                      (map (fun j => (tl (pf (firstn j rs)), mul rho (@p2 F one add mul (mm - 1 - j)))) (seq s k))).
    { intros s k. revert s. induction k as [| k ih]; intros s hk; [constructor |].
      cbn [seq map]. constructor; [| apply ih; lia]. cbn [fst snd]. split.
      + pose proof (hd (firstn s rs)) as h. rewrite length_firstn in h. replace (Nat.min s (length rs)) with s in h by lia.
        exact h.
      + apply (@mul_nonzero F zero one add mul sub div opp inv Hf); [exact hr |].
        apply (@p2_nonzero F zero one add mul sub div opp inv Hf h2). }
    apply gen. lia.
  Qed.

  Local Notation dsG := (map (degZ m base) (seq 0 m)).
  Local Notation dsT := (map (degZ n1 3) (seq 0 n1)).

  Definition honDL := @honL2 F zero one add mul sub specsD m n1 pfG pfT rhoG rhoT rz rt.
  Definition simDL := @simL2 F zero one add mul sub inv rhoG rhoT rz rt cGD cTD.
  Definition VwDL := @Vw2 F zero one add mul sub specsD m n1 pfG pfT rhoG rhoT rz rt.
  Local Notation RLD := (@RL2 F lf specsD dsG dsT).

  (* the pieces of the layer's zero knowledge, for the join with the opening *)
  Theorem dec_layer_parts : @goodspecs F zero one mul sub specsD -> rhoG <> zero -> rhoT <> zero ->
    NoDup RLD
    /\ (forall x, In x RLD -> In (VwDL x) RLD)
    /\ (forall x x', In x RLD -> In x' RLD -> VwDL x = VwDL x' -> x = x')
    /\ (forall v, In v RLD -> exists x, In x RLD /\ VwDL x = v)
    /\ (forall x, In x RLD -> honDL x = simDL (VwDL x)).
  Proof.
    intros hgood hG hT. unfold honDL, simDL, VwDL.
    apply (@layer2_parts F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall specsD hgood two_nz m n1
             fG fT pfG pfT rhoG rhoT rz rt dsG dsT).
    - exact Hrz.
    - exact Hrt.
    - rewrite length_map, length_seq. reflexivity.
    - rewrite length_map, length_seq. reflexivity.
    - intro avs. apply ok_params; [exact Hrz | exact hG | intro pre; apply rvals_lagr_len].
    - intro avs. apply ok_params; [exact Hrt | exact hT | intro pre; apply rvals_lagr_len].
    - intros avs j X hj. apply dec_HpfG; assumption.
    - intros avs j X hj. apply dec_HpfT; assumption.
    - intros avs hl. apply dec_HcG_true; assumption.
    - intros avs hl. apply dec_HcT_true; assumption.
  Qed.

  (* Theorem 7.1, zero knowledge of the sumcheck layer *)
  Theorem dec_layer_zk : @goodspecs F zero one mul sub specsD -> rhoG <> zero -> rhoT <> zero ->
    Permutation (map honDL RLD) (map simDL RLD).
  Proof.
    intros hgood hG hT. destruct (dec_layer_parts hgood hG hT) as (n & i & j & sj & e).
    exact (zk_perm VwDL honDL simDL RLD RLD n n i j sj e).
  Qed.

End DecLayer.
