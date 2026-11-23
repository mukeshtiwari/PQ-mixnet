(* The checks of the opening (fp_core.py: _slots_compile, pcs_open_verify,
   without the Merkle paths and the transcript) as an executable boolean
   function, and its refinement to the acceptance predicate AccO of
   OpenSound.v.

   Inputs, for given challenges kappa, c, gamma, J:
     mu, the slot vectors ub v, the proximity vectors pvB, pvS (sent by the
     prover); the claims and their values; Xe i j, the entry of row i in
     opened column j (rows numbered as in MixLayout.v; the Merkle paths say
     that these are entries of the committed words).

   Theorem xaccO_sound: if xaccO returns true, AccO holds at GF(q^2) for
   the committed words X i j := to_F (Xe i j), with the same claims, values
   and messages. AccO reads X only at opened columns, so this is the
   condition of open_sound for any committed words that agree with the
   opened entries.

   Differences from fp_core.py, none of which changes the decision:
     - rows of a tensor slot are not merged (mix_proof.py adds the weights
       of repeated rows); the sums are the same;
     - gamma is the list of the coefficients of the rows of rws in order
       (fp_core.py draws one coefficient per row and skips the two rows of
       the proximity mask);
     - vectors must have length at most k (fp_core.py: exactly k);
     - codewords are evaluated by Horner's rule at omega^j (fp_core.py:
       NTT). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon Opening MatQueries OpenSound SlotKinds. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecClaims ExecFFT.
Import ListNotations.

Local Notation dot2 := (@LogDer.dot Fq2 fzero fadd fmul).
Local Notation padd2 := (@LogDer.padd Fq2 fadd).

(* ---------------------------------------------------------------------- *)
(* vectors and polynomials *)

Fixpoint xdot (a p : list xf) : xf :=
  match a, p with
  | x :: a', y :: p' => xadd (xmul x y) (xdot a' p')
  | _, _ => xzero
  end.

Fixpoint xpadd (p q : list xf) : list xf :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | x :: p', y :: q' => xadd x y :: xpadd p' q'
  end.

Definition xpscale (c : xf) (p : list xf) : list xf := map (xmul c) p.

Fixpoint xeval (p : list xf) (x : xf) : xf :=
  match p with
  | [] => xzero
  | c :: p' => xadd c (xmul x (xeval p' x))
  end.

(* x^k by square-and-multiply; the fuel k bounds the depth log2 k + 1 of the recursion *)
Fixpoint xpw_f (fuel : nat) (x : xf) (k : nat) : xf :=
  match fuel with
  | O => xone
  | S f => if Nat.eqb k 0 then xone
           else let y := xpw_f f x (Nat.div2 k) in
                if Nat.eqb (k - 2 * Nat.div2 k) 0 then xmul y y else xmul x (xmul y y)
  end.

Definition xpw (x : xf) (k : nat) : xf := xpw_f k x k.

Definition xrs_enc (om : xf) (p : list xf) (j : nat) : xf := xeval p (xpw om j).

Lemma to_F_dot : forall a p, to_F (xdot a p) = dot2 (map to_F a) (map to_F p).
Proof.
  induction a as [| x a ih]; intro p; [exact to_F_zero |]. destruct p as [| y p]; [exact to_F_zero |].
  cbn [xdot map LogDer.dot]. rewrite to_F_add, to_F_mul, ih. reflexivity.
Qed.

Lemma to_F_padd : forall p q, map to_F (xpadd p q) = padd2 (map to_F p) (map to_F q).
Proof.
  induction p as [| x p ih]; intro q; [reflexivity |]. destruct q as [| y q]; [reflexivity |].
  cbn [xpadd map LogDer.padd]. rewrite to_F_add, ih. reflexivity.
Qed.

Lemma to_F_pscale : forall c p, map to_F (xpscale c p) = @LogDer.pscale Fq2 fmul (to_F c) (map to_F p).
Proof.
  intros c p. unfold xpscale, LogDer.pscale. rewrite !map_map. apply map_ext. intro x. apply to_F_mul.
Qed.

Lemma to_F_eval : forall p x, to_F (xeval p x) = @eval Fq2 fzero fadd fmul (map to_F p) (to_F x).
Proof.
  induction p as [| c p ih]; intro x; [exact to_F_zero |].
  cbn [xeval map PolyRoots.eval]. rewrite to_F_add, to_F_mul, ih. reflexivity.
Qed.

Add Field fieldF2open : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Lemma pw_add_F : forall (x : Fq2) a b, @pw Fq2 fone fmul x (a + b) = fmul (@pw Fq2 fone fmul x a) (@pw Fq2 fone fmul x b).
Proof.
  intros x a b. induction a as [| a ih]; cbn [Nat.add Negacyclic.pw].
  + field.
  + rewrite ih. field.
Qed.

Lemma to_F_pw_f : forall fuel x k, (k < 2 ^ fuel)%nat -> to_F (xpw_f fuel x k) = @pw Fq2 fone fmul (to_F x) k.
Proof.
  induction fuel as [| f ih]; intros x k hk.
  + cbn in hk. replace k with 0%nat by lia. exact to_F_one.
  + cbn [xpw_f]. destruct (Nat.eqb_spec k 0) as [-> | hk0]; [exact to_F_one |].
    pose proof (Nat.div2_odd k) as hd.
    assert (hdl : (Nat.div2 k < 2 ^ f)%nat).
    { rewrite Nat.div2_div. apply Nat.Div0.div_lt_upper_bound. rewrite Nat.pow_succ_r' in hk. lia. }
    set (d := Nat.div2 k) in *.
    destruct (Nat.odd k); cbn [Nat.b2n] in hd.
    - replace (Nat.eqb (k - 2 * d) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
      rewrite !to_F_mul, (ih x _ hdl).
      assert (e : @pw Fq2 fone fmul (to_F x) k = fmul (to_F x) (fmul (@pw Fq2 fone fmul (to_F x) d) (@pw Fq2 fone fmul (to_F x) d))).
      { rewrite hd. replace (2 * d + 1)%nat with (1 + (d + d))%nat by lia. rewrite !pw_add_F. cbn [Negacyclic.pw]. field. }
      rewrite e. reflexivity.
    - replace (Nat.eqb (k - 2 * d) 0) with true by (symmetry; apply Nat.eqb_eq; lia).
      rewrite to_F_mul, (ih x _ hdl).
      assert (e : @pw Fq2 fone fmul (to_F x) k = fmul (@pw Fq2 fone fmul (to_F x) d) (@pw Fq2 fone fmul (to_F x) d)).
      { rewrite hd. replace (2 * d + 0)%nat with (d + d)%nat by lia. apply pw_add_F. }
      rewrite e. reflexivity.
Qed.

Lemma to_F_pw : forall x k, to_F (xpw x k) = @pw Fq2 fone fmul (to_F x) k.
Proof. intros x k. apply to_F_pw_f. apply Nat.pow_gt_lin_r. lia. Qed.

Lemma to_F_rs_enc : forall om p j,
  to_F (xrs_enc om p j) = @rs_enc Fq2 fzero fone fadd fmul (to_F om) (map to_F p) j.
Proof. intros om p j. unfold xrs_enc, ReedSolomon.rs_enc. rewrite to_F_eval, to_F_pw. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* compiling the slots (SlotKinds.v) *)

Definition tslotx (t : xterm) : nat := fst (fst (fst t)).
Definition trowx (t : xterm) : nat := snd (fst (fst t)).
Definition tcoefx (t : xterm) : xf := snd (fst t).
Definition tlvx (t : xterm) : list xf := snd t.

Fixpoint xgsel (k0 : xf) (cl : list xterm) (v : nat) : list (nat * xf) :=
  match cl with
  | [] => []
  | t :: cl' => if Nat.eqb (tslotx t) v then (trowx t, xmul k0 (tcoefx t)) :: xgsel k0 cl' v else xgsel k0 cl' v
  end.

Fixpoint xgbatch (kp : list xf) (cls : list (list xterm)) (v : nat) : list (nat * xf) :=
  match kp, cls with
  | k0 :: kp', cl :: cls' => xgsel k0 cl v ++ xgbatch kp' cls' v
  | _, _ => []
  end.

Fixpoint xlsel (k0 : xf) (cl : list xterm) (v : nat) : list xf :=
  match cl with
  | [] => []
  | t :: cl' =>
      if Nat.eqb (tslotx t) v then xpadd (xpscale (xmul k0 (tcoefx t)) (tlvx t)) (xlsel k0 cl' v) else xlsel k0 cl' v
  end.

Fixpoint xlsum (kp : list xf) (cls : list (list xterm)) (v : nat) : list xf :=
  match kp, cls with
  | k0 :: kp', cl :: cls' => xpadd (xlsel k0 cl v) (xlsum kp' cls' v)
  | _, _ => []
  end.

Section Compile.

  Variable kind : nat -> bool.
  Variable frow : nat -> nat.
  Variable Ltx : nat -> list xf.

  Definition xcbk (kp : list xf) (cls : list (list xterm)) (v : nat) : list (nat * xf) :=
    if kind v then [(frow v, xone)] else xgbatch kp cls v.

  Definition xLk (kp : list xf) (cls : list (list xterm)) (v : nat) : list xf :=
    if kind v then xlsum kp cls v else Ltx v.

  Definition pairF (iw : nat * xf) : nat * Fq2 := (fst iw, to_F (snd iw)).

  Local Notation LtF := (fun v => map to_F (Ltx v)).

  Lemma tF_fields : forall t, tslot (tF t) = tslotx t /\ trow (tF t) = trowx t /\ tcoef (tF t) = to_F (tcoefx t)
                              /\ tlv (tF t) = map to_F (tlvx t).
  Proof. intros [[[s r] c] lv]. repeat split. Qed.

  Lemma to_F_gsel : forall k0 cl v, map pairF (xgsel k0 cl v) = @gsel Fq2 fmul (to_F k0) (map tF cl) v.
  Proof.
    intros k0; induction cl as [| t cl ih]; intro v; [reflexivity |].
    destruct (tF_fields t) as (e1 & e2 & e3 & e4).
    cbn [xgsel map SlotKinds.gsel]. rewrite e1. destruct (Nat.eqb (tslotx t) v); [| apply ih].
    cbn [map]. rewrite ih. unfold pairF. cbn [fst snd]. rewrite e2, e3, to_F_mul. reflexivity.
  Qed.

  Lemma to_F_gbatch : forall kp cls v,
    map pairF (xgbatch kp cls v) = @gbatch Fq2 fmul (map to_F kp) (map (map tF) cls) v.
  Proof.
    induction kp as [| k0 kp ih]; intros cls v; [reflexivity |]. destruct cls as [| cl cls]; [reflexivity |].
    cbn [xgbatch map SlotKinds.gbatch]. rewrite map_app, to_F_gsel, ih. reflexivity.
  Qed.

  Lemma to_F_lsel : forall k0 cl v, map to_F (xlsel k0 cl v) = @lsel Fq2 fadd fmul (to_F k0) (map tF cl) v.
  Proof.
    intros k0; induction cl as [| t cl ih]; intro v; [reflexivity |].
    destruct (tF_fields t) as (e1 & e2 & e3 & e4).
    cbn [xlsel map SlotKinds.lsel]. rewrite e1. destruct (Nat.eqb (tslotx t) v); [| apply ih].
    rewrite to_F_padd, to_F_pscale, ih, to_F_mul, e3, e4. reflexivity.
  Qed.

  Lemma to_F_lsum : forall kp cls v,
    map to_F (xlsum kp cls v) = @lsum Fq2 fadd fmul (map to_F kp) (map (map tF) cls) v.
  Proof.
    induction kp as [| k0 kp ih]; intros cls v; [reflexivity |]. destruct cls as [| cl cls]; [reflexivity |].
    cbn [xlsum map SlotKinds.lsum]. rewrite to_F_padd, to_F_lsel, ih. reflexivity.
  Qed.

  Lemma to_F_cbk : forall kp cls v,
    map pairF (xcbk kp cls v) = @cbk Fq2 fone fmul kind frow (map to_F kp) (map (map tF) cls) v.
  Proof.
    intros kp cls v. unfold xcbk, SlotKinds.cbk. destruct (kind v); [| apply to_F_gbatch].
    cbn. unfold pairF. cbn. rewrite to_F_one. reflexivity.
  Qed.

  Lemma to_F_Lk : forall kp cls v,
    map to_F (xLk kp cls v) = @Lk Fq2 fadd fmul kind LtF (map to_F kp) (map (map tF) cls) v.
  Proof.
    intros kp cls v. unfold xLk, SlotKinds.Lk. destruct (kind v); [apply to_F_lsum | reflexivity].
  Qed.

End Compile.

(* ---------------------------------------------------------------------- *)
(* the checks *)

(* ---------------------------------------------------------------------- *)
(* the encoding of a whole vector by the NTT (ExecFFT.v), looked up at the opened columns *)

Definition xencv (w : Z) (n : nat) (p : list xf) : list xf := combine (zenc w n (map fst p)) (zenc w n (map snd p)).

(* the value of the encoding of p at column j: from the precomputed encoding ep when om is in the
   base field and j < n, otherwise by Horner *)
Definition xenc_at (om : xf) (n : nat) (ep p : list xf) (j : nat) : xf :=
  if Nat.ltb j n && Z.eqb (snd om) 0 then nth j ep xzero else xrs_enc om p j.

Lemma to_F_bz_split : forall x : xf, to_F x = fadd (to_F (bz (fst x))) (fmul ftg (to_F (bz (snd x)))).
Proof.
  intros [p q]. rewrite <-to_F_tg, <-to_F_mul, <-to_F_add. unfold to_F, xadd, xmul, xtg, bz. cbn [fst snd].
  replace (0 * q + 3 * 1 * 0)%Z with 0%Z by ring. replace (0 * 0 + 1 * q)%Z with q by ring.
  rewrite Zmod_0_l, Z.add_0_r, Z.add_0_l, !zq_of_mod. reflexivity.
Qed.

Lemma peval_split_ri : forall (p : list xf) x,
  @eval Fq2 fzero fadd fmul (map to_F p) x = fadd (@eval Fq2 fzero fadd fmul (map to_F (map bz (map fst p))) x) (fmul ftg (@eval Fq2 fzero fadd fmul (map to_F (map bz (map snd p))) x)).
Proof.
  induction p as [| c p ih]; intro x; cbn [map PolyRoots.eval]; [field |].
  rewrite ih, (to_F_bz_split c). field.
Qed.

Lemma xencv_F : forall w n p j, (j < n)%nat ->
  to_F (nth j (xencv w n p) xzero) = @rs_enc Fq2 fzero fone fadd fmul (to_F (bz w)) (map to_F p) j.
Proof.
  intros w n p j hj. unfold xencv. change xzero with (0%Z, 0%Z). unfold xf.
  rewrite combine_nth by (rewrite !xfft_zenc_length; reflexivity).
  rewrite to_F_bz_split. cbn [fst snd]. unfold bz at 1 2. fold (bz (nth j (zenc w n (map fst p)) 0%Z)).
  fold (bz (nth j (zenc w n (map snd p)) 0%Z)).
  rewrite !xfft_zenc_F by exact hj. unfold ReedSolomon.rs_enc. rewrite (peval_split_ri p (pw (to_F (bz w)) j)). reflexivity.
Qed.

Lemma xencv_reduced : forall w n p j, (j < n)%nat -> reduced (nth j (xencv w n p) xzero).
Proof.
  intros w n p j hj. unfold xencv. change xzero with (0%Z, 0%Z). unfold xf.
  rewrite combine_nth by (rewrite !xfft_zenc_length; reflexivity).
  assert (hr : forall msg, (0 <= nth j (zenc w n msg) 0%Z < Q)%Z).
  { intro msg. rewrite xfft_zenc_spec. unfold zenc_horner.
    rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, xfft_zpows_len; exact hj).
    rewrite map_nth. apply xfft_zhorner_range. }
  split; cbn [fst snd]; apply hr.
Qed.

Lemma to_F_enc_at : forall om n ep p j, ep = xencv (fst om) n p ->
  to_F (xenc_at om n ep p j) = @rs_enc Fq2 fzero fone fadd fmul (to_F om) (map to_F p) j.
Proof.
  intros [w w2] n ep p j ->. unfold xenc_at. cbn [fst snd].
  destruct (Nat.ltb_spec j n) as [hj | hj]; [destruct (Z.eqb_spec w2 0) as [-> | hw] |]; cbn [andb].
  - apply xencv_F, hj.
  - apply to_F_rs_enc.
  - apply to_F_rs_enc.
Qed.

Lemma xenc_at_reduced : forall om n p j, reduced (xenc_at om n (xencv (fst om) n p) p j).
Proof.
  intros om n p j. unfold xenc_at.
  destruct (Nat.ltb_spec j n) as [hj | hj]; cbn [andb]; [destruct (Z.eqb (snd om) 0) |].
  - apply xencv_reduced, hj.
  - unfold xrs_enc. destruct p as [| c p]; [unfold reduced, xzero; cbn; unfold Q; lia | apply xadd_reduced].
  - unfold xrs_enc. destruct p as [| c p]; [unfold reduced, xzero; cbn; unfold Q; lia | apply xadd_reduced].
Qed.

Section Checks.

  Variable Xe : nat -> nat -> xf.
  Local Notation XF := (fun i j => to_F (Xe i j)).

  Fixpoint xwsum (cb : list (nat * xf)) (j : nat) : xf :=
    match cb with
    | [] => xzero
    | iw :: cb' => xadd (xmul (snd iw) (Xe (fst iw) j)) (xwsum cb' j)
    end.

  Definition xxw (mcb cb : list (nat * xf)) (c : xf) (j : nat) : xf := xadd (xwsum mcb j) (xmul c (xwsum cb j)).

  Definition xpi (xmp : nat -> xf) (rws : list nat) (gam : list xf) (j : nat) : xf :=
    xadd (xmp j) (xdot gam (map (fun i => Xe i j) rws)).

  Lemma to_F_wsum : forall cb j,
    to_F (xwsum cb j) = @wsum Fq2 fzero fadd fmul XF (map pairF cb) j.
  Proof.
    induction cb as [| [i w] cb ih]; intro j; [exact to_F_zero |].
    cbn [xwsum map Opening.wsum pairF fst snd]. rewrite to_F_add, to_F_mul, ih. reflexivity.
  Qed.

  Lemma to_F_xw : forall mcb cb c j,
    to_F (xxw mcb cb c j) = @xw Fq2 fzero fadd fmul XF (map pairF mcb) (map pairF cb) (to_F c) j.
  Proof. intros. unfold xxw, Opening.xw. rewrite to_F_add, to_F_mul, !to_F_wsum. reflexivity. Qed.

  Lemma to_F_pi : forall xmp rws gam j,
    to_F (xpi xmp rws gam j)
    = @pi Fq2 fzero fadd fmul (fun j => to_F (xmp j)) (map XF rws) (map to_F gam) j.
  Proof.
    intros. unfold xpi, Proximity.pi, Proximity.lin. rewrite to_F_add, to_F_dot, !map_map. reflexivity.
  Qed.

  (* one matrix *)
  Definition xmacc (om : xf) (n k : nat) (xmp : nat -> xf) (rws : list nat) (gam pv : list xf) (svM : list nat)
    (ub : nat -> list xf) (mcb cb : nat -> list (nat * xf)) (c : xf) (J : list nat) : bool :=
    Nat.leb (length pv) k
    && (let ep := xencv (fst om) n pv in forallb (fun j => xeqb (xenc_at om n ep pv j) (xpi xmp rws gam j)) J)
    && forallb (fun v => Nat.leb (length (ub v)) k
                         && (let eu := xencv (fst om) n (ub v) in
                             forallb (fun j => xeqb (xenc_at om n eu (ub v) j) (xxw (mcb v) (cb v) c j)) J)) svM.

  Lemma xeqb_eq : forall x y, xeqb x y = true -> to_F x = to_F y.
  Proof.
    intros [a b] [c d] h. unfold xeqb in h. cbn [fst snd] in h. apply andb_true_iff in h.
    destruct h as [h1 h2]. apply Z.eqb_eq in h1, h2. subst. reflexivity.
  Qed.

  Theorem xmacc_sound : forall om n k xmp rws gam pv svM ub mcb cb c J,
    xmacc om n k xmp rws gam pv svM ub mcb cb c J = true ->
    @macc Fq2 fzero fone fadd fmul (to_F om) k XF (fun j => to_F (xmp j)) rws (map to_F gam) (map to_F pv) svM
          (fun v => map to_F (ub v)) (fun v => map pairF (mcb v)) (fun v => map pairF (cb v)) (to_F c) J.
  Proof.
    intros om n k xmp rws gam pv svM ub mcb cb c J h. unfold xmacc in h. cbv zeta in h.
    apply andb_true_iff in h. destruct h as [h h3]. apply andb_true_iff in h. destruct h as [h1 h2].
    unfold MatQueries.macc. split; [| split].
    + rewrite length_map. apply Nat.leb_le. exact h1.
    + intros j hj. rewrite forallb_forall in h2. specialize (h2 j hj).
      apply xeqb_eq in h2. rewrite (to_F_enc_at om n _ pv j eq_refl), to_F_pi in h2. exact h2.
    + intros v hv. rewrite forallb_forall in h3. specialize (h3 v hv). apply andb_true_iff in h3.
      destruct h3 as [hl hj]. split; [rewrite length_map; apply Nat.leb_le; exact hl |].
      intros j hjJ. rewrite forallb_forall in hj. specialize (hj j hjJ). apply xeqb_eq in hj.
      rewrite (to_F_enc_at om n _ (ub v) j eq_refl), to_F_xw in hj. exact hj.
  Qed.

  (* both matrices and the claimed values *)
  Variables omB omS : xf.
  Variables nB nS : nat.
  Variables kB kS : nat.
  Variables xmpB xmpS : nat -> xf.
  Variables rwsB rwsS : list nat.
  Variable kind : nat -> bool.
  Variable frow : nat -> nat.
  Variable Ltx : nat -> list xf.
  Variable mcb : nat -> list (nat * xf).
  Variables svB svS : list nat.
  Variable cls : list (list xterm).
  Variable vals : list xf.

  Definition xaccO (kp : list xf) (c : xf) (gamB gamS : list xf) (JB JS : list nat)
    (mu : xf) (ub : nat -> list xf) (pvB pvS : list xf) : bool :=
    xeqb (xfsum (map (fun v => xdot (ub v) (xLk kind Ltx kp cls v)) (svB ++ svS))) (xadd mu (xmul c (xdot kp vals)))
    && xmacc omB nB kB xmpB rwsB gamB pvB svB ub mcb (xcbk kind frow kp cls) c JB
    && xmacc omS nS kS xmpS rwsS gamS pvS svS ub mcb (xcbk kind frow kp cls) c JS.

  Theorem xaccO_sound : forall kp c gamB gamS JB JS mu ub pvB pvS,
    xaccO kp c gamB gamS JB JS mu ub pvB pvS = true ->
    @AccO Fq2 fzero fone fadd fmul (to_F omB) (to_F omS) kB kS XF rwsB rwsS
          (fun j => to_F (xmpB j)) (fun j => to_F (xmpS j)) (map to_F vals)
          (fun kp' => @Lk Fq2 fadd fmul kind (fun v => map to_F (Ltx v)) kp' (map (map tF) cls))
          (fun kp' => @cbk Fq2 fone fmul kind frow kp' (map (map tF) cls))
          (fun v => map pairF (mcb v)) svB svS
          (fun _ => to_F mu) (fun _ _ v => map to_F (ub v)) (fun _ _ => map to_F pvB) (fun _ _ => map to_F pvS)
          (map to_F kp) (to_F c, (map to_F gamB, map to_F gamS)) (JB, JS).
  Proof.
    intros kp c gamB gamS JB JS mu ub pvB pvS h. unfold xaccO in h.
    apply andb_true_iff in h. destruct h as [h hS]. apply andb_true_iff in h. destruct h as [h0 hB].
    unfold OpenSound.AccO, OpenSound.maccB, OpenSound.maccS. cbn [fst snd].
    split; [| split].
    + apply xeqb_eq in h0. rewrite to_F_fsum, map_map, to_F_add, to_F_mul, to_F_dot in h0.
      rewrite <-h0. f_equal. apply map_ext. intro v. rewrite to_F_dot, to_F_Lk. reflexivity.
    + pose proof (xmacc_sound _ _ _ _ _ _ _ _ _ _ _ _ _ hB) as m.
      unfold MatQueries.macc in *. destruct m as (m1 & m2 & m3). split; [exact m1 | split; [exact m2 |]].
      intros v hv. destruct (m3 v hv) as [m4 m5]. split; [exact m4 |].
      intros j hj. rewrite (m5 j hj). f_equal. apply to_F_cbk.
    + pose proof (xmacc_sound _ _ _ _ _ _ _ _ _ _ _ _ _ hS) as m.
      unfold MatQueries.macc in *. destruct m as (m1 & m2 & m3). split; [exact m1 | split; [exact m2 |]].
      intros v hv. destruct (m3 v hv) as [m4 m5]. split; [exact m4 |].
      intros j hj. rewrite (m5 j hj). f_equal. apply to_F_cbk.
  Qed.

End Checks.
