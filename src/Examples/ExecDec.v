(* The verifier of the decryption proof (dec_proof.py: dec_derive,
   dec_verify) as executable code, and what its acceptance implies.

   - xclaimsD, to_F_claimsD: the kd + 6 claims of dec_derive are claimsD of
     DecLayout.v at GF(q^2). Claim D uses the sum of the adjoints
     nadj u_i eq(theta1) weighted by eq(theta, i), as in the proofs;
     dec_proof.py computes the same vector with tshift of the combined u_i
     (compared in Unverified/cross_field.py, not proven).
   - xdec_derive, xdec_derive_sound: the sumcheck layer of dec_derive gives
     valsD and PreAccD of DecSound.v, with VD, VK as in DecFinal.v.
   - xdec_back, xdec_back_sound: derive + claims + opening checks (xaccO)
     give, at the transcript's challenges, the events of dec_full /
     dec_theorem_7_1, with the committed words replaced by the opened
     entries.
   - xdec_front: the Fiat-Shamir transcript and the Merkle paths, on a proof
     given as its components. Not proven, as for the shuffle proof.
   - xdec_parse, xdec_verify_bytes: the byte format of dec_proof.py
     (dec_serialize): fields in transcript order, no length prefixes, no
     trailing bytes. Not proven (tested against dec_deserialize). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String Ascii setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckSound MaskedExt SlotKinds OpenSound RowLayout ZeroTest DecSound DecLayout Interp. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify.
Import ListNotations.
Local Open Scope list_scope.

Add Field fieldF2e : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation bidx2 := (@bidx Fq2 fone Fq2_dec).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation eqvec2 := (@eqvec Fq2 fzero fone fadd fmul fsub).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation nF2 := (@nF Fq2 fzero fone fadd).
Local Notation peval2 := (@eval Fq2 fzero fadd fmul).

(* ---------------------------------------------------------------------- *)
(* tools *)

Lemma bidx_app : forall u v : list Fq2, bidx2 (u ++ v) = (bidx2 u + 2 ^ List.length u * bidx2 v)%nat.
Proof.
  induction u as [| x u ih]; intro v; cbn [app bidx List.length Nat.pow]; [lia |].
  rewrite ih. destruct (Fq2_dec x fone); lia.
Qed.

Lemma nth_concat_uniform : forall {A : Type} (ls : list (list A)) (n x i : nat) (d : A),
  (forall l, In l ls -> List.length l = n) -> (x < n)%nat -> (i < List.length ls)%nat ->
  nth (x + n * i) (List.concat ls) d = nth x (nth i ls []) d.
Proof.
  intros A ls n x; induction ls as [| l ls ih]; intros i d hl hx hi; [cbn in hi; lia |].
  cbn [List.concat]. destruct i as [| i].
  + rewrite Nat.mul_0_r, Nat.add_0_r. cbn [nth]. apply app_nth1. rewrite (hl l (or_introl eq_refl)). exact hx.
  + rewrite app_nth2 by (rewrite (hl l (or_introl eq_refl)); nia). rewrite (hl l (or_introl eq_refl)).
    replace (x + n * S i - n)%nat with (x + n * i)%nat by nia. cbn [nth].
    apply ih; [intros l' h'; apply hl; right; exact h' | exact hx | cbn in hi; lia].
Qed.

Lemma length_concat_uniform : forall {A : Type} (ls : list (list A)) (n : nat),
  (forall l, In l ls -> List.length l = n) -> List.length (List.concat ls) = (List.length ls * n)%nat.
Proof.
  intros A ls n; induction ls as [| l ls ih]; intro h; [reflexivity |].
  cbn [List.concat List.length]. rewrite length_app, (h l (or_introl eq_refl)), ih by (intros; apply h; right; assumption).
  lia.
Qed.

Lemma nth_eq_table : forall (y : list xf) i, (i < 2 ^ List.length y)%nat ->
  to_F (nth i (xeq_table y) xzero) = eqp2 (pt2 (List.length y) i) (map to_F y).
Proof.
  intros y i hi. rewrite to_F_nth, to_F_eq_table. unfold RowLayout.eqvec.
  rewrite (nth_indep _ fzero (eqp2 (pt2 (List.length y) 0) (map to_F y))) by (rewrite length_map, length_seq; exact hi).
  rewrite (map_nth (fun j => eqp2 (pt2 (List.length y) j) (map to_F y))), seq_nth by exact hi. reflexivity.
Qed.

(* sum_k k_i phi(z_i) *)
Fixpoint xinnerZ (phi : xf -> xf) (ks zl : list xf) : xf :=
  match ks, zl with
  | k :: ks', z :: zl' => xadd (xmul k (phi z)) (xinnerZ phi ks' zl')
  | _, _ => xzero
  end.

Lemma to_F_innerZ : forall (phi : xf -> xf) (phiF : list Fq2) ks zl,
  (forall z, to_F (phi z) = peval2 phiF (to_F z)) ->
  to_F (xinnerZ phi ks zl) = @innerZ Fq2 fzero fadd fmul phiF (map to_F ks) (map to_F zl).
Proof.
  intros phi phiF ks; induction ks as [| k ks ih]; intros zl hp; [exact to_F_zero |].
  destruct zl as [| z zl]; [exact to_F_zero |].
  cbn [xinnerZ map ZeroTest.innerZ]. rewrite to_F_add, to_F_mul, hp, ih by exact hp. reflexivity.
Qed.

(* prod_(v < k) (z - v) *)
Fixpoint xrangep (k : nat) (z : xf) : xf :=
  match k with
  | O => xone
  | S k' => xmul (xrangep k' z) (xsub z (xint (Z.of_nat k')))
  end.

Lemma to_F_rangep : forall k z, to_F (xrangep k z) = peval2 (@rangep Fq2 fzero fone fadd fmul fopp k) (to_F z).
Proof.
  induction k as [| k ih]; intro z.
  + cbn. rewrite to_F_one. field.
  + cbn [xrangep]. rewrite (@rangep_eval Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field k (to_F z)).
    rewrite to_F_mul, ih, to_F_sub, to_F_xint_nat. reflexivity.
Qed.

Lemma to_F_cube_phi3 : forall z, to_F (xcube3 z) = peval2 (@phi3 Fq2 fzero fone fopp) (to_F z).
Proof.
  intro z. rewrite (@phi3_eval Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), to_F_cube3. reflexivity.
Qed.

Fixpoint xlincomb (e : nat -> xf) (g : nat -> list xf) (l : list nat) : list xf :=
  match l with
  | [] => []
  | i :: l' => xpadd (xpscale (e i) (g i)) (xlincomb e g l')
  end.

Lemma to_F_lincomb : forall e g (eF : nat -> Fq2) (gF : nat -> list Fq2) l,
  (forall i, In i l -> to_F (e i) = eF i) -> (forall i, In i l -> map to_F (g i) = gF i) ->
  map to_F (xlincomb e g l) = @lincomb Fq2 fadd fmul eF gF l.
Proof.
  intros e g eF gF; induction l as [| i l ih]; intros he hg; [reflexivity |].
  cbn [xlincomb DecLayout.lincomb]. rewrite to_F_padd, to_F_pscale, he, hg by (left; reflexivity).
  rewrite ih; [reflexivity | intros j hj; apply he; right; exact hj | intros j hj; apply hg; right; exact hj].
Qed.

Lemma tF_mk : forall s r c lv, tF (s, r, c, lv) = mk_gterm s r (to_F c) (map to_F lv).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the claims *)

Section Claims.

  Variables n1 ell lo1 SO kd base : nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Variable ax : list xf.
  Variable ppx : xf.
  Variable usx : list (list xf).
  Variables dG dT : list nat.
  Variables ptD th2 rz rt : list xf.
  Local Notation rw := (rwD n1 ell lo1).

  Definition xgS (c : xf) (lv : list xf) : xterm := (3%nat, SO, c, lv).
  Definition xgE (c : xf) (lv : list xf) : xterm := (4%nat, (SO + 1)%nat, c, lv).
  Definition xgM (c : xf) (lv : list xf) : xterm := (5%nat, (SO + 2)%nat, c, lv).

  Definition xwsv : list xf :=
    xlincomb (fun i => nth i (xeq_table (skipn n1 ptD)) xzero)
             (fun i => xnadj (nth i usx []) (xeq_table (firstn n1 ptD))) (seq 0 tau).
  Definition xwav : list xf := xnadj ax (xeq_table th2).

  Definition xdigD : list xterm :=
    List.concat (map (fun d => xtabt 1 (d * rw)%nat (xmul ppx (xint (Z.of_nat base ^ Z.of_nat d)%Z)) lo1 ptD) (seq 0 kd)).

  Definition xclZ (d : nat) : list xterm := xtabt 2 (d * rw)%nat xone lo1 rz ++ [xgM (xzval rz) (xunitv d)].

  Definition xclaimsD : list (list xterm) :=
    (xgS xone xwsv :: xdigD)
    :: [xgS xone xwav; xgE ppx (xeq_table th2)]
    :: map xclZ (seq 0 kd)
    ++ [[xgS xone (xeq_table rt); xgM (xzval rt) (xunitv kd)];
        [xgE xone (xeq_table rt); xgM (xzval rt) (xunitv (kd + 1))];
        [xgM xone (xgfunv (offG kd) (xfuncv dG rz))];
        [xgM xone (xgfunv (offT kd dG) (xfuncv dT rt))]].

  Hypothesis HptD : List.length ptD = m.
  Hypothesis Hth2 : List.length th2 = n1.
  Hypothesis Hrz : List.length rz = m.
  Hypothesis Hrt : List.length rt = n1.

  Local Notation usF := (fun i => map to_F (nth i usx [])).

  Theorem to_F_claimsD :
    map (map tF) xclaimsD
    = @claimsD Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base (map to_F ax) (to_F ppx) usF dG dT
               (map to_F ptD) (map to_F th2) (map to_F rz) (map to_F rt).
  Proof.
    assert (eqt : forall y : list xf, List.length y = n1 -> map to_F (xeq_table y) = eqvec2 n1 (map to_F y))
      by (intros y hy; rewrite to_F_eq_table, hy; reflexivity).
    unfold xclaimsD, DecLayout.claimsD. cbn [map]. f_equal; [| f_equal; [| rewrite !map_app, !map_map]].
    + (* claim D *)
      unfold DecLayout.clD. cbn [map]. f_equal.
      * unfold xgS, DecLayout.gS, DecLayout.rS. rewrite tF_mk, to_F_one. f_equal.
        unfold xwsv, DecLayout.wsv.
        apply to_F_lincomb.
        -- intros i hi. apply in_seq in hi.
           rewrite nth_eq_table by (rewrite length_skipn; replace (List.length ptD - n1)%nat with ell by lia; lia).
           rewrite length_skipn, <-skipn_map. f_equal. f_equal. lia.
        -- intros i _. rewrite to_F_nadj, eqt by (rewrite length_firstn; lia). rewrite firstn_map. reflexivity.
      * unfold xdigD, DecLayout.digD. rewrite concat_map, !map_map. f_equal. apply map_ext. intro d.
        rewrite to_F_tabt, HptD, to_F_mul, <-Nat2Z.inj_pow, to_F_xint_nat. reflexivity.
    + (* claim K *)
      unfold DecLayout.clK, xgS, xgE, DecLayout.gS, DecLayout.gE, DecLayout.rS, DecLayout.rE. cbn [map].
      rewrite !tF_mk, to_F_one. unfold xwav, DecLayout.wav. rewrite to_F_nadj, !eqt by exact Hth2. reflexivity.
    + f_equal.
      * apply map_ext. intro d. unfold xclZ, DecLayout.clZ. rewrite map_app, to_F_tabt, Hrz. cbn [map].
        unfold xgM, DecLayout.gM, DecLayout.rMd. cbn [map]. rewrite tF_mk, to_F_zval, to_F_unitv. reflexivity.
      * unfold DecLayout.clS, DecLayout.clE, DecLayout.clGm, DecLayout.clTm, xgS, xgE, xgM,
               DecLayout.gS, DecLayout.gE, DecLayout.gM, DecLayout.rS, DecLayout.rE, DecLayout.rMd. cbn [map].
        rewrite !tF_mk, !to_F_one, !to_F_zval, !to_F_unitv, !eqt by exact Hrt.
        rewrite !to_F_gfunv, !to_F_funcv. reflexivity.
  Qed.

End Claims.

(* ---------------------------------------------------------------------- *)
(* the sumcheck layer *)

Section Derive.

  Variables n1 ell kd base : nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Variables (bx : list xf) (ppx offx : xf) (tsx : list (list xf)).
  (* challenges *)
  Variables th th1 th2 tz kG rz tt kT rt : list xf.
  (* messages *)
  Variables GGx GTx : xf.
  Variables mG mT : list (list xf).
  Variables zGx zTx : list xf.

  Definition ptDx : list xf := th1 ++ th.

  Definition VDx : xf := xadd (xmle (List.concat tsx) ptDx) (xmul ppx offx).
  Definition VKx : xf := xdot bx (xeq_table th2).
  Definition claimGx : xf := xmul (xkk kG kd) GGx.
  Definition claimTx : xf := xmul (xkk kT 2) GTx.
  Definition fGx : xf := xmul (xeq_eval rz tz) (xinnerZ (xrangep base) (firstn kd kG) zGx).
  Definition fTx : xf := xmul (xeq_eval rt tt) (xinnerZ xcube3 (firstn 2 kT) zTx).

  Definition dshapes_ok : bool :=
    Nat.eqb (List.length zGx) kd && Nat.eqb (List.length zTx) 2 && Nat.eqb (List.length th1) n1
    && Nat.eqb (List.length th) ell && Nat.eqb (List.length th2) n1 && Nat.eqb (List.length tsx) tau
    && forallb (fun l => Nat.eqb (List.length l) N) tsx && Nat.eqb (List.length bx) N
    && forallb (fun ev => Nat.leb (List.length ev) DMAX) mG && forallb (fun ev => Nat.leb (List.length ev) DMAX) mT
    && xnz (xkk kG kd) && xnz (xkk kT 2).

  Definition xdec_derive : option (list xf) :=
    if dshapes_ok then
      match xsc_verify mG rz claimGx, xsc_verify mT rt claimTx with
      | Some clG, Some clT =>
          Some ([VDx; VKx] ++ zGx ++ zTx ++
                [xmul (xsub clG fGx) (xinv (xkk kG kd)); xmul (xsub clT fTx) (xinv (xkk kT 2))])
      | _, _ => None
      end
    else None.

  (* at the field *)
  Variables (dts : list (list Fq2 -> Fq2)) (stab etab : list Fq2 -> Fq2).
  Hypothesis Hdts : List.length dts = kd.

  Definition tsF (i : nat) : list Fq2 := map to_F (nth i tsx []).
  Definition VDF (t : @ThT Fq2) : Fq2 :=
    @VDv Fq2 fzero fone fadd fmul fsub Fq2_dec n1 ell (to_F ppx) (to_F offx) tsF (fst t).
  Definition VKF (t : @ThT Fq2) : Fq2 := @VKv Fq2 fzero fone fadd fmul fsub n1 (map to_F bx) (snd t).

  Definition wD : @WD Fq2 :=
    (((map to_F ptDx, map to_F th2), ((map to_F tz, map to_F kG), map to_F rz)),
     ((map to_F tt, map to_F kT), map to_F rt)).

  Definition cmsG := @coefmsgs Fq2 fzero fone fadd fmul fsub fopp finv (map (map to_F) mG) (map to_F rz) (to_F claimGx).
  Definition cmsT := @coefmsgs Fq2 fzero fone fadd fmul fsub fopp finv (map (map to_F) mT) (map to_F rt) (to_F claimTx).
  Definition stratGF (_ : @ThT Fq2) (_ : list Fq2 * list Fq2) (pre : list Fq2) : list Fq2 := nth (List.length pre) cmsG [].
  Definition stratTF (_ : @P2 Fq2) (_ : list Fq2 * list Fq2) (pre : list Fq2) : list Fq2 := nth (List.length pre) cmsT [].
  Definition zsGF (_ : @ThT Fq2) (_ : list Fq2 * list Fq2) (_ : list Fq2) : list Fq2 := map to_F zGx.
  Definition zsTF (_ : @P2 Fq2) (_ : list Fq2 * list Fq2) (_ : list Fq2) : list Fq2 := map to_F zTx.
  Definition GGGF (_ : @ThT Fq2) : Fq2 := to_F GGx.
  Definition GGTF (_ : @P2 Fq2) : Fq2 := to_F GTx.

  Local Notation phiR := (@rangep Fq2 fzero fone fadd fmul fopp base).

  Definition valsDF : list Fq2 :=
    @valsD Fq2 fzero fone fadd fmul fsub fopp finv Fq2_dec dts stab etab phiR GGGF stratGF zsGF GGTF stratTF zsTF
           VDF VKF wD.
  Definition PreAccDF : Prop :=
    @PreAccD Fq2 fzero fone fadd fmul Fq2_dec dts stab etab GGGF stratGF zsGF GGTF stratTF zsTF wD.

  Lemma VD_value : List.length th1 = n1 -> List.length th = ell -> List.length tsx = tau ->
    (forall l, In l tsx -> List.length l = N) -> to_F VDx = VDF (fst (fst wD)).
  Proof.
    intros h1 h0 hts hl. unfold VDx, VDF, wD, DecLayout.VDv. cbn [fst].
    rewrite to_F_add, to_F_mul. f_equal.
    assert (hp : List.length ptDx = m) by (unfold ptDx; rewrite length_app; lia).
    rewrite to_F_mle.
    2:{ rewrite hp. rewrite (length_concat_uniform tsx N hl), hts, Nat.pow_add_r. lia. }
    rewrite hp. apply (@mle_ext Fq2 fzero fone fadd fmul fsub m). intros bq hb.
    pose proof (@cube_length Fq2 fzero fone m bq hb) as hbl.
    unfold tabOf, DecLayout.TsT, tsF.
    rewrite <-(firstn_skipn n1 bq) at 1. rewrite bidx_app, length_firstn.
    replace (Nat.min n1 (List.length bq)) with n1 by lia.
    pose proof (@bidx_lt Fq2 fone Fq2_dec (firstn n1 bq)) as b1. rewrite length_firstn in b1.
    pose proof (@bidx_lt Fq2 fone Fq2_dec (skipn n1 bq)) as b2. rewrite length_skipn in b2.
    replace (Nat.min n1 (List.length bq)) with n1 in b1 by lia. replace (List.length bq - n1)%nat with ell in b2 by lia.
    rewrite <-to_F_zero, !map_nth. f_equal.
    apply nth_concat_uniform; [exact hl | exact b1 | lia].
  Qed.

  Theorem xdec_derive_sound : forall vals, xdec_derive = Some vals -> map to_F vals = valsDF /\ PreAccDF.
  Proof.
    intros vals h. unfold xdec_derive in h. destruct dshapes_ok eqn:hs; [| discriminate].
    unfold dshapes_ok in hs. repeat rewrite andb_true_iff in hs.
    destruct hs as (((((((((((hzG & hzT) & h1) & h0) & h2) & hts) & htl) & hb) & hmG) & hmT) & hnG) & hnT).
    apply Nat.eqb_eq in hzG, hzT, h1, h0, h2, hts, hb.
    rewrite forallb_forall in htl, hmG, hmT.
    assert (htl' : forall l, In l tsx -> List.length l = N) by (intros l hl; apply Nat.eqb_eq, htl, hl).
    assert (fa : forall ms : list (list xf), (forall ev, In ev ms -> Nat.leb (List.length ev) DMAX = true) ->
                 Forall (fun ev => (List.length ev <= DMAX)%nat) ms)
      by (intros ms hms; apply Forall_forall; intros ev hev; apply Nat.leb_le, hms, hev).
    destruct (xsc_verify mG rz claimGx) as [clG |] eqn:eG; [| discriminate].
    destruct (xsc_verify mT rt claimTx) as [clT |] eqn:eT; [| discriminate].
    injection h as <-.
    pose proof (accepted_coef _ _ _ _ (fa _ hmG) eG) as rG.
    pose proof (accepted_coef _ _ _ _ (fa _ hmT) eT) as rT.
    assert (hrunG : @runG Fq2 fzero fone fadd fmul Fq2_dec dts GGGF stratGF wD = Some (to_F clG)).
    { unfold DecSound.runG, DecSound.wTh, DecSound.wcG, DecSound.wrG, wD. cbn [fst snd].
      unfold stratGF. rewrite <-rG. f_equal.
      unfold ZeroTest.claimZ, ZeroTest.rhoOf, claimGx, GGGF. rewrite to_F_mul, to_F_kk, Hdts. reflexivity. }
    assert (hrunT : @runT Fq2 fzero fone fadd fmul Fq2_dec stab etab GGTF stratTF wD = Some (to_F clT)).
    { unfold DecSound.runT, DecSound.wcT, DecSound.wrT, wD. cbn [fst snd].
      unfold stratTF. rewrite <-rT. f_equal.
      unfold ZeroTest.claimZ, ZeroTest.rhoOf, claimTx, GGTF. rewrite to_F_mul, to_F_kk. reflexivity. }
    split.
    + unfold valsDF, DecSound.valsD. rewrite hrunG, hrunT. cbn [DecSound.unoptD].
      cbn [map app]. rewrite !map_app. cbn [map app].
      unfold DecSound.zG, DecSound.zT, zsGF, zsTF, DecSound.wTh.
      f_equal; [apply VD_value; assumption |]. f_equal.
      { unfold VKx, VKF, wD, DecLayout.VKv. cbn [fst snd]. rewrite to_F_dot, to_F_eq_table, h2. reflexivity. }
      f_equal. f_equal.
      unfold DecSound.fGv, DecSound.fTv, DecSound.zG, DecSound.zT, DecSound.wTh, DecSound.wcG, DecSound.wrG,
        DecSound.wcT, DecSound.wrT, wD, zsGF, zsTF. cbn [fst snd].
      unfold ZeroTest.ksOf, ZeroTest.rhoOf. rewrite Hdts. cbn [List.length].
      rewrite !to_F_mul, !to_F_sub, !to_F_inv, !to_F_kk. unfold fGx, fTx.
      rewrite !to_F_mul, !to_F_eq_eval.
      rewrite (to_F_innerZ (xrangep base) phiR) by apply to_F_rangep.
      rewrite (to_F_innerZ xcube3 (@phi3 Fq2 fzero fone fopp)) by apply to_F_cube_phi3.
      cbn [snd]. rewrite <-!firstn_map. reflexivity.
    + unfold PreAccDF, DecSound.PreAccD, DecSound.LenD, DecSound.zG, DecSound.zT, zsGF, zsTF.
      rewrite hrunG, hrunT. rewrite !length_map, hzG, hzT, Hdts.
      unfold DecSound.wcG, DecSound.wcT, wD, ZeroTest.rhoOf. cbn [fst snd List.length]. rewrite Hdts.
      repeat split; try discriminate.
      * rewrite <-to_F_nth. apply xnz_sound. exact hnG.
      * rewrite <-to_F_nth. apply xnz_sound. exact hnT.
  Qed.

End Derive.

(* ---------------------------------------------------------------------- *)
(* the verifier *)

Record dfront : Type := mk_dfront {
  dth : list xf; dth1 : list xf; dth2 : list xf; dtz : list xf; dkG : list xf; drz : list xf;
  dtt : list xf; dkT : list xf; drt : list xf;
  dGG : xf; dGT : xf; dmG : list (list xf); dzG : list xf; dmT : list (list xf); dzT : list xf;
  dkp : list xf; dc : xf; dgB : list xf; dgS : list xf; dJB : list nat; dJS : list nat;
  dmu : xf; dub : nat -> list xf; dpvB : list xf; dpvS : list xf; dXe : nat -> nat -> xf
}.

Section DecVerify.

  Variables n1 ell lo1 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Local Notation m := (n1 + ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.

  Definition rwX : nat := rwD n1 ell lo1.
  Definition SOX : nat := (kd * rwX + 6)%nat.
  Definition dGX : list nat := map (fun i => if Nat.eqb (S i) m then (2 * base + 1)%nat else (base + 1)%nat) (seq 0 m).
  Definition dTX : list nat := map (fun i => if Nat.eqb (S i) n1 then 7%nat else 4%nat) (seq 0 n1).
  Definition aDX : list xf := map bx a.
  Definition bDX : list xf := map bx b.
  Definition usX : list (list xf) := map (map bx) us.
  Definition tsX : list (list xf) := map (map bx) ts.

  Definition mcbX (v : nat) : list (nat * xf) :=
    match v with
    | 1 => [((kd * rwX)%nat, xone); ((kd * rwX + 1)%nat, xtg)]
    | 2 => [((kd * rwX + 2)%nat, xone); ((kd * rwX + 3)%nat, xtg)]
    | 3 => [((SOX + 3)%nat, xone); ((SOX + 4)%nat, xtg)]
    | 4 => [((SOX + 5)%nat, xone); ((SOX + 6)%nat, xtg)]
    | _ => [((SOX + 7)%nat, xone); ((SOX + 8)%nat, xtg)]
    end.
  Definition rwsBX : list nat := seq 0 (kd * rwX + 4).
  Definition rwsSX : list nat := map (fun i => (SOX + i)%nat) (seq 0 9).

  Section Back.
    Variable f : dfront.
    Definition ptX : list xf := dth1 f ++ dth f.
    Definition clsX : list (list xterm) :=
      xclaimsD n1 ell lo1 SOX kd base aDX (bx pplain) usX dGX dTX ptX (dth2 f) (drz f) (drt f).
    Definition LtX (v : nat) : list xf := if Nat.eqb v 1 then xlo_vec lo1 ptX else xlo_vec lo1 (drz f).
    Definition xmpBX (j : nat) : xf := xadd (dXe f (kd * rwX + 4) j) (xmul xtg (dXe f (kd * rwX + 5) j)).
    Definition xmpSX (j : nat) : xf := xadd (dXe f (SOX + 9) j) (xmul xtg (dXe f (SOX + 10) j)).

    Definition derivedX : option (list xf) :=
      xdec_derive n1 ell kd base bDX (bx pplain) (bx off) tsX (dth f) (dth1 f) (dth2 f) (dtz f) (dkG f) (drz f)
                  (dtt f) (dkT f) (drt f) (dGG f) (dGT f) (dmG f) (dmT f) (dzG f) (dzT f).

    Definition openX (vals : list xf) : bool :=
      xaccO (dXe f) (bx omB) (bx omS) nB nS kB kS xmpBX xmpSX rwsBX rwsSX kindD (frowD SOX) LtX mcbX
            [1; 2]%nat [3; 4; 5]%nat clsX vals (dkp f) (dc f) (dgB f) (dgS f) (dJB f) (dJS f) (dmu f) (dub f)
            (dpvB f) (dpvS f).

    Definition dlengths_ok : bool :=
      Nat.eqb (List.length (drz f)) m && Nat.eqb (List.length (drt f)) n1 && Nat.eqb (List.length (dth2 f)) n1
      && Nat.eqb (List.length (dth1 f)) n1 && Nat.eqb (List.length (dth f)) ell.

    Definition xdec_back : bool :=
      dlengths_ok && match derivedX with Some vals => openX vals | None => false end.
  End Back.

  (* the front end: transcript and Merkle paths, on the components of a proof *)
  Definition xred (x : xf) : bool := Z.leb 0 (fst x) && Z.ltb (fst x) Q && Z.leb 0 (snd x) && Z.ltb (snd x) Q.

  Definition ddigest : bytes := sha256 (flat_map ser_base (a ++ b ++ List.concat us ++ List.concat ts)).

  Definition xdec_front (root_big root_small : bytes) (G : list xf) (mG : list (list xf)) (zG : list xf)
    (mT : list (list xf)) (zT : list xf) (mu : xf) (vS1 vS2 vSs vSe vSm pvB pvS : list xf)
    (colsB colsS : list (list (list Z * bytes * list bytes))) : option dfront :=
    let allf := G ++ List.concat mG ++ zG ++ List.concat mT ++ zT ++ [mu] ++ vS1 ++ vS2 ++ vSs ++ vSe ++ vSm ++ pvB ++ pvS in
    if negb (forallb xred allf && Nat.eqb (List.length G) 2 && Nat.eqb (List.length zG) kd && Nat.eqb (List.length zT) 2
             && (if list_eq_dec Nat.eq_dec (map (@List.length xf) mG) dGX then true else false)
             && (if list_eq_dec Nat.eq_dec (map (@List.length xf) mT) dTX then true else false)) then None else
    let ch := fs_init (sb "dec") in
    let ch := absorb ch "params" tag in
    let ch := absorb ch "stmt" ddigest in
    let ch := absorb ch "round1" (root_big ++ root_small ++ ser_fs G) in
    bindo (get_F ch (sb "theta") ell) (fun q => let th := fst q in
    bindo (get_F (snd q) (sb "theta1") n1) (fun q => let th1 := fst q in
    bindo (get_F (snd q) (sb "theta2") n1) (fun q => let th2 := fst q in
    bindo (get_F (snd q) (sb "tz") m) (fun q => let tz := fst q in
    bindo (get_F (snd q) (sb "kG") kd) (fun q => let kG := fst q in
    bindo (get_F (snd q) (sb "rhoG") 1) (fun q => let rhoG := fst q in
    bindo (sc_chals "G" 0 mG (snd q)) (fun q => let rz := fst q in
    let ch := absorb (snd q) "evalsG" (ser_fs zG) in
    bindo (get_F ch (sb "tt") n1) (fun q => let tt := fst q in
    bindo (get_F (snd q) (sb "kT") 2) (fun q => let kT := fst q in
    bindo (get_F (snd q) (sb "rhoT") 1) (fun q => let rhoT := fst q in
    bindo (sc_chals "T" 0 mT (snd q)) (fun q => let rt := fst q in
    let ch := absorb (snd q) "evalsT" (ser_fs zT) in
    bindo (get_F ch (sb "pcs.kappa") (kd + 6)) (fun q => let kp := fst q in
    let ch := absorb (snd q) "pcs.mu" (ser_f mu) in
    bindo (get_F ch (sb "pcs.c") 1) (fun q => let c := nth 0 (fst q) xzero in
    bindo (get_F (snd q) (sb "pcs.gamma.big") (kd * rwX + 6)) (fun q => let gB := fst q in
    bindo (get_F (snd q) (sb "pcs.gamma.small") 11) (fun q => let gS := fst q in
    let ch := absorb (snd q) "pcs.vec" (ser_fs vS1 ++ ser_fs vS2 ++ ser_fs vSe ++ ser_fs vSm ++ ser_fs vSs
                                        ++ ser_fs pvB ++ ser_fs pvS) in
    bindo (get_I ch (sb "pcs.J.big") nqB (Z.of_nat nB)) (fun q => let JB := map Z.to_nat (fst q) in
    bindo (get_I (snd q) (sb "pcs.J.small") nqS (Z.of_nat nS)) (fun q => let JS := map Z.to_nat (fst q) in
    if negb (merkle_ok [root_big] JB colsB && merkle_ok [root_small] JS colsS) then None else
    let colB := map (fun bs => flat_map (fun it => fst (fst it)) bs) colsB in
    let colS := map (fun bs => flat_map (fun it => fst (fst it)) bs) colsS in
    let Xe i j := if Nat.ltb i SOX then bx (nth i (nth (idx_of JB j 0) colB []) 0%Z)
                  else bx (nth (i - SOX) (nth (idx_of JS j 0) colS []) 0%Z) in
    let ub v := match v with 1 => vS1 | 2 => vS2 | 3 => vSs | 4 => vSe | _ => vSm end in
    Some (mk_dfront th th1 th2 tz (kG ++ rhoG) rz tt (kT ++ rhoT) rt (nth 0 G xzero) (nth 1 G xzero)
                    mG zG mT zT kp c (firstn (kd * rwX + 4) gB) (firstn 9 gS) JB JS mu ub pvB pvS Xe)
    ))))))))))))))))).

  (* what acceptance of the back end implies *)
  Theorem xdec_back_sound : forall f (dts : list (list Fq2 -> Fq2)) (stab etab : list Fq2 -> Fq2),
    List.length dts = kd -> xdec_back f = true ->
    exists vals,
      map to_F vals
        = valsDF n1 ell kd base bDX (bx pplain) (bx off) tsX (dth f) (dth1 f) (dth2 f) (dtz f) (dkG f) (drz f)
                 (dtt f) (dkT f) (drt f) (dGG f) (dGT f) (dmG f) (dmT f) (dzG f) (dzT f) dts stab etab
      /\ PreAccDF kd (dth f) (dth1 f) (dth2 f) (dtz f) (dkG f) (drz f) (dtt f) (dkT f) (drt f) (dGG f) (dGT f)
                  (dmG f) (dmT f) (dzG f) (dzT f) dts stab etab
      /\ map (map tF) (clsX f)
         = @claimsD Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SOX kd base (map to_F aDX) (to_F (bx pplain))
                    (fun i => map to_F (nth i usX [])) dGX dTX (map to_F (ptX f)) (map to_F (dth2 f))
                    (map to_F (drz f)) (map to_F (drt f))
      /\ @AccO Fq2 fzero fone fadd fmul (to_F (bx omB)) (to_F (bx omS)) kB kS (fun i j => to_F (dXe f i j))
               rwsBX rwsSX (fun j => to_F (xmpBX f j)) (fun j => to_F (xmpSX f j)) (map to_F vals)
               (fun kp' => @Lk Fq2 fadd fmul kindD (fun v => map to_F (LtX f v)) kp' (map (map tF) (clsX f)))
               (fun kp' => @cbk Fq2 fone fmul kindD (frowD SOX) kp' (map (map tF) (clsX f)))
               (fun v => map pairF (mcbX v)) [1; 2]%nat [3; 4; 5]%nat
               (fun _ => to_F (dmu f)) (fun _ _ v => map to_F (dub f v)) (fun _ _ => map to_F (dpvB f))
               (fun _ _ => map to_F (dpvS f))
               (map to_F (dkp f)) (to_F (dc f), (map to_F (dgB f), map to_F (dgS f))) (dJB f, dJS f).
  Proof.
    intros f dts stab etab hd h. unfold xdec_back in h. apply andb_true_iff in h. destruct h as [hl h].
    destruct (derivedX f) as [vals |] eqn:ed; [| discriminate].
    exists vals.
    unfold dlengths_ok in hl. repeat rewrite andb_true_iff in hl.
    destruct hl as ((((hz & ht) & h2) & h1) & h0).
    apply Nat.eqb_eq in hz, ht, h2, h1, h0.
    destruct (xdec_derive_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dts stab etab hd vals ed) as [e1 e2].
    split; [exact e1 |]. split; [exact e2 |]. split.
    + apply to_F_claimsD; [unfold ptX; rewrite length_app; lia | exact h2 | exact hz | exact ht].
    + exact (xaccO_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h).
  Qed.

Definition xdec_verify root_big root_small G mG zG mT zT mu vS1 vS2 vSs vSe vSm pvB pvS colsB colsS : bool :=
  match xdec_front root_big root_small G mG zG mT zT mu vS1 vS2 vSs vSe vSm pvB pvS colsB colsS with
  | Some f => xdec_back f
  | None => false
  end.

  (* the byte format (dec_proof.py: dec_serialize, dec_deserialize) *)
  Local Notation "x <- o ;; f" := (bindo o (fun x => f)) (at level 61, o at next level, right associativity).

  Record dparts : Type := mk_dparts {
    proot_big : bytes; proot_small : bytes; pG : list xf; pmG : list (list xf); pzG : list xf;
    pmT : list (list xf); pzT : list xf; pmu : xf;
    pvS1 : list xf; pvS2 : list xf; pvSe : list xf; pvSm : list xf; pvSs : list xf; ppvB : list xf; ppvS : list xf;
    pcolsB : list (list (list Z * bytes * list bytes)); pcolsS : list (list (list Z * bytes * list bytes))
  }.

  Definition xdec_parse (prf : bytes) : option dparts :=
    p <- take 32 prf;; let rb := fst p in
    p <- take 32 (snd p);; let rs := fst p in
    p <- prep 2 pf (snd p);; let G := fst p in
    p <- pmsgs dGX (snd p);; let mG := fst p in
    p <- prep kd pf (snd p);; let zG := fst p in
    p <- pmsgs dTX (snd p);; let mT := fst p in
    p <- prep 2 pf (snd p);; let zT := fst p in
    p <- pf (snd p);; let mu := fst p in
    p <- prep kB pf (snd p);; let v1 := fst p in
    p <- prep kB pf (snd p);; let v2 := fst p in
    p <- prep kS pf (snd p);; let ve := fst p in
    p <- prep kS pf (snd p);; let vm := fst p in
    p <- prep kS pf (snd p);; let vs := fst p in
    p <- prep kB pf (snd p);; let pvB := fst p in
    p <- prep kS pf (snd p);; let pvS := fst p in
    p <- prep nqB (pbatches [(kd * rwX + 6)%nat] (log2n 64 nB)) (snd p);; let colsB := fst p in
    p <- prep nqS (pbatches [11%nat] (log2n 64 nS)) (snd p);; let colsS := fst p in
    if match snd p with [] => false | _ => true end then None else
    Some (mk_dparts rb rs G mG zG mT zT mu v1 v2 ve vm vs pvB pvS colsB colsS).

  Definition xdec_verify_bytes (prf : bytes) : bool :=
    match xdec_parse prf with
    | Some P => xdec_verify (proot_big P) (proot_small P) (pG P) (pmG P) (pzG P) (pmT P) (pzT P) (pmu P)
                  (pvS1 P) (pvS2 P) (pvSs P) (pvSe P) (pvSm P) (ppvB P) (ppvS P) (pcolsB P) (pcolsS P)
    | None => false
    end.

End DecVerify.
