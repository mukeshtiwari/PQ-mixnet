(* The sumcheck layer of mix_derive (mix_proof.py) as executable code: from
   the statement, the challenges and the prover's messages, the nine
   claimed values, or None if a check fails. And its refinement to vals9
   and PreAcc of MixSound.v.

   xderive checks what mix_derive checks before the opening: the shapes,
   the round checks of the three sumchecks (implicit in the evaluation
   form, Interp.v), and rho_A, rho_C <> 0. The challenges are inputs here;
   the transcript that produces them is separate.

   Theorem xderive_sound: if xderive returns Some vals, then, at GF(q^2),
   for the challenge tuple w made of these challenges and for the prover
   whose messages are these messages (constant strategies; the round
   messages as coefficient lists, Interp.coefmsgs),
     map to_F vals = vals9 w    and    PreAcc w,
   with the verifier's tables of ExecPublic.v (so Hver holds for them). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex Sumcheck SumcheckSound MixMultiset MixSummands MixSoundA MixSoundC MixSound Interp. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecOpen ExecPublic.
Import ListNotations.

Add Field fieldF2d : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation sc_run2 := (@sc_run Fq2 fzero fone fadd fmul Fq2_dec).
Local Notation sc_verify2 := (@Sumcheck.sc_verify Fq2 fzero fone fadd fmul Fq2_dec).
Local Notation coefmsgs2 := (@coefmsgs Fq2 fzero fone fadd fmul fsub fopp finv).

(* ---------------------------------------------------------------------- *)
(* tools *)

Definition xkk (l : list xf) (i : nat) : xf := nth i l xzero.

Lemma to_F_kk : forall l i, to_F (xkk l i) = @kk Fq2 fzero (map to_F l) i.
Proof. intros l i. unfold xkk, MixSoundC.kk. apply to_F_nth. Qed.

Fixpoint xidr (x : list xf) : xf :=
  match x with
  | [] => xzero
  | x0 :: xs => xadd x0 (xmul (xadd xone xone) (xidr xs))
  end.

Lemma to_F_idr : forall x, to_F (xidr x) = @idr Fq2 fzero fone fadd fmul (map to_F x).
Proof.
  induction x as [| x0 xs ih]; [exact to_F_zero |].
  cbn [xidr map CubeIndex.idr]. rewrite to_F_add, to_F_mul, to_F_add, to_F_one, ih. reflexivity.
Qed.

Definition xcube3 (w : xf) : xf := xsub (xmul (xmul w w) w) w.

Lemma to_F_cube3 : forall w, to_F (xcube3 w) = @cube3 Fq2 fmul fsub (to_F w).
Proof. intro w. unfold xcube3, MixSummands.cube3. rewrite to_F_sub, !to_F_mul. reflexivity. Qed.

(* x <> 0 in the field, tested on the reduced representative *)
Definition xnz (x : xf) : bool := negb (Z.eqb (fst x mod Q) 0 && Z.eqb (snd x mod Q) 0).

Lemma xnz_sound : forall x, xnz x = true -> to_F x <> fzero.
Proof.
  intros [a b] h e. unfold xnz in h. cbn [fst snd] in h.
  unfold to_F, fzero, ezero in e. cbn [fst snd] in e. injection e as e1 e2.
  rewrite e1, e2 in h. cbn in h. discriminate.
Qed.

Lemma skipn_nth_cons : forall {A : Type} (l : list A) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros A l; induction l as [| x l ih]; intros k d h; [cbn in h; lia |].
  destruct k as [| k]; [reflexivity |]. cbn [skipn nth]. apply ih. cbn in h. lia.
Qed.

(* a strategy that sends the messages of a list *)
Lemma sc_run_list : forall (cms : list (list Fq2)) chals pre claim,
  length cms = (length pre + length chals)%nat ->
  sc_run2 (fun p => nth (length p) cms []) pre chals claim = sc_verify2 (skipn (length pre) cms) chals claim.
Proof.
  intros cms; induction chals as [| r cs ih]; intros pre claim hl.
  + cbn [length] in hl. rewrite (skipn_all2 (n := length pre)) by lia. reflexivity.
  + cbn [SumcheckSound.sc_run].
    rewrite (skipn_nth_cons cms (length pre) []) by (cbn in hl; lia).
    cbn [Sumcheck.sc_verify].
    destruct (@feqb Fq2 Fq2_dec _ claim); [| reflexivity].
    rewrite ih by (rewrite length_app; cbn in hl |- *; lia).
    rewrite length_app. cbn [length]. rewrite Nat.add_1_r. reflexivity.
Qed.

Lemma xsc_verify_length : forall msgs chals claim c, xsc_verify msgs chals claim = Some c -> length msgs = length chals.
Proof.
  induction msgs as [| ev ms ih]; intros chals claim c h; destruct chals as [| r cs]; cbn in h; try discriminate;
    [reflexivity |].
  destruct ev; [discriminate |]. cbn. f_equal. exact (ih _ _ _ h).
Qed.

Lemma coefmsgs_length : forall msgs chals claim, length msgs = length chals -> length (coefmsgs2 msgs chals claim) = length msgs.
Proof.
  induction msgs as [| ev ms ih]; intros chals claim h; destruct chals as [| r cs]; cbn in h; try lia; [reflexivity |].
  cbn. f_equal. apply ih. lia.
Qed.

Definition DMAX : nat := 1000.

(* the coefficient lists behind accepted evaluation-form messages *)
Lemma accepted_coef : forall msgs chals claim c,
  Forall (fun ev => (length ev <= DMAX)%nat) msgs ->
  xsc_verify msgs chals claim = Some c ->
  sc_run2 (fun p => nth (length p) (coefmsgs2 (map (map to_F) msgs) (map to_F chals) (to_F claim)) [])
          [] (map to_F chals) (to_F claim) = Some (to_F c).
Proof.
  intros msgs chals claim c hl h.
  pose proof (xsc_verify_length _ _ _ _ h) as hlen.
  rewrite sc_run_list.
  + cbn [length skipn].
    assert (hl' : Forall (fun ev => (length ev <= DMAX)%nat) (map (map to_F) msgs)).
    { apply Forall_map. eapply Forall_impl; [| exact hl]. intros ev hev. rewrite length_map. exact hev. }
    exact (proj1 (@esc_sound Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field DMAX
                    (Fq2_char_upto DMAX ltac:(vm_compute; reflexivity)) _ _ _ _ hl' (to_F_sc_verify _ _ _ _ h))).
  + cbn [length]. rewrite coefmsgs_length by (rewrite !length_map; exact hlen). rewrite !length_map. exact hlen.
Qed.

Lemma map_nth_seq_list : forall {A B : Type} (f : A -> B) (d : A) (l : list A),
  map (fun i => f (nth i l d)) (seq 0 (length l)) = map f l.
Proof.
  intros A B f d l. rewrite <-(map_map (fun i => nth i l d) f). f_equal.
  apply nth_ext with (d := d) (d' := d); rewrite length_map, length_seq; [reflexivity |].
  intros i hi. rewrite (nth_indep _ d (nth 0 l d)) by (rewrite length_map, length_seq; exact hi).
  rewrite (map_nth (fun i => nth i l d) (seq 0 (length l)) 0%nat i), seq_nth by exact hi. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)

Section Derive.

  (* the statement *)
  Variables (a b : list xf) (pp : xf).
  Variables cinx coutx : list (list xf * list xf).
  Variables n1 ell : nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.

  (* the challenges *)
  Variables ru rv : list xf.
  Variables alpha beta : xf.
  Variables tc kA rA : list xf.
  Variable rhoB : xf.
  Variable ry : list xf.
  Variables tz kC rz : list xf.

  (* the prover's messages *)
  Variables GA GB GC : xf.
  Variable mA : list (list xf).
  Variables U Uh sv Hd : xf.
  Variables mB mC : list (list xf).
  Variables w1 w2 w3 : xf.

  Definition zpub : list xf := map (xproj ru rv) cinx.
  Definition zhat : list xf := map (xproj ru rv) coutx.

  Definition claimA : xf := xadd (xadd (xkk kA 0) (xkk kA 1)) (xmul (xkk kA 3) GA).
  Definition Hh : xf := xsub (xadd (xmle zhat rA) (xmul beta sv)) alpha.
  Definition fA : xf :=
    xadd (xmul (xeq_eval rA tc) (xadd (xmul (xkk kA 0) (xmul U Hd)) (xmul (xkk kA 1) (xmul Uh Hh))))
         (xmul (xkk kA 2) (xsub U Uh)).
  Definition claimB : xf :=
    xadd (xadd (xsub (xsub Hd (xmle zpub rA)) (xmul beta (xidr rA))) alpha) (xmul rhoB GB).
  Definition claimC : xf := xmul (xkk kC 3) GC.
  Definition fC : xf :=
    xmul (xeq_eval rz tz)
         (xadd (xadd (xmul (xkk kC 0) (xcube3 w1)) (xmul (xkk kC 1) (xcube3 w2))) (xmul (xkk kC 2) (xcube3 w3))).

  Definition shapes_ok : bool :=
    Nat.eqb (length ru) N && Nat.eqb (length rv) N && Nat.eqb (length cinx) tau && Nat.eqb (length coutx) tau
    && Nat.eqb (length rA) ell
    && forallb (fun ev => Nat.leb (length ev) DMAX) mA && forallb (fun ev => Nat.leb (length ev) DMAX) mB
    && forallb (fun ev => Nat.leb (length ev) DMAX) mC
    && xnz (xkk kA 3) && xnz (xkk kC 3).

  Definition xderive : option (list xf) :=
    if shapes_ok then
      match xsc_verify mA rA claimA, xsc_verify mB ry claimB, xsc_verify mC rz claimC with
      | Some clA, Some clB, Some clC =>
          Some [U; Uh; sv; clB; w1; w2; w3;
                xmul (xsub clA fA) (xinv (xkk kA 3)); xmul (xsub clC fC) (xinv (xkk kC 3))]
      | _, _, _ => None
      end
    else None.

  (* ------------------------------------------------------------------ *)
  (* the same at the field *)

  Definition aF : list Fq2 := map to_F a.
  Definition bF : list Fq2 := map to_F b.
  Definition cinF (i : nat) : @ctx Fq2 := ctxF (nth i cinx ([], [])).
  Definition coutF (j : nat) : @ctx Fq2 := ctxF (nth j coutx ([], [])).

  Local Notation zpT2 := (@zpT n1 ell cinF).
  Local Notation zhT2 := (@zhT n1 ell coutF).
  Local Notation alT2 := alT.
  Local Notation beT2 := (@beT n1).

  Definition c1F : list Fq2 := @point Fq2 (map to_F ru) (map to_F rv) (to_F alpha) (to_F beta).

  Definition wF : @Wm Fq2 :=
    (((c1F, ((map to_F tc, map to_F kA), map to_F rA)), (to_F rhoB, map to_F ry)),
     ((map to_F tz, map to_F kC), map to_F rz)).

  (* the prover: constant strategies *)
  Definition cmsA := coefmsgs2 (map (map to_F) mA) (map to_F rA) (to_F claimA).
  Definition cmsB := coefmsgs2 (map (map to_F) mB) (map to_F ry) (to_F claimB).
  Definition cmsC := coefmsgs2 (map (map to_F) mC) (map to_F rz) (to_F claimC).
  Definition stratA2 (_ : list Fq2) (_ : list Fq2 * list Fq2) (pre : list Fq2) : list Fq2 := nth (length pre) cmsA [].
  Definition stratB2 (_ : @P3 Fq2) (_ : Fq2) (pre : list Fq2) : list Fq2 := nth (length pre) cmsB [].
  Definition stratC2 (_ : @P5 Fq2) (_ : list Fq2 * list Fq2) (pre : list Fq2) : list Fq2 := nth (length pre) cmsC [].
  Definition cst3 (x : xf) (_ : list Fq2) (_ : list Fq2 * list Fq2) (_ : list Fq2) : Fq2 := to_F x.
  Definition cstP (x : xf) (_ : @P5 Fq2) (_ : list Fq2 * list Fq2) (_ : list Fq2) : Fq2 := to_F x.
  Definition cst1 (x : xf) (_ : list Fq2) : Fq2 := to_F x.

  Definition vals9F : list Fq2 :=
    @vals9 Fq2 fzero fone fadd fmul fsub finv Fq2_dec ell zpT2 zhT2 alT2 beT2 (cst1 GA) (cst1 GB) (cst1 GC)
           stratA2 (cst3 U) (cst3 Uh) (cst3 sv) (cst3 Hd) stratB2 stratC2 (cstP w1) (cstP w2) (cstP w3) wF.

  Definition PreAccF : Prop :=
    @PreAcc Fq2 fzero fone fadd fmul fsub Fq2_dec ell zpT2 alT2 beT2 (cst1 GA) (cst1 GB) (cst1 GC)
            stratA2 (cst3 Hd) stratB2 stratC2 wF.

  Lemma tables_mle : length ru = N -> length rv = N -> length cinx = tau -> length coutx = tau ->
    length rA = ell ->
    mle2 ell (zpT2 c1F) (map to_F rA) = to_F (xmle zpub rA) /\
    mle2 ell (zhT2 c1F) (map to_F rA) = to_F (xmle zhat rA).
  Proof.
    intros hu hv hci hco hr.
    destruct (point_fields n1 (map to_F ru) (map to_F rv) (to_F alpha) (to_F beta)
                ltac:(rewrite length_map; exact hu) ltac:(rewrite length_map; exact hv)) as (e1 & e2 & _ & _).
    fold c1F in e1, e2.
    rewrite to_F_mle by (unfold zpub; rewrite length_map, hci, hr; reflexivity).
    rewrite to_F_mle by (unfold zhat; rewrite length_map, hco, hr; reflexivity).
    rewrite hr. unfold ExecPublic.zpT, ExecPublic.zhT. rewrite e1, e2. split; f_equal; f_equal.
    + unfold zpub. rewrite map_map, <-hci. unfold cinF.
      rewrite (map_nth_seq_list (fun c => @proj Fq2 fzero fadd fmul (map to_F ru) (map to_F rv) (ctxF c)) ([], []) cinx).
      apply map_ext. intro c. symmetry. apply to_F_proj.
    + unfold zhat. rewrite map_map, <-hco. unfold coutF.
      rewrite (map_nth_seq_list (fun c => @proj Fq2 fzero fadd fmul (map to_F ru) (map to_F rv) (ctxF c)) ([], []) coutx).
      apply map_ext. intro c. symmetry. apply to_F_proj.
  Qed.

  Theorem xderive_sound : forall vals, xderive = Some vals -> map to_F vals = vals9F /\ PreAccF.
  Proof.
    intros vals h. unfold xderive in h.
    destruct shapes_ok eqn:hs; [| discriminate].
    unfold shapes_ok in hs. repeat rewrite andb_true_iff in hs.
    destruct hs as (((((((((hu & hv) & hci) & hco) & hr) & hmA) & hmB) & hmC) & hnA) & hnC).
    apply Nat.eqb_eq in hu, hv, hci, hco, hr.
    rewrite forallb_forall in hmA, hmB, hmC.
    assert (fA' : forall ms : list (list xf), (forall ev, In ev ms -> Nat.leb (length ev) DMAX = true) ->
                  Forall (fun ev => (length ev <= DMAX)%nat) ms).
    { intros ms hms. apply Forall_forall. intros ev hev. apply Nat.leb_le. apply hms. exact hev. }
    destruct (xsc_verify mA rA claimA) as [clA |] eqn:eA; [| discriminate].
    destruct (xsc_verify mB ry claimB) as [clB |] eqn:eB; [| discriminate].
    destruct (xsc_verify mC rz claimC) as [clC |] eqn:eC; [| discriminate].
    injection h as <-.
    pose proof (accepted_coef _ _ _ _ (fA' _ hmA) eA) as rA'.
    pose proof (accepted_coef _ _ _ _ (fA' _ hmB) eB) as rB'.
    pose proof (accepted_coef _ _ _ _ (fA' _ hmC) eC) as rC'.
    destruct (tables_mle hu hv hci hco hr) as [mzp mzh].
    destruct (point_fields n1 (map to_F ru) (map to_F rv) (to_F alpha) (to_F beta)
                ltac:(rewrite length_map; exact hu) ltac:(rewrite length_map; exact hv)) as (_ & _ & e3 & e4).
    fold c1F in e3, e4.
    (* the three runs *)
    assert (hrunA : @runA Fq2 fzero fone fadd fmul Fq2_dec (cst1 GA) stratA2 wF = Some (to_F clA)).
    { unfold MixSound.runA, MixSound.w1, MixSound.w2, MixSound.wA, wF. cbn [fst snd].
      unfold stratA2. rewrite <-rA'. f_equal.
      unfold claimA. rewrite !to_F_add, to_F_mul, !to_F_kk. reflexivity. }
    assert (hrunB : @runB Fq2 fzero fone fadd fmul fsub Fq2_dec ell zpT2 alT2 beT2 (cst1 GB) (cst3 Hd) stratB2 wF
                    = Some (to_F clB)).
    { unfold MixSound.runB, MixSound.w1, MixSound.w2, MixSound.wA, MixSound.wB, MixSound.wY, wF. cbn [fst snd].
      unfold stratB2. rewrite <-rB'. f_equal.
      unfold claimB, cst3, cst1. rewrite e3, e4, mzp.
      rewrite !to_F_add, !to_F_sub, !to_F_mul, to_F_idr. reflexivity. }
    assert (hrunC : @runC Fq2 fzero fone fadd fmul Fq2_dec (cst1 GC) stratC2 wF = Some (to_F clC)).
    { unfold MixSound.runC, MixSound.w1, MixSound.w4, MixSound.wZ, wF. cbn [fst snd].
      unfold stratC2. rewrite <-rC'. f_equal.
      unfold claimC, cst1. rewrite to_F_mul, to_F_kk. reflexivity. }
    split.
    + unfold vals9F, MixSound.vals9. rewrite hrunA, hrunB, hrunC. cbn [MixSound.unopt map].
      unfold MixSound.fAv, MixSound.fCv, MixSound.w1, MixSound.w2, MixSound.wA, MixSound.w4, MixSound.wZ, wF.
      cbn [fst snd]. unfold cst3, cstP.
      unfold fA, fC, Hh.
      repeat progress (rewrite ?to_F_add, ?to_F_mul, ?to_F_sub, ?to_F_inv, ?to_F_kk, ?to_F_cube3, ?to_F_eq_eval).
      rewrite e3, e4, mzh. reflexivity.
    + unfold PreAccF, MixSound.PreAcc. rewrite hrunA, hrunB, hrunC.
      unfold MixSound.w2, MixSound.w4, wF. cbn [fst snd].
      repeat split; try discriminate.
      - rewrite <-to_F_kk. apply xnz_sound. exact hnA.
      - rewrite <-to_F_kk. apply xnz_sound. exact hnC.
  Qed.

End Derive.
