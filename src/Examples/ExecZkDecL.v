(* The extracted decryption prover against the zero-knowledge model (zero knowledge for the running code,
   decryption proof; the counterpart of ExecZkTables.v and ExecZkMsgs.v for the shuffle).

   The model (ZkDecLayer.v, ZkDecOpen.v, ZkDecJoin.v) reads its tables off witness rows dB, sRow, eRow.
   Here these rows are the data parts of the prover's committed rows (dBr, sRowZ, eRowZ), and:

     digW_tab, stabW_pt, etabW_pt   the model's tables are the prover's tables on the cube;
     SfullG, SfullT                 the masked summands of the prover's tables are the model's fG, fT;
     msgsG_run, msgsT_run           the sumcheck messages of a run are the model's honest messages. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckMask MaskedExt RowLayout
  SlotKinds ZeroTest DecSound DecLayout ZkSumcheck ZkTranscript ZkDecLayer.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecDerive ExecVerify
  ExecProveBase ExecSerial ExecFold ExecRows ExecDec ExecDecProve ExecDecComplete ZkOpenMix ZkDecOpen ZkDecJoin ExecZkSC.
From Examples Require ExecZkTables ExecZkMain.
From Crypto Require ZkMix.
Import ListNotations.

Add Field fieldF2zd : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation pevalF := (@PolyRoots.eval Fq2 fzero fadd fmul).
Local Notation fsumF := (@LogDer.fsum Fq2 fzero fadd).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation tabOf := ExecPublic.tabOf.
Local Notation nF := (@nF Fq2 fzero fone fadd).
Local Notation p2F := (@p2 Fq2 fone fadd fmul).
Local Notation WF := (@W Fq2 fzero fone fadd fmul).
Local Notation evsF := (@ZkMix.evs Fq2 fzero fone fadd fmul fsub).
Local Notation phiR := (fun base => @rangep Fq2 fzero fone fadd fmul fopp base).

(* the expanded range polynomial is the range polynomial, at every point of F *)
Lemma peval_rcoefs_F : forall k y, pevalF (map to_F (xrcoefs k)) y = pevalF (phiR k) y.
Proof.
  induction k as [| k ih]; intro y.
  - cbn. rewrite to_F_one. field.
  - cbn [xrcoefs]. rewrite to_F_padd, to_F_pscale.
    rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
            (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (@rangep_eval Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field k y).
    cbn [map PolyRoots.eval]. rewrite ih, to_F_neg, to_F_zero, to_F_xint_nat. field.
Qed.

Lemma inner_seq : forall M (phi : list F) (ks : list F) (Ts : list (list F -> F)) (avs : list F) x n,
  List.length ks = n -> List.length Ts = n -> List.length avs = n ->
  @inner Fq2 fzero fone fadd fmul fsub M phi ks Ts avs x
  = fsumF (map (fun d => fmul (nth d ks fzero) (pevalF phi (@mstar Fq2 fzero fone fadd fmul fsub M (nth d Ts (fun _ => fzero)) (nth d avs fzero) x)))
               (seq 0 n)).
Proof.
  intros M phi ks; induction ks as [| k0 ks ih]; intros Ts avs x n h1 h2 h3.
  - subst n. reflexivity.
  - destruct Ts as [| T Ts]; [cbn in *; lia |]. destruct avs as [| a0 avs]; [cbn in *; lia |].
    subst n. cbn [List.length inner seq map LogDer.fsum nth]. rewrite (ih Ts avs x (List.length ks)) by (cbn in *; lia).
    rewrite <-seq_shift, map_map. reflexivity.
Qed.

Section DL.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k : dcoins.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation rw := (rwX n1 ell lo1).

  Hypothesis Hp : dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS.
  Hypothesis Hk : dcok n1 ell lo1 lo2 kd base nB nqB nS nqS k.
  Hypothesis Hw : dwshape n1 ell s e E.

  (* the witness rows of the model: the data parts of the prover's committed rows *)
  Definition digrows : list (list Z) := flat_map (fun d => split_rows C1 (Tdig base off E d)) (seq 0 kd).
  Definition dBr (i : nat) : list Zq := map zq_of (padrow C1 (nth i digrows []) []).
  Definition sRowZ : list Zq := map zq_of (padrow C2 (sZ s) []).
  Definition eRowZ : list Zq := map zq_of (padrow C2 (eZ e) []).
  Definition PwD : nat -> list F := P0 n1 ell lo1 kd dBr (dSw lo2 sRowZ eRowZ).
  Definition dtsW : list (list F -> F) := @dtsT Fq2 fzero fone Fq2_dec PwD n1 ell lo1 kd.
  Definition stabW : list F -> F := @stabT Fq2 fzero fone Fq2_dec PwD SO.
  Definition etabW : list F -> F := @etabT Fq2 fzero fone Fq2_dec PwD SO.

  Lemma map_emb_zq : forall l : list Z, map emb (map zq_of l) = map to_F (map bx l).
  Proof. intro l. rewrite !map_map. apply map_ext. intro z. symmetry. apply emb_bx. Qed.

  Lemma digrows_nth : forall d t, (d < kd)%nat -> (t < rw)%nat ->
    nth (d * rw + t) digrows [] = nth t (split_rows C1 (Tdig base off E d)) [].
  Proof.
    intros d t hd ht. unfold digrows. rewrite flat_map_concat_map.
    rewrite (Nat.add_comm (d * rw) t), (Nat.mul_comm d rw).
    rewrite (ExecDec.nth_concat_uniform _ rw t d []).
    - rewrite nth_map_seq0 by exact hd. reflexivity.
    - intros l hl. apply in_map_iff in hl. destruct hl as (d' & <- & _). exact (proj1 (dig_split n1 ell lo1 base off s e E Hw d')).
    - exact ht.
    - rewrite length_map, length_seq. exact hd.
  Qed.

  Lemma PwD_dig : forall d t, (d < kd)%nat -> (t < rw)%nat ->
    PwD (d * rw + t) = map to_F (map bx (padrow C1 (nth t (split_rows C1 (Tdig base off E d)) []) [])).
  Proof.
    intros d t hd ht. unfold PwD, P0. destruct (Nat.ltb_spec (d * rw + t) (kd * rwD n1 ell lo1 + 6)) as [_ | h];
      [| unfold rwX in *; nia].
    unfold ZkDecOpen.datasB. rewrite nth_map_seq0 by (unfold rwX in *; nia).
    unfold dBr. rewrite map_emb_zq, digrows_nth by assumption. reflexivity.
  Qed.

  Lemma digW_tab : forall d X, (d < kd)%nat -> (X < 2 ^ m)%nat ->
    nth d dtsW (fun _ => fzero) (pt2 m X) = to_F (bx (nth X (Tdig base off E d) 0%Z)).
  Proof.
    intros d X hd hX. unfold dtsW, dtsT. rewrite nth_map_seq0 by exact hd. unfold digT.
    apply (rdtab_list PwD (d * rwD n1 ell lo1) m lo1 (Tdig base off E d) (fun _ => []));
      [apply (Tdig_len' n1 ell base off s e E Hw) | | exact hX].
    intros t ht. exact (PwD_dig d t hd ht).
  Qed.

  Lemma rowW : forall j x, (j < 2)%nat -> (x < N)%nat ->
    nth x (PwD (SO + j)) fzero = to_F (bx (nth x (nth j [s; e] []) 0%Z)).
  Proof.
    intros j x hj hx. destruct Hw as (_ & _ & hs & he).
    unfold PwD, P0. destruct (Nat.ltb_spec (SO + j) (kd * rwD n1 ell lo1 + 6)) as [h | _]; [unfold SOX, rwX in h; lia |].
    unfold ZkDecOpen.datasS. replace (SO + j - (kd * rwD n1 ell lo1 + 6))%nat with j by (unfold SOX, rwX; lia).
    rewrite nth_map_seq0 by lia. unfold dSw.
    rewrite (nth_map_dflt emb _ x qzero fzero) by (unfold emb, fzero, ezero; reflexivity).
    destruct j as [| [| j]]; try lia; cbn [Nat.eqb nth]; [unfold sRowZ, sZ | unfold eRowZ, eZ];
      rewrite (nth_map_dflt zq_of _ x 0%Z qzero) by (apply zq_of_0);
      rewrite nth_padrow by (rewrite length_map; lia);
      rewrite (nth_map_dflt zm _ x 0%Z 0%Z eq_refl), <-emb_bx, !to_F_bx_zm; reflexivity.
  Qed.

  Lemma stabW_pt : forall x, (x < N)%nat -> stabW (pt2 n1 x) = to_F (bx (nth x s 0%Z)).
  Proof.
    intros x hx. unfold stabW, stabT, rS.
    rewrite (@rowT_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PwD n1 SO x hx).
    rewrite <-(Nat.add_0_r SO), (rowW 0 x) by lia. reflexivity.
  Qed.

  Lemma etabW_pt : forall x, (x < N)%nat -> etabW (pt2 n1 x) = to_F (bx (nth x e 0%Z)).
  Proof.
    intros x hx. unfold etabW, etabT, rE.
    rewrite (@rowT_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PwD n1 (SO + 1) x hx).
    rewrite (rowW 1 x) by lia. reflexivity.
  Qed.

  (* the masked summands of the prover's tables are the model's *)
  Theorem SfullG : forall tz kG x, List.length x = m -> List.length tz = m -> List.length kG = kd ->
    Sfull (map sF (termsG kd base kG)) m (tablesG kd base off E tz) (mF (tmaskG kd k)) x
    = @fG Fq2 fzero fone fadd fmul fsub fopp n1 ell base dtsW (map to_F tz) (map to_F kG) (map to_F (dmask k)) x.
  Proof.
    intros tz kG x hx htz hkG. pose proof Hk as (_ & _ & _ & hm & _).
    assert (hadl : List.length (a_dig kd k) = kd) by (unfold a_dig; rewrite length_firstn, hm; unfold n_maskD; lia).
    unfold Sfull. rewrite termsG_val. unfold fG, gZ.
    rewrite (inner_seq m _ (map to_F kG) dtsW (firstn (List.length dtsW) (map to_F (dmask k))) x kd).
    2: rewrite length_map; exact hkG.
    2: unfold dtsW, dtsT; rewrite length_map, length_seq; reflexivity.
    2: unfold dtsW, dtsT; rewrite length_map, length_seq, length_firstn, length_map, hm; unfold n_maskD; lia.
    assert (hlT : List.length (tablesG kd base off E tz) = S kd)
      by (unfold tablesG; cbn [List.length]; rewrite length_map, length_seq; reflexivity).
    assert (hlM : List.length (mF (tmaskG kd k)) = S kd)
      by (unfold mF, tmaskG; cbn [List.length map]; rewrite !length_map, hadl; reflexivity).
    assert (hv : forall j, (j < S kd)%nat ->
      nth j (map (fun p : list xf * option F => fadd (mle2 m (tabOf (map to_F (fst p))) x) (fmul (mval (snd p)) (Zp2 x)))
                 (combine (tablesG kd base off E tz) (mF (tmaskG kd k)))) fzero
      = fadd (mle2 m (tabOf (map to_F (nth j (tablesG kd base off E tz) []))) x) (fmul (mval (nth j (mF (tmaskG kd k)) None)) (Zp2 x))).
    { intros j hj. rewrite (ExecZkTables.nth_map_combine _ _ _ [] None fzero j) by lia. reflexivity. }
    rewrite (hv 0%nat) by lia.
    assert (h0 : fadd (mle2 m (tabOf (map to_F (nth 0 (tablesG kd base off E tz) []))) x) (fmul (mval (nth 0 (mF (tmaskG kd k)) None)) (Zp2 x))
                 = eqp2 x (map to_F tz)).
    { cbn [nth tablesG]. unfold mF, tmaskG. cbn [map nth option_map mval].
      rewrite <-htz at 1. rewrite ExecZkTables.mle_eqtab by lia. field. }
    rewrite h0.
    match goal with |- _ = fadd ?A _ => transitivity A; [| field] end.
    f_equal. f_equal. apply map_ext_in. intros d hd. apply in_seq in hd.
    rewrite (hv (S d)) by lia. rewrite <-to_F_nth, peval_rcoefs_F. f_equal. f_equal.
    unfold mstar. f_equal.
    - cbn [nth tablesG]. rewrite nth_map_seq0 by lia.
      apply ExecZkTables.mle_tab_ext. intros i hi.
      rewrite digW_tab by lia. rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero), (nth_map_dflt bx _ i 0%Z xzero eq_refl).
      reflexivity.
    - f_equal. unfold mF, tmaskG. cbn [map nth].
      rewrite (nth_indep (map (option_map to_F) (map Some (a_dig kd k))) None (option_map to_F (Some xzero)))
        by (rewrite !length_map, hadl; lia).
      rewrite !map_map. rewrite (map_nth (fun x0 => option_map to_F (Some x0)) _ xzero). cbn [option_map mval].
      unfold dtsW, dtsT. rewrite length_map, length_seq. rewrite nth_firstn. destruct (Nat.ltb_spec d kd) as [_ | h]; [| lia].
      unfold a_dig. rewrite nth_firstn. destruct (Nat.ltb_spec d kd) as [_ | h]; [| lia].
      rewrite to_F_nth. reflexivity.
  Qed.

  Theorem SfullT : forall tt kT x, List.length x = n1 -> List.length tt = n1 -> List.length kT = 2%nat ->
    Sfull (map sF (termsT kT)) n1 (tablesT s e tt) (mF (tmaskT kd k)) x
    = @fT Fq2 fzero fone fadd fmul fsub fopp n1 dtsW stabW etabW (map to_F tt) (map to_F kT) (map to_F (dmask k)) x.
  Proof.
    intros tt kT x hx htt hkT. pose proof Hk as (_ & _ & _ & hm & _).
    destruct kT as [| k0 [| k1 [| ]]]; cbn in hkT; try lia.
    unfold Sfull, fT, gZ. unfold tablesT, mF, tmaskT, termsT. cbn [map combine fst snd].
    unfold dtsW, dtsT. rewrite length_map, length_seq.
    cbn [inner map nth]. unfold mstar. unfold termsF, termF. cbn.
    assert (hsk2 : forall (l : list xf) j, (j + 2 <= List.length l)%nat ->
                     skipn j l = nth j l xzero :: nth (j + 1) l xzero :: skipn (j + 2) l).
    { induction l as [| a0 l ih]; intros j hj; [cbn in hj; lia |]. destruct j as [| j].
      - destruct l as [| a1 l]; [cbn in hj; lia | reflexivity].
      - cbn [skipn nth Nat.add]. apply ih. cbn in hj; lia. }
    rewrite skipn_map, (hsk2 (dmask k) kd) by (rewrite hm; unfold n_maskD; lia). cbn [map].
    fold (a_s kd k). replace (nth (kd + 1) (dmask k) xzero) with (a_e kd k) by reflexivity.
    assert (heq : mle2 n1 (tabOf (map to_F (xeq_table tt))) x = eqp2 x (map to_F tt))
      by (rewrite <-htt; apply ExecZkTables.mle_eqtab; lia).
    rewrite !heq.
    rewrite (ExecZkTables.mle_tab_ext n1 (map to_F (map bx (sZ s))) stabW),
            (ExecZkTables.mle_tab_ext n1 (map to_F (map bx (eZ e))) etabW).
    2:{ intros i hi. rewrite etabW_pt by lia. unfold eZ.
        rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero), (nth_map_dflt bx _ i 0%Z xzero eq_refl),
                (nth_map_dflt zm _ i 0%Z 0%Z eq_refl). apply to_F_bx_zm. }
    2:{ intros i hi. rewrite stabW_pt by lia. unfold sZ.
        rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero), (nth_map_dflt bx _ i 0%Z xzero eq_refl),
                (nth_map_dflt zm _ i 0%Z 0%Z eq_refl). apply to_F_bx_zm. }
    rewrite !to_F_neg. field.
  Qed.

  (* the sumcheck messages of a run are the model's honest messages *)
  Hypothesis Hn1 : (1 <= n1)%nat.
  Hypothesis HbaseQ : (Z.of_nat (Nat.max (2 * base + 2) 8) < Q)%Z.

  Local Notation avsW := (map to_F (dmask k)).
  Local Notation gGx := (gGD n1 ell kd base k).
  Local Notation gTx := (gTD n1 ell kd base k).
  Local Notation hmsgF := (@hmsg Fq2 fzero fone fadd fmul).

  Lemma HcharW : forall j, (0 < j <= Nat.max (2 * base + 2) 8)%nat -> nF j <> fzero.
  Proof. intros j hj. apply Fq2_char. lia. Qed.

  Theorem msgsG_run : forall tz kG rho mG rz finG c0 c1,
    List.length tz = m -> List.length kG = kd ->
    sc_loop (fun c nm => get_F c nm 1) "G" (tmaskG kd k) (termsG kd base kG) (fst gGx) (snd gGx)
            rho (dGX n1 ell base) 0 (tablesG kd base off E tz) [] c0 = Some (mG, rz, finG, c1) ->
    forall i, (i < m)%nat ->
      map to_F (nth i mG []) =
      map (fun c => pevalF (hmsgF m (@pfG Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dtsW (map to_F tz) (map to_F kG) avsW)
                                  (to_F rho) (to_F (fst gGx)) (csF (snd gGx)) (map to_F rz) i) (nF c))
          (spoints (nth i (dGX n1 ell base) 0%nat)).
  Proof.
    intros tz kG rho mG rz finG c0 c1 htz hkG H i hi.
    pose proof Hk as (_ & _ & _ & hm & _).
    assert (hrz : List.length rz = m) by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); cbn; apply dGX_len).
    pose proof (sc_msgs_hmsg (fun c nm => get_F c nm 1) "G"%string (tmaskG kd k) (termsG kd base kG) (fst gGx) (snd gGx)
             rho (dGX n1 ell base) (tablesG kd base off E tz) c0 mG rz finG c1
             (@fG Fq2 fzero fone fadd fmul fsub fopp n1 ell base dtsW (map to_F tz) (map to_F kG) avsW)
             (@pfG Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dtsW (map to_F tz) (map to_F kG) avsW)) as hM.
    rewrite !dGX_len in hM. apply hM; clear hM.
    - intro ec. pose proof (f_equal (@List.length nat) ec) as e'. rewrite dGX_len in e'. cbn in e'. lia.
    - exact (proj1 (gG_shape n1 ell kd base k)).
    - unfold tablesG, tmaskG. cbn [List.length]. rewrite !length_map, length_seq.
      unfold a_dig. rewrite length_firstn, hm. unfold n_maskD. lia.
    - discriminate.
    - unfold tablesG. constructor.
      + rewrite xeq_table_length, htz. reflexivity.
      + apply Forall_map, Forall_forall. intros d _. rewrite length_map. apply (Tdig_len' n1 ell base off s e E Hw).
    - exact H.
    - intros x hx. apply SfullG; assumption.
    - intros j X hj.
      exact (@dec_HpfG Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field n1 ell base Hn1 HcharW dtsW
               (map to_F tz) (map to_F kG) (map to_F rz) (repeat fzero n1)
               ltac:(rewrite length_map; exact hrz) (repeat_length _ _) avsW j X hj).
    - exact hi.
  Qed.

  Theorem msgsT_run : forall tt kT rho mT rt finT c0 c1,
    List.length tt = n1 -> List.length kT = 2%nat ->
    sc_loop (fun c nm => get_F c nm 1) "T" (tmaskT kd k) (termsT kT) (fst gTx) (snd gTx)
            rho (dTX n1) 0 (tablesT s e tt) [] c0 = Some (mT, rt, finT, c1) ->
    forall i, (i < n1)%nat ->
      map to_F (nth i mT []) =
      map (fun c => pevalF (hmsgF n1 (@pfT Fq2 fzero fone fadd fmul fsub fopp finv n1 dtsW stabW etabW (map to_F tt) (map to_F kT) avsW)
                                  (to_F rho) (to_F (fst gTx)) (csF (snd gTx)) (map to_F rt) i) (nF c))
          (spoints (nth i (dTX n1) 0%nat)).
  Proof.
    intros tt kT rho mT rt finT c0 c1 htt hkT H i hi.
    pose proof Hw as (_ & _ & hs & he).
    assert (hrt : List.length rt = n1) by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H); cbn; apply dTX_len).
    pose proof (sc_msgs_hmsg (fun c nm => get_F c nm 1) "T"%string (tmaskT kd k) (termsT kT) (fst gTx) (snd gTx)
             rho (dTX n1) (tablesT s e tt) c0 mT rt finT c1
             (@fT Fq2 fzero fone fadd fmul fsub fopp n1 dtsW stabW etabW (map to_F tt) (map to_F kT) avsW)
             (@pfT Fq2 fzero fone fadd fmul fsub fopp finv n1 dtsW stabW etabW (map to_F tt) (map to_F kT) avsW)) as hM.
    rewrite !dTX_len in hM. apply hM; clear hM.
    - intro ec. pose proof (f_equal (@List.length nat) ec) as e'. rewrite dTX_len in e'. cbn in e'. lia.
    - exact (proj1 (gT_shape n1 ell kd base k)).
    - reflexivity.
    - discriminate.
    - unfold tablesT, sZ, eZ. repeat constructor.
      + rewrite xeq_table_length, htt. reflexivity.
      + rewrite !length_map, hs. reflexivity.
      + rewrite !length_map, he. reflexivity.
    - exact H.
    - intros x hx. apply SfullT; assumption.
    - intros j X hj.
      exact (@dec_HpfT Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field n1 ell base Hn1 HcharW dtsW stabW etabW
               (repeat fzero m) (map to_F tt) (map to_F kT) (map to_F rt)
               (repeat_length _ _) ltac:(rewrite length_map; exact hrt) avsW j X hj).
    - exact hi.
  Qed.

  (* the G values: the first component of the model's honT for each sumcheck *)
  Local Notation Gof := (fun (g : xf * list (list xf)) => fadd (fmul (p2F (List.length (csF (snd g)))) (to_F (fst g))) (WF (csF (snd g)))).

  Theorem G_runD : map to_F (GD n1 ell kd base k) = [Gof gGx; Gof gTx].
  Proof.
    destruct (gG_shape n1 ell kd base k) as [hG _]. destruct (gT_shape n1 ell kd base k) as [hT _].
    assert (hG0 : snd gGx <> []) by (intro ec; rewrite ec in hG; cbn in hG; lia).
    assert (hT0 : snd gTx <> []) by (intro ec; rewrite ec in hT; cbn in hT; lia).
    unfold GD. cbn [map]. rewrite !to_F_mtotal by assumption.
    unfold csF. rewrite <-!(length_map (map to_F)).
    rewrite !(@mask_tsum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). reflexivity.
  Qed.

  (* the masked evaluations sent after the two sumchecks are the model's evs *)
  Hypothesis Hdmax : (2 * base + 1 <= DMAX)%nat.

  Theorem evals_runD : forall tz kG rhoG mG rz finG c0 c1 tt kT rhoT mT rt finT c2 c3,
    ternZ s -> ternZ e ->
    List.length tz = m -> List.length kG = kd -> List.length rhoG = 1%nat ->
    List.length tt = n1 -> List.length kT = 2%nat -> List.length rhoT = 1%nat ->
    sc_loop (fun c nm => get_F c nm 1) "G" (tmaskG kd k) (termsG kd base kG) (fst gGx) (snd gGx)
            (nth 0 rhoG xzero) (dGX n1 ell base) 0 (tablesG kd base off E tz) [] c0 = Some (mG, rz, finG, c1) ->
    sc_loop (fun c nm => get_F c nm 1) "T" (tmaskT kd k) (termsT kT) (fst gTx) (snd gTx)
            (nth 0 rhoT xzero) (dTX n1) 0 (tablesT s e tt) [] c2 = Some (mT, rt, finT, c3) ->
    map to_F (firstn kd (tl finG) ++ firstn 2 (tl finT))
    = evsF (@specsD Fq2 n1 ell dtsW stabW etabW (map to_F rz) (map to_F rt)) avsW.
  Proof.
    intros tz kG rhoG mG rz finG c0 c1 tt kT rhoT mT rt finT c2 c3 hts hte htz hkG hrG htt hkT hrT eG eT.
    pose proof Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & hb).
    pose proof Hk as (_ & _ & _ & hm & _).
    pose proof Hw as (hE & hEf & hs & he).
    destruct (dscG n1 ell kd base off s e E k Hn1 hb Hdmax (conj hE hEf) hs he hm tz kG rhoG mG rz finG c0 c1 htz hkG hrG eG)
      as (_ & _ & _ & hrz & _ & finGv).
    destruct (dscT n1 ell kd base s e E k Hn1 hb Hdmax (conj hE hEf) hs he hm tt kT rhoT mT rt finT c2 c3 hts hte htt hkT hrT eT)
      as (_ & _ & _ & hrt & _ & finTv).
    assert (hne : forall (l : list nat), List.length l <> 0%nat -> l <> []) by (intros l h ec; subst; cbn in h; lia).
    assert (lfG : List.length finG = S kd).
    { rewrite (sc_loop_fin_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hne (dGX n1 ell base) ltac:(rewrite dGX_len; lia)) eG).
      unfold tablesG, tmaskG. cbn [List.length]. rewrite !length_map, length_seq.
      unfold a_dig. rewrite length_firstn, hm. unfold n_maskD. lia. }
    assert (lfT : List.length finT = 3%nat)
      by (rewrite (sc_loop_fin_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hne (dTX n1) ltac:(rewrite dTX_len; lia)) eT); reflexivity).
    assert (hdl : List.length dtsW = kd) by (unfold dtsW, dtsT; rewrite length_map, length_seq; reflexivity).
    assert (hav : (kd + 2 <= List.length avsW)%nat) by (rewrite length_map, hm; unfold n_maskD; lia).
    assert (len_evs : forall specs avs, (List.length specs <= List.length avs)%nat ->
                        List.length (evsF specs avs) = List.length specs).
    { induction specs as [| sp specs ih]; intros avs h; [reflexivity |].
      destruct avs as [| a0 avs]; cbn in h; [lia |]. cbn. rewrite ih by lia. reflexivity. }
    assert (nth_evs : forall specs avs i, (i < List.length specs)%nat -> (i < List.length avs)%nat ->
      nth i (evsF specs avs) fzero
      = @ZkMix.ev Fq2 fzero fone fadd fmul fsub (nth i specs (0%nat, fun _ => fzero, [])) (nth i avs fzero)).
    { induction specs as [| sp specs ih]; intros avs i h1 h2; [cbn in h1; lia |].
      destruct avs as [| a0 avs]; cbn in h2; [lia |].
      destruct i as [| i]; [reflexivity |]. cbn [ZkMix.evs nth]. apply ih; cbn in h1, h2; lia. }
    assert (hsl : List.length (specsD n1 ell dtsW stabW etabW (map to_F rz) (map to_F rt)) = (kd + 2)%nat)
      by (unfold specsD; rewrite length_app, length_map, hdl; reflexivity).
    apply nth_ext with (d := fzero) (d' := fzero).
    { rewrite len_evs by lia. rewrite hsl, length_map, length_app, !length_firstn, !length_tl, lfG, lfT. lia. }
    intros i hi. rewrite length_map, length_app, !length_firstn, !length_tl, lfG, lfT in hi.
    rewrite nth_evs by lia. rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero).
    assert (htl : forall (l : list xf) j, nth j (tl l) xzero = nth (S j) l xzero)
      by (intros [| x0 l] j; [destruct j; reflexivity | reflexivity]).
    assert (hmle : forall (tbl r : list xf) M, List.length r = M -> List.length tbl = (2 ^ M)%nat ->
              to_F (xmle tbl r) = mle2 M (tabOf (map to_F tbl)) (map to_F r))
      by (intros tbl r M hr ht; subst M; apply to_F_mle; exact ht).
    unfold specsD, ZkMix.ev, mstar.
    destruct (Nat.lt_ge_cases i kd) as [hik | hik].
    - rewrite app_nth1 by (rewrite length_firstn, length_tl, lfG; lia).
      rewrite app_nth1 by (rewrite length_map, hdl; exact hik).
      rewrite nth_firstn. destruct (Nat.ltb_spec i kd) as [_ | h]; [| lia].
      rewrite htl, finGv by lia.
      rewrite (nth_indep (map (fun T => (m, T, map to_F rz)) dtsW) _ (m, fun _ => fzero, map to_F rz))
        by (rewrite length_map, hdl; exact hik).
      rewrite (map_nth (fun T => (m, T, map to_F rz))). cbn [fst snd].
      cbn [nth tablesG]. rewrite nth_map_seq0 by exact hik.
      rewrite (hmle _ _ m hrz) by (rewrite length_map; apply (Tdig_len' n1 ell base off s e E Hw)).
      rewrite (ExecZkTables.mle_tab_ext m _ (nth i dtsW (fun _ => fzero))).
      2:{ intros j hj. rewrite digW_tab by lia.
          rewrite (nth_map_dflt to_F _ j xzero fzero to_F_zero), (nth_map_dflt bx _ j 0%Z xzero eq_refl). reflexivity. }
      f_equal. f_equal.
      unfold maskv, tmaskG. cbn [nth].
      rewrite (nth_indep (map Some (a_dig kd k)) None (Some xzero))
        by (rewrite length_map; unfold a_dig; rewrite length_firstn, hm; unfold n_maskD; lia).
      rewrite map_nth. unfold a_dig. rewrite nth_firstn. destruct (Nat.ltb_spec i kd) as [_ | h]; [| lia].
      rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero). reflexivity.
    - rewrite app_nth2 by (rewrite length_firstn, length_tl, lfG; lia).
      rewrite app_nth2 by (rewrite length_map, hdl; exact hik).
      rewrite length_firstn, length_tl, lfG, length_map, hdl. replace (Nat.min kd (S kd - 1)) with kd by lia.
      assert (hi2 : (i - kd < 2)%nat) by lia.
      rewrite nth_firstn. destruct (Nat.ltb_spec (i - kd) 2) as [_ | h]; [| lia].
      rewrite htl, finTv by lia.
      rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero).
      destruct (i - kd)%nat as [| [| j]] eqn:ej; [| | lia]; cbn [nth tablesT fst snd]; unfold maskv, tmaskT; cbn [nth].
      + rewrite (hmle _ _ n1 hrt) by (unfold sZ; rewrite !length_map; exact hs).
        rewrite (ExecZkTables.mle_tab_ext n1 (map to_F (map bx (sZ s))) stabW).
        2:{ intros j hj. rewrite stabW_pt by lia. unfold sZ.
            rewrite (nth_map_dflt to_F _ j xzero fzero to_F_zero), (nth_map_dflt bx _ j 0%Z xzero eq_refl),
                    (nth_map_dflt zm _ j 0%Z 0%Z eq_refl). apply to_F_bx_zm. }
        replace i with kd by lia. reflexivity.
      + rewrite (hmle _ _ n1 hrt) by (unfold eZ; rewrite !length_map; exact he).
        rewrite (ExecZkTables.mle_tab_ext n1 (map to_F (map bx (eZ e))) etabW).
        2:{ intros j hj. rewrite etabW_pt by lia. unfold eZ.
            rewrite (nth_map_dflt to_F _ j xzero fzero to_F_zero), (nth_map_dflt bx _ j 0%Z xzero eq_refl),
                    (nth_map_dflt zm _ j 0%Z 0%Z eq_refl). apply to_F_bx_zm. }
        replace i with (kd + 1)%nat by lia. reflexivity.
  Qed.

End DL.
