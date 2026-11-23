(* Zero knowledge of the decryption proof: the sumcheck layer and the
   opening joined (paper, Theorem 7.1, zero-knowledge part).

   The prover's coins are those of the layer (ZkDecLayer.v: the mask
   coefficients a_d, a_s, a_e and the two sumcheck masks) and those of the
   opening (ZkDecOpen.v). The mask table is the layer's randomness and the
   third data row of the small matrix, so the opening depends on the
   layer's coins (dSx). The witness rows (digit tables, s, e) are fixed.

   The opening's simulator needs the batched target value cv. cvVD
   computes it from the layer transcript as dec_derive does: the public
   values VD, VK, the masked evaluations, and the mask values of the two
   sumchecks solved from their final values. cv_honest_dec: on honest
   transcripts this is the true value, for a witness.

   dec_zk: over all coins, the honest transcripts (layer, opening) are a
   permutation of the simulated ones (zk_join). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Sumcheck SumcheckMask MaskedExt PolyFun Interp ZkBlocks
  ZkSumcheck ZkMix ZkTranscript ZkOpen ZkOpenTranscript ZkJoin SlotKinds Opening OpenClaims RowLayout ZeroTest
  DecSound DecLayout ZkDecLayer CubeIndex.
From Examples Require Import ConcreteField ExecHash ExecVerify ExecFront ZkOpenMix ZkDecOpen.
Import ListNotations.

Add Field fieldF2dj : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation dotF := (@LogDer.dot Fq2 fzero fadd fmul).

(* ---------------------------------------------------------------------- *)
(* a mask table as a row over Z_q: every F entry as its two coordinates *)

Definition flatZ (km : list F) : list Zq := flat_map (fun z => [fst z; snd z]) km.

Lemma flatZ_length : forall km, length (flatZ km) = (2 * length km)%nat.
Proof. induction km as [| z km ih]; [reflexivity |]. cbn [flatZ flat_map app length]. fold (flatZ km). rewrite ih. lia. Qed.

Lemma emb_ment : forall (re0 im0 : Zq), fadd (emb re0) (fmul ftg (emb im0)) = (re0, im0).
Proof.
  intros x y. unfold emb, ftg, fadd, fmul, egen, eadd, emul. cbn [fst snd].
  f_equal; ring.
Qed.

Local Notation pt2 := (@pt Fq2 fzero fone).

Lemma pt_split2 : forall a b y t, (y < 2 ^ a)%nat -> pt2 (a + b) (y + 2 ^ a * t) = pt2 a y ++ pt2 b t.
Proof.
  induction a as [| a ih]; intros b y t hy.
  + cbn in hy. replace y with 0%nat by lia. cbn. f_equal. lia.
  + cbn [Nat.add CubeIndex.pt app].
    replace (y + 2 ^ S a * t)%nat with (y + 2 * (2 ^ a * t))%nat by (rewrite Nat.pow_succ_r'; lia).
    f_equal.
    - unfold CubeIndex.bit. rewrite Nat.odd_add_mul_2. reflexivity.
    - rewrite <-ih by (rewrite Nat.div2_div; apply Nat.Div0.div_lt_upper_bound; rewrite Nat.pow_succ_r' in hy; lia).
      f_equal. rewrite !Nat.div2_div. rewrite (Nat.mul_comm 2 (2 ^ a * t)), Nat.div_add by lia. reflexivity.
Qed.

Lemma cube_pt : forall k b, In b (@Mle.cube Fq2 fzero fone k) -> exists y, (y < 2 ^ k)%nat /\ b = pt2 k y.
Proof.
  intros k b h. pose proof (@pt_perm Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field k) as hp.
  apply (Permutation_in _ (Permutation_sym hp)) in h. apply in_map_iff in h. destruct h as (y & <- & hy).
  apply in_seq in hy. exists y. split; [lia | reflexivity].
Qed.

Lemma cube_split : forall a c b, In b (@Mle.cube Fq2 fzero fone (a + c)) ->
  exists y t, (y < 2 ^ a)%nat /\ (t < 2 ^ c)%nat /\ b = pt2 a y ++ pt2 c t.
Proof.
  intros a c b h. destruct (cube_pt (a + c) b h) as (z & hz & ->).
  exists (z mod 2 ^ a)%nat, (z / 2 ^ a)%nat.
  assert (h2 : (2 ^ a <> 0)%nat) by (apply Nat.pow_nonzero; lia).
  split; [apply Nat.mod_upper_bound; exact h2 |]. split.
  - apply Nat.Div0.div_lt_upper_bound. rewrite <-Nat.pow_add_r. lia.
  - rewrite <-pt_split2 by (apply Nat.mod_upper_bound; exact h2). f_equal. pose proof (Nat.div_mod z (2 ^ a) h2). lia.
Qed.

Section DecJoin.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (nqB nB nqS nS : nat) (omB omS : Zq).

  Local Notation m := (n1 + ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwD n1 ell lo1).
  Local Notation SO := (kd * rwD n1 ell lo1 + 6)%nat.

  (* the witness rows: the digit rows of the big matrix, s and e *)
  Variable dB : nat -> list Zq.
  Variables sRow eRow : list Zq.
  Hypothesis HdB : forall i, (i < kd * rw)%nat -> length (dB i) = C1.
  Hypothesis Hs : length sRow = C2.
  Hypothesis He : length eRow = C2.

  (* the mask table of the layer coins (a_d, a_s, a_e; mask G; mask T) *)
  Definition kmOf (x : @rand2 F) : list F :=
    fst x ++ (fst (fst (snd x)) :: List.concat (snd (fst (snd x))))
          ++ (fst (snd (snd x)) :: List.concat (snd (snd (snd x)))).
  Definition mrowZ (km : list F) : list Zq := flatZ km ++ repeat qzero (C2 - 2 * length km).

  Definition dSx (x : @rand2 F) (j : nat) : list Zq :=
    if Nat.eqb j 0 then sRow else if Nat.eqb j 1 then eRow else mrowZ (kmOf x).
  Definition dSw (j : nat) : list Zq :=
    if Nat.eqb j 0 then sRow else if Nat.eqb j 1 then eRow else repeat qzero C2.

  Local Notation Px := (fun x => P0 n1 ell lo1 kd dB (dSx x)).
  Local Notation Pw := (P0 n1 ell lo1 kd dB dSw).

  (* the rows with and without the layer's coins differ only in the mask-table row *)
  Lemma rows_agree : forall x r, r <> (SO + 2)%nat -> Px x r = Pw r.
  Proof.
    intros x r hr. cbv beta. unfold P0. destruct (Nat.ltb_spec r SO); [reflexivity |].
    unfold ZkDecOpen.datasS. f_equal.
    destruct (Nat.lt_ge_cases (r - SO) 3) as [h | h].
    - rewrite !(nth_map_seq_any2 _ 3 (r - SO) [] h). unfold dSx, dSw.
      destruct (Nat.eqb_spec (r - SO) 0); [reflexivity |]. destruct (Nat.eqb_spec (r - SO) 1); [reflexivity |]. lia.
    - rewrite !nth_overflow by (rewrite length_map, length_seq; exact h). reflexivity.
  Qed.

  Lemma row_mask : forall x, Px x (SO + 2)%nat = map emb (mrowZ (kmOf x)).
  Proof.
    intro x. cbv beta. unfold P0. destruct (Nat.ltb_spec (SO + 2) SO); [lia |].
    replace (SO + 2 - SO)%nat with 2%nat by lia. unfold ZkDecOpen.datasS. reflexivity.
  Qed.

  (* entries of the mask table, read as F elements *)
  Lemma ment_mrow : forall km e, (e < length km)%nat ->
    @ment Fq2 fzero fadd fmul ftg (map emb (mrowZ km)) e = nth e km fzero.
  Proof.
    intros km e he. unfold RowLayout.ment, mrowZ. rewrite !map_app.
    rewrite !app_nth1 by (rewrite length_map, flatZ_length; lia).
    revert e he. induction km as [| z km ih]; intros e he; [cbn in he; lia |].
    destruct e as [| e].
    - cbn [flatZ flat_map app map nth]. destruct z as [z0 z1]. cbn [fst snd]. apply emb_ment.
    - cbn [flatZ flat_map app map]. fold (flatZ km).
      replace (2 * S e)%nat with (S (S (2 * e))) by lia. replace (S (S (2 * e)) + 1)%nat with (S (S (2 * e + 1))) by lia.
      cbn [nth]. apply ih. cbn in he. lia.
  Qed.

  (* the witness tables read the same rows in both families *)
  Local Notation digTx := (fun x d => @digT Fq2 fzero fone Fq2_dec (Px x) n1 ell lo1 d).
  Local Notation digTw := (fun d => @digT Fq2 fzero fone Fq2_dec Pw n1 ell lo1 d).

  Lemma digT_agree : forall x d bq, (d < kd)%nat -> length bq = m -> digTx x d bq = digTw d bq.
  Proof.
    intros x d bq hd hl. cbv beta. unfold DecLayout.digT, RowLayout.rdtab.
    rewrite (rows_agree x); [reflexivity |].
    pose proof (@bidx_lt Fq2 fone Fq2_dec (skipn (loE m lo1) bq)) as hb.
    rewrite length_skipn, hl in hb. unfold rwD, RowLayout.hiE, RowLayout.loE in *.
    assert (hrw : (bidx (skipn (Nat.min lo1 m) bq) < 2 ^ (m - Nat.min lo1 m))%nat) by exact hb.
    nia.
  Qed.

  Lemma stab_agree : forall x bq, @stabT Fq2 fzero fone Fq2_dec (Px x) SO bq = @stabT Fq2 fzero fone Fq2_dec Pw SO bq.
  Proof. intros x bq. unfold DecLayout.stabT, DecLayout.rowT, DecLayout.rS. rewrite (rows_agree x) by lia. reflexivity. Qed.

  Lemma etab_agree : forall x bq, @etabT Fq2 fzero fone Fq2_dec (Px x) SO bq = @etabT Fq2 fzero fone Fq2_dec Pw SO bq.
  Proof. intros x bq. unfold DecLayout.etabT, DecLayout.rowT, DecLayout.rE. rewrite (rows_agree x) by lia. reflexivity. Qed.


  (* ------------------------------------------------------------------ *)
  (* the statement, the witness and the challenges *)

  Variables (aF bF : list F) (ppF offF : F) (usF tsF : nat -> list F).
  Variables th th1 th2 tz kG rz tt kT rt : list F.
  Variables rhoG rhoT : F.
  Hypothesis Hn1 : (1 <= n1)%nat.
  Hypothesis Hlo1 : (lo1 <= m)%nat.
  Hypothesis Hth : length th = ell.
  Hypothesis Hth1 : length th1 = n1.
  Hypothesis Hth2 : length th2 = n1.
  Hypothesis Hrz : length rz = m.
  Hypothesis Hrt : length rt = n1.
  Local Notation ptD := (th1 ++ th).
  Local Notation dG := (map (degZ m base) (seq 0 m)).
  Local Notation dT := (map (degZ n1 3) (seq 0 n1)).
  Local Notation Nmax := (Nat.max (2 * base + 2) 8).

  Lemma HptD : length ptD = m.
  Proof. rewrite length_app, Hth1, Hth. reflexivity. Qed.
  Lemma HdGl : length dG = m.
  Proof. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma HdTl : length dT = n1.
  Proof. rewrite length_map, length_seq. reflexivity. Qed.

  (* the layer's tables: the witness rows *)
  Local Notation dtsW := (@dtsT Fq2 fzero fone Fq2_dec Pw n1 ell lo1 kd).
  Local Notation stabW := (@stabT Fq2 fzero fone Fq2_dec Pw SO).
  Local Notation etabW := (@etabT Fq2 fzero fone Fq2_dec Pw SO).

  Hypothesis Hwit : @is_dec_witness Fq2 fzero fone fadd fmul fsub fopp aF bF ppF offF n1 ell base usF tsF
                      dtsW stabW etabW (@rangep Fq2 fzero fone fadd fmul fopp base).

  Lemma dtsW_length : length dtsW = kd.
  Proof. unfold DecLayout.dtsT. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma Hdig : forall T, In T dtsW -> forall b, In b (@Mle.cube Fq2 fzero fone m) ->
    @eval Fq2 fzero fadd fmul (@rangep Fq2 fzero fone fadd fmul fopp base) (T b) = fzero.
  Proof. exact (proj1 Hwit). Qed.

  Lemma Htern : forall b, In b (@Mle.cube Fq2 fzero fone n1) ->
    @eval Fq2 fzero fadd fmul (@phi3 Fq2 fzero fone fopp) (stabW b) = fzero
    /\ @eval Fq2 fzero fadd fmul (@phi3 Fq2 fzero fone fopp) (etabW b) = fzero.
  Proof.
    intros b hb. destruct (proj1 (proj2 Hwit) b hb) as [hs hE].
    assert (h : forall w, @Bgv.tern Fq2 fzero fone fopp w -> @eval Fq2 fzero fadd fmul (@phi3 Fq2 fzero fone fopp) w = fzero).
    { intros w hw. rewrite (@phi3_eval Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
      destruct hw as [-> | [-> | ->]]; field. }
    split; apply h; assumption.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* list tools *)

  Lemma map_nth_seq : forall (l : list F) k, (k <= length l)%nat -> map (fun i => nth i l fzero) (seq 0 k) = firstn k l.
  Proof.
    induction l as [| x l ih]; intros k hk; destruct k as [| k]; cbn in hk; try lia; try reflexivity.
    cbn [seq map firstn nth]. f_equal. rewrite <-seq_shift, map_map. apply ih. lia.
  Qed.

  Lemma concat_len : forall (degs : list nat) (cs : list (list F)), @shaped F degs cs -> length (List.concat cs) = dsumL degs.
  Proof.
    intros degs cs h. induction h as [| d l ds cs hl h ih]; [reflexivity |].
    cbn [List.concat dsumL]. rewrite length_app, hl, ih. reflexivity.
  Qed.

  Lemma chunks_concat_sh : forall (degs : list nat) (cs : list (list F)) rest, @shaped F degs cs ->
    @RowLayout.chunks F degs (List.concat cs ++ rest) = cs.
  Proof.
    intros degs cs rest h. induction h as [| d l ds cs hl h ih]; [reflexivity |].
    cbn [RowLayout.chunks List.concat]. rewrite <-app_assoc. subst d.
    rewrite firstn_app, Nat.sub_diag, firstn_all, firstn_O, app_nil_r, skipn_app, skipn_all, Nat.sub_diag, skipn_O.
    cbn [app]. rewrite ih. reflexivity.
  Qed.

  Lemma gtval_agree : forall (P P' : nat -> list F) kind Lt cl, (forall t, In t cl -> P (trow t) = P' (trow t)) ->
    @gtval Fq2 fzero fadd fmul P kind Lt cl = @gtval Fq2 fzero fadd fmul P' kind Lt cl.
  Proof.
    intros P P' kind Lt; induction cl as [| t cl ih]; intro h; [reflexivity |]. cbn [SlotKinds.gtval].
    rewrite (h t (or_introl eq_refl)), ih by (intros t' h'; apply h; right; exact h'). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the claims D and K read no mask-table entry *)

  Local Notation clDx := (@clD Fq2 fzero fone fadd fmul fsub fopp n1 ell lo1 SO kd base ppF usF ptD).
  Local Notation clKx := (@clK Fq2 fzero fone fadd fmul fsub fopp n1 SO aF ppF th2).

  Lemma rows_clD : forall t, In t clDx -> trow t <> (SO + 2)%nat.
  Proof.
    intros t ht. unfold DecLayout.clD in ht. destruct ht as [<- | ht]; [cbn; unfold DecLayout.rS; lia |].
    unfold DecLayout.digD in ht. apply in_concat in ht. destruct ht as (l & hl & ht).
    apply in_map_iff in hl. destruct hl as (d & <- & hd). apply in_seq in hd.
    destruct (@tabt_terms Fq2 fzero fone fadd fmul fsub _ _ _ _ _ _ _ ht) as (e & j & hj & er).
    rewrite er. change (2 ^ hiE m lo1)%nat with rw in hj.
    assert (hlt : (d * rw + j < kd * rw)%nat) by nia. lia.
  Qed.

  Lemma rows_clK : forall t, In t clKx -> trow t <> (SO + 2)%nat.
  Proof. intros t ht. unfold DecLayout.clK in ht. destruct ht as [<- | [<- | []]]; cbn; unfold DecLayout.rS, DecLayout.rE; lia. Qed.


  (* ------------------------------------------------------------------ *)
  (* the claims D and K: for a witness their values are the public values *)

  Local Notation VDx := (@VDv Fq2 fzero fone fadd fmul fsub Fq2_dec n1 ell ppF offF tsF ptD).
  Local Notation VKx := (@VKv Fq2 fzero fone fadd fmul fsub n1 bF th2).
  Local Notation gtvx := (fun P => @gtval Fq2 fzero fadd fmul P kindD (@LtD Fq2 fzero fone fadd fmul fsub n1 ell lo1 ptD rz)).

  Lemma mle_zero_cube : forall k (T : list F -> F) x, length x = k ->
    (forall b, In b (@Mle.cube Fq2 fzero fone k) -> T b = fzero) -> mle2 k T x = fzero.
  Proof.
    intros k T x hx h. rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub k T (fun _ => fzero)) by exact h.
    apply (@mle_const Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). exact hx.
  Qed.

  Lemma valD : forall x, gtvx (Px x) clDx = VDx.
  Proof.
    intro x. cbv beta. rewrite (gtval_agree (Px x) Pw) by (intros t ht; apply rows_agree, rows_clD, ht).
    pose proof (@claimD Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field Pw n1 ell lo1 SO kd base ppF offF
                  usF tsF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdGl HdTl) as e.
    rewrite (mle_zero_cube m) in e by
      (first [exact HptD
             | intros b hb; destruct (cube_split n1 ell b hb) as (y & t & hy & ht & ->);
               rewrite (@HD_T Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field Pw n1 ell lo1 SO kd base
                          ppF offF usF tsF t y ht hy);
               exact (proj1 (proj2 (proj2 Hwit)) t y ht hy)]).
    cbv beta. transitivity (fsub VDx (fsub VDx (gtvx Pw clDx))); [field |]. cbv beta in e. rewrite e. field.
  Qed.

  Lemma valK : forall x, gtvx (Px x) clKx = VKx.
  Proof.
    intro x. cbv beta. rewrite (gtval_agree (Px x) Pw) by (intros t ht; apply rows_agree, rows_clK, ht).
    pose proof (@claimK Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field Pw n1 ell lo1 SO aF bF ppF
                  dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdGl HdTl) as e.
    rewrite (mle_zero_cube n1) in e by
      (first [exact Hth2
             | intros b hb; destruct (cube_pt n1 b hb) as (y & hy & ->);
               rewrite (@HK_T Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field Pw n1 SO aF bF ppF y hy);
               exact (proj2 (proj2 (proj2 Hwit)) y hy)]).
    cbv beta. transitivity (fsub VKx (fsub VKx (gtvx Pw clKx))); [field |]. cbv beta in e. rewrite e. field.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the masked evaluations *)

  Local Notation specsW := (@specsD Fq2 n1 ell dtsW stabW etabW rz rt).
  Local Notation evsF := (@evs Fq2 fzero fone fadd fmul fsub).
  Local Notation evalsF := (@evalsOf Fq2 fzero fone fadd fmul fsub).
  Local Notation mstarF := (@mstar Fq2 fzero fone fadd fmul fsub).

  Lemma evs_map_app : forall (k : nat) (r : list F) (ds : list (list F -> F)) rest avs, (length ds <= length avs)%nat ->
    evsF (map (fun T => (k, T, r)) ds ++ rest) avs = evalsF k ds (firstn (length ds) avs) r ++ evsF rest (skipn (length ds) avs).
  Proof.
    intros k r; induction ds as [| T ds ih]; intros rest avs h; [reflexivity |].
    destruct avs as [| a avs]; cbn in h; [lia |].
    cbn [map app length firstn skipn evs]. rewrite ih by lia. reflexivity.
  Qed.

  Lemma evs_specsW : forall avs, length avs = (kd + 2)%nat ->
    evsF specsW avs = evalsF m dtsW (firstn kd avs) rz ++ evalsF n1 [stabW; etabW] (skipn kd avs) rt.
  Proof.
    intros avs h. unfold specsD. rewrite evs_map_app by (rewrite dtsW_length; lia). rewrite dtsW_length.
    f_equal.
  Qed.

  Lemma evalsOf_length : forall k (Ts : list (list F -> F)) avs r, length avs = length Ts -> length (evalsF k Ts avs r) = length Ts.
  Proof.
    intros k; induction Ts as [| T Ts ih]; intros avs r h; destruct avs as [| a avs]; cbn in h; try lia; [reflexivity |].
    cbn. rewrite ih by lia. reflexivity.
  Qed.

  Lemma evalsOf_agree : forall x l avs, (forall d, In d l -> (d < kd)%nat) ->
    evalsF m (map (fun d => digTx x d) l) avs rz = evalsF m (map digTw l) avs rz.
  Proof.
    intros x; induction l as [| d l ih]; intros avs h; [reflexivity |].
    destruct avs as [| a avs]; [reflexivity |]. cbn [map ZeroTest.evalsOf]. f_equal.
    - unfold MaskedExt.mstar. cbv beta.
      rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub m _ (digTw d)); [reflexivity |]. intros b hb.
      apply digT_agree; [apply h; left; reflexivity | exact (@cube_length Fq2 fzero fone _ b hb)].
    - apply ih. intros d' hd'. apply h. right. exact hd'.
  Qed.

  Lemma mstar_stab : forall x a r, mstarF n1 (@stabT Fq2 fzero fone Fq2_dec (Px x) SO) a r = mstarF n1 stabW a r.
  Proof.
    intros x a r. unfold MaskedExt.mstar.
    rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub n1 _ stabW); [reflexivity |]. intros b _. apply stab_agree.
  Qed.

  Lemma mstar_etab : forall x a r, mstarF n1 (@etabT Fq2 fzero fone Fq2_dec (Px x) SO) a r = mstarF n1 etabW a r.
  Proof.
    intros x a r. unfold MaskedExt.mstar.
    rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub n1 _ etabW); [reflexivity |]. intros b _. apply etab_agree.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the mask table read back *)

  Local Notation PmX := (fun x => map emb (mrowZ (kmOf x))).

  Lemma PmD_x : forall x, @PmD Fq2 (Px x) SO = PmX x.
  Proof. intro x. unfold DecLayout.PmD, DecLayout.rMd. exact (row_mask x). Qed.

  Lemma ment_km : forall x e, (e < length (kmOf x))%nat -> @ment Fq2 fzero fadd fmul ftg (PmX x) e = nth e (kmOf x) fzero.
  Proof. intros x e h. cbv beta. apply ment_mrow. exact h. Qed.

  Lemma read_mask : forall (km pre : list F) a0 (cs : list (list F)) degs rest,
    km = pre ++ (a0 :: List.concat cs) ++ rest -> @shaped F degs cs ->
    (forall e, (e < length km)%nat -> @ment Fq2 fzero fadd fmul ftg (map emb (mrowZ km)) e = nth e km fzero) ->
    @maskA0 Fq2 fzero fadd fmul ftg (map emb (mrowZ km)) (length pre) = a0
    /\ @maskCs Fq2 fzero fadd fmul ftg (map emb (mrowZ km)) (length pre) degs = cs.
  Proof.
    intros km pre a0 cs degs rest ek hsh hm.
    assert (hlen : length km = (length pre + 1 + length (List.concat cs) + length rest)%nat)
      by (rewrite ek, !length_app; cbn [length]; lia).
    split.
    - unfold RowLayout.maskA0. rewrite hm by lia. rewrite ek, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
    - unfold RowLayout.maskCs.
      rewrite (map_ext_in _ (fun i => nth i (List.concat cs ++ rest) fzero)).
      + rewrite map_nth_seq by (rewrite length_app, (concat_len degs cs hsh); lia).
        rewrite firstn_app, <-(concat_len degs cs hsh), firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
        rewrite <-(app_nil_r (List.concat cs)). apply chunks_concat_sh. exact hsh.
      + intros i hi. apply in_seq in hi. rewrite (concat_len degs cs hsh) in hlen.
        rewrite hm by lia. rewrite ek, app_nth2 by lia.
        replace (length pre + 1 + i - length pre)%nat with (S i) by lia. reflexivity.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the batched target value from the layer transcript *)

  Variables (kp : list F) (cc : F).
  Hypothesis HbaseQ : (Z.of_nat (Nat.max (2 * base + 2) 8) < Q)%Z.
  Hypothesis HrhoG : rhoG <> fzero.
  Hypothesis HrhoT : rhoT <> fzero.

  Lemma Hchar : forall k, (0 < k <= Nmax)%nat -> @nF Fq2 fzero fone fadd k <> fzero.
  Proof. intros k hk. apply Fq2_char. lia. Qed.

  Local Notation phiR := (@rangep Fq2 fzero fone fadd fmul fopp base).
  Local Notation phi3F := (@phi3 Fq2 fzero fone fopp).
  Local Notation eqpF := (@eqp Fq2 fone fadd fmul fsub).

  Definition finOfD (msgs : list (list F)) (rs : list F) (cl : F) : F :=
    match @Sumcheck.sc_verify Fq2 fzero fone fadd fmul Fq2_dec msgs rs cl with Some v => v | None => fzero end.

  Definition EGD (ys : list F) : F := fmul (eqpF rz tz) (@innerZ Fq2 fzero fadd fmul phiR kG (firstn kd ys)).
  Definition ETD (ys : list F) : F :=
    fmul (eqpF rt tt) (@innerZ Fq2 fzero fadd fmul phi3F kT [nth kd ys fzero; nth (kd + 1) ys fzero]).

  Definition valsVD (t : @view2 F) : list F :=
    let ys := fst t in
    let finG := finOfD (snd (fst (snd t))) rz (fadd (@cGD Fq2 fzero ys) (fmul rhoG (fst (fst (snd t))))) in
    let finT := finOfD (snd (snd (snd t))) rt (fadd (@cTD Fq2 fzero ys) (fmul rhoT (fst (snd (snd t))))) in
    [VDx; VKx] ++ firstn kd ys ++ [nth kd ys fzero; nth (kd + 1) ys fzero]
    ++ [fdiv (fsub finG (EGD ys)) rhoG; fdiv (fsub finT (ETD ys)) rhoT].

  Definition cvVD (t : @view2 F) : F := fmul cc (dotF kp (valsVD t)).

  Local Notation honDLx := (@honDL Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dtsW stabW etabW tz kG rz tt kT rt rhoG rhoT).
  Local Notation fGx := (@fG Fq2 fzero fone fadd fmul fsub fopp n1 ell base dtsW tz kG).
  Local Notation fTx := (@fT Fq2 fzero fone fadd fmul fsub fopp n1 dtsW stabW etabW tt kT).

  Lemma firstn_app_ex : forall (l1 l2 : list F) n, n = length l1 -> firstn n (l1 ++ l2) = l1.
  Proof. intros l1 l2 n ->. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all. reflexivity. Qed.

  Lemma fG_EG : forall avs, length avs = (kd + 2)%nat -> fGx avs rz = EGD (evsF specsW avs).
  Proof.
    intros avs h. unfold EGD. rewrite evs_specsW by exact h.
    rewrite firstn_app_ex by (rewrite evalsOf_length by (rewrite length_firstn, dtsW_length; lia); symmetry; apply dtsW_length).
    rewrite (@innerZ_evals Fq2 fzero fone fadd fmul fsub m ltac:(lia) phiR base
               (@rangep_length Fq2 fzero fone fadd fmul fopp base) kG dtsW (firstn kd avs) rz)
      by (rewrite length_firstn, dtsW_length; lia).
    unfold fG, ZeroTest.gZ. rewrite dtsW_length.
    generalize (@ZeroTest.inner Fq2 fzero fone fadd fmul fsub m phiR kG dtsW (firstn kd avs) rz).
    generalize (@gmask Fq2 fzero fadd fmul fzero (repeat [] m) rz). intros g u. field.
  Qed.

  Lemma fT_ET : forall avs, length avs = (kd + 2)%nat -> fTx avs rt = ETD (evsF specsW avs).
  Proof.
    intros avs h. unfold ETD. rewrite evs_specsW by exact h.
    assert (hl1 : length (evalsF m dtsW (firstn kd avs) rz) = kd)
      by (rewrite evalsOf_length by (rewrite length_firstn, dtsW_length; lia); apply dtsW_length).
    rewrite !app_nth2 by lia. rewrite hl1, Nat.sub_diag. replace (kd + 1 - kd)%nat with 1%nat by lia.
    assert (hs : length (skipn kd avs) = 2%nat) by (rewrite length_skipn; lia).
    unfold fT, ZeroTest.gZ. rewrite dtsW_length.
    destruct (skipn kd avs) as [| a0 [| a1 [| a2 l]]] eqn:es; cbn in hs; try lia.
    cbn [ZeroTest.evalsOf nth].
    rewrite <-(@innerZ_evals Fq2 fzero fone fadd fmul fsub n1 Hn1 phi3F 3 ltac:(reflexivity) kT [stabW; etabW] [a0; a1] rt)
      by reflexivity.
    cbn [ZeroTest.evalsOf].
    generalize (@gmask Fq2 fzero fadd fmul fzero (repeat [] n1) rt). intro g. field.
  Qed.

  Theorem cv_honest_dec : forall avs aG csG aT csT, length avs = (kd + 2)%nat ->
    @shaped F dG csG -> @shaped F dT csT ->
    cvD n1 ell lo1 kd base dB (dSx (avs, ((aG, csG), (aT, csT)))) aF ppF usF dG dT ptD th2 rz rt kp cc
    = cvVD (honDLx (avs, ((aG, csG), (aT, csT)))).
  Proof.
    intros avs aG csG aT csT h7 hG hT.
    set (x := (avs, ((aG, csG), (aT, csT))) : @rand2 F).
    pose proof (Forall2_length hG) as lG. pose proof (Forall2_length hT) as lT.
    rewrite length_map, length_seq in lG, lT.
    assert (hspec : length avs = length specsW)
      by (unfold specsD; rewrite length_app, length_map, dtsW_length; cbn [length]; lia).
    (* the final values of the two sumchecks *)
    pose proof (@sc_complete Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field m (fGx avs)
                  (@pfG Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dtsW tz kG avs) rhoG rz dG
                  Hrz HdGl (fun j X hj => @dec_HpfG Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field
                                             n1 ell base Hn1 Hchar dtsW tz kG rz rt Hrz Hrt avs j X hj)
                  aG csG (eq_sym lG)) as scG.
    pose proof (@sc_complete Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field n1 (fTx avs)
                  (@pfT Fq2 fzero fone fadd fmul fsub fopp finv n1 dtsW stabW etabW tt kT avs) rhoT rt dT
                  Hrt HdTl (fun j X hj => @dec_HpfT Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field
                                             n1 ell base Hn1 Hchar dtsW stabW etabW rz tt kT rt Hrz Hrt avs j X hj)
                  aT csT (eq_sym lT)) as scT.
    rewrite (@dec_HcG_true Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell base Hn1 dtsW stabW etabW
               Hdig tz kG rz rt Hrz Hrt avs hspec) in scG.
    rewrite (@dec_HcT_true Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 ell Hn1 dtsW stabW etabW
               Htern rz tt kT rt Hrz Hrt avs hspec) in scT.
    unfold cvD, cvVD. f_equal. f_equal.
    rewrite (@layout_identityD Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field
               (P0 n1 ell lo1 kd dB (dSx x)) ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt
               HptD Hth2 Hrz Hrt HdGl HdTl).
    pose proof (valD x) as eD. pose proof (valK x) as eK. cbv beta in eD, eK. rewrite eD, eK.
    (* the mask table read back *)
    assert (hkm : length (kmOf x) = (kd + 2 + (1 + dsumL dG) + (1 + dsumL dT))%nat).
    { unfold kmOf, x. cbn [fst snd]. rewrite !length_app. cbn [length].
      rewrite (concat_len dG csG hG), (concat_len dT csT hT). lia. }
    assert (hav : forall e, (e < kd + 2)%nat -> @ment Fq2 fzero fadd fmul ftg (PmX x) e = nth e avs fzero).
    { intros e he. rewrite ment_km by lia. unfold kmOf, x. cbn [fst snd]. rewrite app_nth1 by lia. reflexivity. }
    assert (eAvG : @avG Fq2 fzero fadd fmul (P0 n1 ell lo1 kd dB (dSx x)) ftg SO kd = firstn kd avs).
    { unfold DecLayout.avG. rewrite PmD_x.
      rewrite (map_ext_in _ (fun e => nth e avs fzero)) by (intros e he; apply in_seq in he; apply hav; lia).
      apply map_nth_seq. lia. }
    assert (eAvT : @avT Fq2 fzero fadd fmul (P0 n1 ell lo1 kd dB (dSx x)) ftg SO kd = [nth kd avs fzero; nth (kd + 1) avs fzero]).
    { unfold DecLayout.avT. rewrite PmD_x, !hav by lia. reflexivity. }
    assert (hrd : forall e, (e < length (kmOf x))%nat -> @ment Fq2 fzero fadd fmul ftg (map emb (mrowZ (kmOf x))) e = nth e (kmOf x) fzero)
      by (intros e he; apply ment_mrow; exact he).
    destruct (read_mask (kmOf x) avs aG csG dG ((aT :: List.concat csT)) ltac:(unfold kmOf, x; cbn [fst snd]; reflexivity) hG hrd)
      as [eA0 eCs].
    destruct (read_mask (kmOf x) (avs ++ (aG :: List.concat csG)) aT csT dT []
                ltac:(unfold kmOf, x; cbn [fst snd]; rewrite app_nil_r, <-app_assoc; reflexivity) hT hrd)
      as [eT0 eTs].
    assert (hoG : offG kd = length avs) by (unfold offG; lia).
    assert (hoT : offT kd dG = length (avs ++ aG :: List.concat csG))
      by (unfold offT, offG; rewrite length_app; cbn [length]; rewrite (concat_len dG csG hG); lia).
    unfold DecLayout.a0GT, DecLayout.csGT, DecLayout.a0TT, DecLayout.csTT. rewrite !PmD_x. cbv beta.
    rewrite hoG, eA0, eCs, hoT, eT0, eTs, eAvG, eAvT.
    rewrite (evalsOf_agree x (seq 0 kd)) by (intros d hd; apply in_seq in hd; lia).
    fold dtsW. cbn [ZeroTest.evalsOf]. rewrite mstar_stab, mstar_etab.
    (* the transcript side *)
    unfold valsVD, honDL, honL2. unfold x. cbn [fst snd]. unfold honT. cbn [fst snd].
    unfold finOfD. rewrite scG, scT.
    rewrite <-(fG_EG avs h7), <-(fT_ET avs h7).
    rewrite evs_specsW by exact h7.
    assert (hl1 : length (evalsF m dtsW (firstn kd avs) rz) = kd)
      by (rewrite evalsOf_length by (rewrite length_firstn, dtsW_length; lia); apply dtsW_length).
    rewrite firstn_app_ex by (symmetry; exact hl1).
    rewrite !app_nth2 by lia. rewrite hl1, Nat.sub_diag. replace (kd + 1 - kd)%nat with 1%nat by lia.
    assert (hs : length (skipn kd avs) = 2%nat) by (rewrite length_skipn; lia).
    assert (e0 : nth kd avs fzero = nth 0 (skipn kd avs) fzero) by (rewrite nth_skipn; f_equal; lia).
    assert (e1 : nth (kd + 1) avs fzero = nth 1 (skipn kd avs) fzero) by (rewrite nth_skipn; reflexivity).
    rewrite e0, e1.
    destruct (skipn kd avs) as [| a0 [| a1 [| a2 l]]]; cbn in hs; try lia.
    cbn [ZeroTest.evalsOf nth app].
    repeat f_equal.
    - generalize (fGx avs rz) (@gmask Fq2 fzero fadd fmul aG csG rz). intros u g. field. exact HrhoG.
    - generalize (fTx avs rt) (@gmask Fq2 fzero fadd fmul aT csT rt). intros u g. field. exact HrhoT.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* parameters of the small matrix: the func-slot vectors and the mask table fit in a row *)

  Local Notation n_maskD := (kd + 2 + (1 + dsumL dG) + (1 + dsumL dT))%nat.
  Hypothesis HNC2 : (N <= C2)%nat.
  Hypothesis Hmask : (2 * n_maskD <= C2)%nat.

  Local Notation clsx := (@claimsD Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt).

  Lemma len_unitv : forall e, length (@unitv Fq2 fzero fone ftg e) = (2 * e + 2)%nat.
  Proof. intro e. unfold RowLayout.unitv. rewrite length_app, repeat_length. cbn. lia. Qed.

  Lemma flat_pairs_len : forall (cf : list F), length (flat_map (fun c => [c; fmul c ftg]) cf) = (2 * length cf)%nat.
  Proof. induction cf as [| c cf ih]; [reflexivity |]. cbn [flat_map app length]. rewrite ih. lia. Qed.

  Lemma len_gfunv : forall off degs r, length r = length degs ->
    length (@gfunv Fq2 fzero fmul ftg off (@funcv Fq2 fone fmul degs r)) = (2 * off + 2 * (1 + dsumL degs))%nat.
  Proof.
    intros off degs r h. unfold RowLayout.gfunv, RowLayout.funcv. rewrite length_app, repeat_length.
    rewrite flat_pairs_len. cbn [length].
    rewrite (fnl_length degs r h). lia.
  Qed.

  Lemma len_eqvec : forall x, length (@eqvec Fq2 fzero fone fadd fmul fsub n1 x) = N.
  Proof. intro x. apply DecLayout.eqvec_length. Qed.

  Lemma HLS_dec : forall cl t, In cl clsx -> In t cl -> kindD (tslot t) = true -> (length (tlv t) <= C2)%nat.
  Proof.
    intros cl t hcl ht hk.
    unfold claimsD in hcl. cbn [In] in hcl. destruct hcl as [<- | [<- | hcl]].
    - unfold DecLayout.clD in ht. destruct ht as [<- | ht].
      + unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv]. unfold DecLayout.wsv. eapply Nat.le_trans; [apply lincomb_length |]; [| exact HNC2].
        intro i. eapply Nat.le_trans; [apply nadj_length_le |]. rewrite DecLayout.eqvec_length. lia.
      + unfold DecLayout.digD in ht. apply in_concat in ht. destruct ht as (l & hl & ht).
        apply in_map_iff in hl. destruct hl as (d & <- & hd).
        destruct (@tabt_terms Fq2 fzero fone fadd fmul fsub _ _ _ _ _ _ _ ht) as (e & j & hj & er).
        rewrite e in hk. discriminate.
    - unfold DecLayout.clK in ht. destruct ht as [<- | [<- | []]]; unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv].
      + unfold DecLayout.wav. eapply Nat.le_trans; [apply nadj_length_le |]. rewrite DecLayout.eqvec_length. exact HNC2.
      + rewrite DecLayout.eqvec_length. exact HNC2.
    - apply in_app_or in hcl. destruct hcl as [hcl | hcl].
      + apply in_map_iff in hcl. destruct hcl as (d & <- & hd). apply in_seq in hd.
        unfold DecLayout.clZ in ht. apply in_app_or in ht. destruct ht as [ht | [<- | []]].
        * destruct (@tabt_terms Fq2 fzero fone fadd fmul fsub _ _ _ _ _ _ _ ht) as (e & j & hj & er).
          rewrite e in hk. discriminate.
        * unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv]. rewrite len_unitv. lia.
      + cbn [In] in hcl. destruct hcl as [<- | [<- | [<- | [<- | []]]]].
        * unfold DecLayout.clS in ht. destruct ht as [<- | [<- | []]]; unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv];
            [rewrite DecLayout.eqvec_length; exact HNC2 | rewrite len_unitv; lia].
        * unfold DecLayout.clE in ht. destruct ht as [<- | [<- | []]]; unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv];
            [rewrite DecLayout.eqvec_length; exact HNC2 | rewrite len_unitv; lia].
        * unfold DecLayout.clGm in ht. destruct ht as [<- | []]. unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv].
          rewrite len_gfunv by (rewrite Hrz, HdGl; reflexivity). unfold offG. lia.
        * unfold DecLayout.clTm in ht. destruct ht as [<- | []]. unfold DecLayout.gS, DecLayout.gE, DecLayout.gM; cbn [tlv].
          rewrite len_gfunv by (rewrite Hrt, HdTl; reflexivity). unfold offT, offG. lia.
  Qed.

  Lemma HdSx : forall avs aG csG aT csT, length avs = (kd + 2)%nat -> @shaped F dG csG -> @shaped F dT csT ->
    forall j, (j < 3)%nat -> length (dSx (avs, ((aG, csG), (aT, csT))) j) = C2.
  Proof.
    intros avs aG csG aT csT h7 hG hT j hj. unfold dSx.
    destruct (Nat.eqb_spec j 0); [exact Hs |]. destruct (Nat.eqb_spec j 1); [exact He |].
    unfold mrowZ, kmOf. cbn [fst snd]. rewrite length_app, flatZ_length, repeat_length, !length_app. cbn [length].
    rewrite (concat_len dG csG hG), (concat_len dT csT hT). lia.
  Qed.

  Lemma HdSw : forall j, (j < 3)%nat -> length (dSw j) = C2.
  Proof.
    intros j hj. unfold dSw. destruct (Nat.eqb_spec j 0); [exact Hs |]. destruct (Nat.eqb_spec j 1); [exact He |].
    apply repeat_length.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the join *)

  Variables (gB gS : list F) (JBz JSz : list Z).
  Variables dnB dnS : nat.
  Hypothesis HnBp : nB = (2 ^ dnB)%nat.
  Hypothesis HnSp : nS = (2 ^ dnS)%nat.
  Hypothesis HdJB : exists c nm c', get_I c (sb nm) nqB (Z.of_nat nB) = Some (JBz, c').
  Hypothesis HdJS : exists c nm c', get_I c (sb nm) nqS (Z.of_nat nS) = Some (JSz, c').
  Local Notation JB := (map Z.to_nat JBz).
  Local Notation JS := (map Z.to_nat JSz).
  Hypothesis HnB : forall i j, (i < nB)%nat -> (j < nB)%nat -> @pw Zq qone qmul omB i = @pw Zq qone qmul omB j -> i = j.
  Hypothesis HnS : forall i j, (i < nS)%nat -> (j < nS)%nat -> @pw Zq qone qmul omS i = @pw Zq qone qmul omS j -> i = j.
  Hypothesis HomB0 : omB <> qzero.
  Hypothesis HomS0 : omS <> qzero.
  Hypothesis Hkp : length kp = (kd + 6)%nat.
  Hypothesis Hgood : @goodspecs Fq2 fzero fone fmul fsub specsW.

  Lemma HJBnd : NoDup JB.
  Proof. destruct HdJB as (c & nm & c' & h). exact (drawn_nodup _ _ _ nm _ HnBp (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJSnd : NoDup JS.
  Proof. destruct HdJS as (c & nm & c' & h). exact (drawn_nodup _ _ _ nm _ HnSp (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJBlt : forall j, In j JB -> (j < nB)%nat.
  Proof. destruct HdJB as (c & nm & c' & h). apply Forall_forall. exact (drawn_indices _ _ _ nm _ HnBp (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJSlt : forall j, In j JS -> (j < nS)%nat.
  Proof. destruct HdJS as (c & nm & c' & h). apply Forall_forall. exact (drawn_indices _ _ _ nm _ HnSp (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJBlen : length JB = nqB.
  Proof. destruct HdJB as (c & nm & c' & h). rewrite length_map. exact (drawn_count _ _ _ nm _ HnBp (ex_intro _ c (ex_intro _ c' h))). Qed.
  Lemma HJSlen : length JS = nqS.
  Proof. destruct HdJS as (c & nm & c' & h). rewrite length_map. exact (drawn_count _ _ _ nm _ HnSp (ex_intro _ c (ex_intro _ c' h))). Qed.

  Local Notation RLD := (@RL2 Fq2 lf2 specsW dG dT).
  Local Notation simDLx := (@simDL Fq2 fzero fone fadd fmul fsub finv rz rt rhoG rhoT).
  Local Notation VwDLx := (@VwDL Fq2 fzero fone fadd fmul fsub fopp finv n1 ell base dtsW stabW etabW tz kG rz tt kT rt rhoG rhoT).
  Local Notation coinsK := (fun dS => coinsDO n1 ell lo1 lo2 kd nqB nqS dB dS JB JS).

  Definition hon2D (x : @rand2 F) y :=
    honDO n1 ell lo1 kd base omB omS dB (dSx x) aF ppF usF dG dT ptD th2 rz rt kp cc gB gS JB JS y.
  Definition f2D (x : @rand2 F) y :=
    oviewDO n1 ell lo1 kd base omB omS dB (dSx x) aF ppF usF dG dT ptD th2 rz rt kp cc gB gS JB JS y.
  Definition sim2D (v : @view2 F) w :=
    @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omB omS JB JS
      (LsB n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp) (LsS n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp)
      (cvVD (simDLx v))
      (shJB n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp cc JB)
      (shJS n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp cc JS)
      (shpB n1 ell lo1 kd gB JB) (shpS n1 ell lo1 kd gS JS) (GhB n1 ell lo1 kd gB JB) (GhS gS JS) w.

  Lemma coins_eqD : forall dS, coinsK dS = coinsK dSw.
  Proof. intro dS. cbv beta. unfold coinsDO, O3L, ZkDecOpen.datasS. rewrite !length_map. reflexivity. Qed.

  Lemma coins_nodupD : NoDup (coinsK dSw).
  Proof.
    exact (proj1 (dec_open_parts n1 ell lo1 lo2 kd base nqB nB nqS nS omB omS dB dSw HdB HdSw aF ppF usF dG dT ptD th2
                    rz rt HptD Hth2 Hrz Hrt HdGl HdTl Hlo1 kp cc gB gS Hkp JB JS HLS_dec HnB HnS HomB0 HomS0
                    HJBnd HJSnd HJBlt HJSlt HJBlen HJSlen _ eq_refl)).
  Qed.

  Lemma shaped_of_RLD : forall x, In x RLD ->
    length (fst x) = (kd + 2)%nat /\ @shaped F dG (snd (fst (snd x))) /\ @shaped F dT (snd (snd (snd x))).
  Proof.
    intros x hx. destruct (proj1 (@RL2_In Fq2 lf2 lf2_all specsW dG dT x) hx) as (h0 & hG & hT).
    split; [| split; assumption]. rewrite h0. unfold specsD. rewrite length_app, length_map, dtsW_length. reflexivity.
  Qed.

  Lemma open_parts_atD : forall x, In x RLD -> forall cv, cv = cvD n1 ell lo1 kd base dB (dSx x) aF ppF usF dG dT ptD th2 rz rt kp cc ->
    NoDup (coinsK dSw)
    /\ (forall y, In y (coinsK dSw) -> In (f2D x y) (coinsK dSw))
    /\ (forall y y', In y (coinsK dSw) -> In y' (coinsK dSw) -> f2D x y = f2D x y' -> y = y')
    /\ (forall w, In w (coinsK dSw) -> exists y, In y (coinsK dSw) /\ f2D x y = w)
    /\ (forall y, In y (coinsK dSw) ->
          hon2D x y = @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omB omS JB JS
                       (LsB n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp) (LsS n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp)
                       cv (shJB n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp cc JB)
                       (shJS n1 ell lo1 kd base aF ppF usF dG dT ptD th2 rz rt kp cc JS)
                       (shpB n1 ell lo1 kd gB JB) (shpS n1 ell lo1 kd gS JS) (GhB n1 ell lo1 kd gB JB) (GhS gS JS) (f2D x y)).
  Proof.
    intros x hx cv ecv. destruct (shaped_of_RLD x hx) as (h7 & hG & hT).
    destruct x as [avs [[aG csG] [aT csT]]]. cbn [fst snd] in h7, hG, hT.
    pose proof (dec_open_parts n1 ell lo1 lo2 kd base nqB nB nqS nS omB omS dB (dSx (avs, ((aG, csG), (aT, csT))))
                  HdB (HdSx avs aG csG aT csT h7 hG hT) aF ppF usF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdGl HdTl Hlo1
                  kp cc gB gS Hkp JB JS HLS_dec HnB HnS HomB0 HomS0 HJBnd HJSnd HJBlt HJSlt HJBlen HJSlen cv ecv) as hp.
    cbv beta in hp |- *. rewrite (coins_eqD (dSx (avs, ((aG, csG), (aT, csT))))) in hp. exact hp.
  Qed.

  (* Theorem 7.1, zero knowledge: the sumcheck layer and the opening of the decryption proof joined *)
  Theorem dec_zk :
    Permutation (map (fun p => (honDLx (fst p), hon2D (fst p) (snd p))) (list_prod RLD (coinsK dSw)))
                (map (fun v => (simDLx (fst v), sim2D (fst v) (snd v))) (list_prod RLD (coinsK dSw))).
  Proof.
    destruct (@dec_layer_parts Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field lf2 lf2_NoDup lf2_all
                n1 ell base Hn1 Hchar dtsW stabW etabW Hdig Htern tz kG rz tt kT rt rhoG rhoT Hrz Hrt Hgood HrhoG HrhoT)
      as (n1L & i1 & j1 & s1 & e1).
    assert (hcv : forall x, In x RLD ->
              cvD n1 ell lo1 kd base dB (dSx x) aF ppF usF dG dT ptD th2 rz rt kp cc = cvVD (simDLx (VwDLx x))).
    { intros x hx. rewrite <-(e1 x hx). destruct (shaped_of_RLD x hx) as (h7 & hG & hT).
      destruct x as [avs [[aG csG] [aT csT]]]. cbn [fst snd] in h7, hG, hT.
      exact (cv_honest_dec avs aG csG aT csT h7 hG hT). }
    apply (zk_join VwDLx honDLx simDLx RLD RLD f2D hon2D sim2D (coinsK dSw) (coinsK dSw)).
    - exact n1L.
    - exact n1L.
    - exact coins_nodupD.
    - exact coins_nodupD.
    - exact i1.
    - exact j1.
    - exact s1.
    - exact e1.
    - intros x y hx hy. exact (proj1 (proj2 (open_parts_atD x hx (cvVD (simDLx (VwDLx x))) (eq_sym (hcv x hx)))) y hy).
    - intros x y y' hx hy hy' e. exact (proj1 (proj2 (proj2 (open_parts_atD x hx (cvVD (simDLx (VwDLx x))) (eq_sym (hcv x hx))))) y y' hy hy' e).
    - intros x w hx hw. exact (proj1 (proj2 (proj2 (proj2 (open_parts_atD x hx (cvVD (simDLx (VwDLx x))) (eq_sym (hcv x hx)))))) w hw).
    - intros x y hx hy. unfold sim2D. exact (proj2 (proj2 (proj2 (proj2 (open_parts_atD x hx (cvVD (simDLx (VwDLx x))) (eq_sym (hcv x hx)))))) y hy).
  Qed.

End DecJoin.
