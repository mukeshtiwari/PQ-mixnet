(* Prover side: the shape of the prover's output (wf_parts of ExecSerial.v),
   so that the verifier's parser reads it back (parse_ser).

   Generic pieces: reducedness of the vector operations, the messages and
   final values of the sumcheck prover, lengths of hashes, Merkle paths,
   columns and rows. The theorem prove_wf is at the end of this file, under
   explicit hypotheses on the parameters, the coins and the shape of the
   witness. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecVerify ExecMerkle ExecProveBase ExecSerial ExecFold ExecFront ExecNtt ExecDec ExecClaims. From Crypto Require Import MixLayout.
Import ListNotations.
Local Open Scope list_scope.

(* ---------------------------------------------------------------------- *)
(* reducedness *)

Lemma xzero_reduced : reduced xzero.
Proof. split; cbn; pose proof Q_pos; lia. Qed.

Lemma xfsum_reduced : forall l, reduced (xfsum l).
Proof. intros [| x l]; [exact xzero_reduced | apply xadd_reduced]. Qed.

Lemma xpadd_reduced : forall p q, Forall reduced p -> Forall reduced q -> Forall reduced (xpadd p q).
Proof.
  induction p as [| x p ih]; intros q hp hq; [exact hq |].
  destruct q as [| y q]; [exact hp |]. cbn [xpadd]. constructor; [apply xadd_reduced |].
  inversion hp; inversion hq; subst. apply ih; assumption.
Qed.

Lemma xpscale_reduced : forall c p, Forall reduced (xpscale c p).
Proof. intros c p. apply Forall_map, Forall_forall. intros. apply xmul_reduced. Qed.

Lemma nth_reduced : forall l i, Forall reduced l -> reduced (nth i l xzero).
Proof.
  intros l i h. destruct (Nat.lt_ge_cases i (List.length l)) as [hi | hi].
  + rewrite Forall_forall in h. apply h, nth_In, hi.
  + rewrite nth_overflow by exact hi. exact xzero_reduced.
Qed.

(* a fold of scaled rows, as in ExecProve.comb *)
Definition fcomb (rows : nat -> list Z) (cb : list (nat * xf)) : list xf :=
  fold_right (fun iw acc => xpadd (xpscale (snd iw) (map bx (rows (fst iw)))) acc) [] cb.

Lemma fcomb_reduced : forall rows cb, Forall reduced (fcomb rows cb).
Proof.
  intros rows cb. induction cb as [| iw cb ih]; [constructor |].
  cbn [fcomb fold_right]. apply xpadd_reduced; [apply xpscale_reduced | exact ih].
Qed.

Lemma fcomb_length_le : forall rows cb kk, Forall (fun iw => (List.length (rows (fst iw)) <= kk)%nat) cb ->
  (List.length (fcomb rows cb) <= kk)%nat.
Proof.
  intros rows cb kk h. unfold fcomb. induction h as [| iw cb hiw hcb ih]; [cbn; lia |].
  cbn [fold_right]. rewrite xpadd_length. unfold xpscale in *. rewrite !length_map. lia.
Qed.

Lemma fcomb_length_eq : forall rows cb kk, Forall (fun iw => (List.length (rows (fst iw)) <= kk)%nat) cb ->
  (exists iw, In iw cb /\ List.length (rows (fst iw)) = kk) -> List.length (fcomb rows cb) = kk.
Proof.
  intros rows cb kk h (iw & hin & hl). apply Nat.le_antisymm; [apply fcomb_length_le; exact h |].
  unfold fcomb. induction cb as [| iw' cb ih]; [destruct hin |].
  cbn [fold_right]. rewrite xpadd_length. unfold xpscale in *. rewrite !length_map.
  destruct hin as [<- | hin]; [lia |]. inversion h; subst. specialize (ih H2 hin). lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* the sumcheck prover's messages and final values *)

Lemma last_uni_reduced : forall z t mk x, reduced (last_uni z t mk x).
Proof. intros z t [a |] x; unfold last_uni, xext; apply xadd_reduced. Qed.

Lemma sc_loop_shape : forall draw name tmask terms a0 cs rho ds j tables point ch msgs pt fin ch',
  (forall d, In d ds -> (1 <= d)%nat) ->
  sc_loop draw name tmask terms a0 cs rho ds j tables point ch = Some (msgs, pt, fin, ch') ->
  Forall2 msg_ok msgs ds /\ Forall reduced fin.
Proof.
  intros draw name tmask terms a0 cs rho. induction ds as [| d ds ih]; intros j tables point ch msgs pt fin ch' hd H.
  { cbn [sc_loop] in H. injection H as <- <- <- <-. split; constructor. }
  cbn [sc_loop] in H.
  destruct (draw _ _) as [[rl chr] |] eqn:hg; [| discriminate].
  rewrite bindo_some in H. cbv beta in H.
  assert (hv : forall (f g : nat -> xf), msg_ok (map (fun c => xadd (f c) (g c)) (spoints d)) d).
  { intros f g. split; [rewrite length_map; apply spoints_length; apply hd; left; reflexivity |].
    apply Forall_map, Forall_forall. intros. apply xadd_reduced. }
  destruct ds as [| d' ds']; cbv beta iota zeta in H.
  - injection H as <- <- <- <-. split.
    + constructor; [apply hv | constructor].
    + unfold last_vals. apply Forall_map, Forall_forall. intros. apply last_uni_reduced.
  - destruct (sc_loop draw name tmask terms a0 cs rho (d' :: ds') (S j) _ _ (snd (rl, chr)))
      as [[[[ms pt0] fin0] ch0] |] eqn:hrec; [| discriminate].
    rewrite bindo_some in H. injection H as <- <- <- <-.
    destruct (ih _ _ _ _ _ _ _ _ (fun d0 h0 => hd d0 (or_intror h0)) hrec) as [h1 h2].
    split; [constructor; [apply hv | exact h1] | exact h2].
Qed.

(* ---------------------------------------------------------------------- *)
(* hashes, roots, paths *)

Lemma up_hashes : forall l, Forall (fun h => List.length h = 32%nat) (up l).
Proof.
  fix ih 1. intros [| x [| y r]]; cbn [up]; try constructor.
  + apply sha256_length.
  + apply ih.
Qed.

Lemma upn_root : forall d l, List.length l = (2 ^ S d)%nat -> List.length (nth 0 (upn (S d) l) []) = 32%nat.
Proof.
  induction d as [| d ih]; intros l hl.
  + cbn [upn]. destruct l as [| x [| y [| z r]]]; cbn in hl; try lia. cbn. apply sha256_length.
  + cbn [upn]. apply (ih (up l)). apply (up_length l (2 ^ S d)).
    replace (2 * 2 ^ S d)%nat with (2 ^ S (S d))%nat by (cbn [Nat.pow]; lia). exact hl.
Qed.

Lemma broot_length : forall om n d msgs salts, (1 <= d)%nat -> List.length salts = (2 ^ d)%nat -> n = (2 ^ d)%nat ->
  List.length (broot (commit om n d msgs salts)) = 32%nat.
Proof.
  intros om n d msgs salts hd hs hn. unfold broot. change (blayers (commit om n d msgs salts))
    with (layers d (leaves_of (commit om n d msgs salts))).
  rewrite last_layers. destruct d as [| d]; [lia |]. apply upn_root.
  unfold leaves_of. rewrite length_map, length_combine, bcols_length. cbn [commit bsalts]. lia.
Qed.

Lemma mpath_length : forall d l j, List.length (mpath d l j) = d.
Proof. induction d as [| d ih]; intros l j; [reflexivity | cbn; rewrite ih; reflexivity]. Qed.

Lemma sib_lt : forall d j, (j < 2 ^ S d)%nat -> (sib j < 2 ^ S d)%nat.
Proof.
  intros d j hj. unfold sib. destruct (Nat.Even_or_Odd j) as [[q ->] | [q ->]].
  + rewrite Nat.even_mul. cbn [Nat.even orb]. cbn [Nat.pow] in hj |- *.
    assert (h2 : (2 * q + 1 <> 2 ^ d + (2 ^ d + 0))%nat).
    { intro e. replace (2 ^ d + (2 ^ d + 0))%nat with (2 * 2 ^ d)%nat in e by lia. lia. }
    lia.
  + rewrite Nat.even_add, Nat.even_mul. cbn [Nat.even orb negb Bool.eqb]. lia.
Qed.

Lemma mpath_hashes : forall d l j, Forall (fun h => List.length h = 32%nat) l -> List.length l = (2 ^ d)%nat ->
  (j < 2 ^ d)%nat -> Forall (fun h => List.length h = 32%nat) (mpath d l j).
Proof.
  induction d as [| d ih]; intros l j hl hlen hj; [constructor |].
  cbn [mpath]. constructor.
  + rewrite Forall_forall in hl. apply hl, nth_In. rewrite hlen. apply sib_lt. exact hj.
  + apply ih.
    * apply up_hashes.
    * apply up_length. rewrite hlen. cbn [Nat.pow]. lia.
    * rewrite Nat.div2_div. apply Nat.Div0.div_lt_upper_bound. cbn [Nat.pow] in hj. lia.
Qed.

Lemma leaves_hashes : forall bt, Forall (fun h => List.length h = 32%nat) (leaves_of bt).
Proof. intro bt. unfold leaves_of, leaf_hash. apply Forall_map, Forall_forall. intros. apply sha256_length. Qed.

(* ---------------------------------------------------------------------- *)
(* columns *)

Lemma zhorner_red : forall p x, zred (zhorner p x).
Proof.
  intros [| c p] x; cbn [zhorner]; [split; [lia | exact Q_pos] |]. split; apply Z.mod_pos_bound; exact Q_pos.
Qed.

Lemma commit_col : forall om n d msgs salts j, (j < n)%nat ->
  nth j (bcols (commit om n d msgs salts)) [] = map (fun msg => nth j (zenc om n msg) 0%Z) msgs.
Proof.
  intros om n d msgs salts j hj. cbn [commit bcols].
  rewrite (transpose_spec 0%Z) by (apply Forall_map, Forall_forall; intros; apply zenc_length).
  rewrite (nth_indep _ [] (map (fun r => nth 0 r 0%Z) (map (zenc om n) msgs))) by (rewrite length_map, length_seq; exact hj).
  rewrite (map_nth (fun i => map (fun r => nth i r 0%Z) (map (zenc om n) msgs)) (seq 0 n) 0%nat j), seq_nth by exact hj.
  rewrite map_map. reflexivity.
Qed.

Lemma commit_col_ok : forall om n d msgs salts j, (j < n)%nat ->
  List.length (nth j (bcols (commit om n d msgs salts)) []) = List.length msgs
  /\ Forall zred (nth j (bcols (commit om n d msgs salts)) []).
Proof.
  intros om n d msgs salts j hj. rewrite commit_col by exact hj. split; [apply length_map |].
  apply Forall_map, Forall_forall. intros msg _. rewrite zenc_spec. unfold zenc_horner.
  rewrite (nth_indep _ 0%Z (zhorner msg 0%Z)) by (rewrite length_map, zpows_length; exact hj).
  rewrite map_nth. apply zhorner_red.
Qed.

Theorem bitem_ok : forall om n d msgs salts cnt j,
  n = (2 ^ d)%nat -> log2n 64 n = d -> List.length salts = n -> Forall (fun s => List.length s = 16%nat) salts ->
  List.length msgs = cnt -> (j < n)%nat ->
  item_ok cnt (log2n 64 n) (bitem (commit om n d msgs salts) j).
Proof.
  intros om n d msgs salts cnt j hn ed hs hs16 hm hj.
  destruct (commit_col_ok om n d msgs salts j hj) as [hc1 hc2].
  unfold bitem, item_ok. split; [rewrite hc1; exact hm |]. split; [exact hc2 |]. split.
  + cbn [commit bsalts]. rewrite Forall_forall in hs16. apply hs16, nth_In.
    apply (Nat.lt_le_trans _ n); [exact hj | apply Nat.eq_le_incl; symmetry; exact hs].
  + change (blayers (commit om n d msgs salts)) with (layers d (leaves_of (commit om n d msgs salts))).
    rewrite lpath_layers, ed. split; [apply mpath_length |].
    apply mpath_hashes; [apply leaves_hashes | | lia].
    unfold leaves_of. rewrite length_map, length_combine, bcols_length. cbn [commit bsalts].
    transitivity (Nat.min n n); [f_equal; exact hs | lia].
Qed.

(* ---------------------------------------------------------------------- *)
(* rows *)

Lemma chunks_shape : forall {A : Type} (C q fuel : nat) (l : list A), (0 < C)%nat -> List.length l = (q * C)%nat ->
  (q <= fuel)%nat -> List.length (chunks fuel C l) = q /\ Forall (fun r => List.length r = C) (chunks fuel C l).
Proof.
  intros A C q. induction q as [| q ih]; intros fuel l hC hl hf.
  + destruct l; [| cbn in hl; lia]. destruct fuel; split; constructor.
  + destruct fuel as [| f]; [lia |]. destruct l as [| x l']; [cbn in hl; lia |].
    cbn [chunks]. destruct (ih f (skipn C (x :: l')) hC ltac:(rewrite length_skipn, hl; lia) ltac:(lia)) as [h1 h2].
    split; [cbn; rewrite h1; reflexivity |]. constructor; [rewrite length_firstn, hl; lia | exact h2].
Qed.

Lemma split_rows_shape : forall lo M (l : list Z), List.length l = (2 ^ M)%nat ->
  List.length (split_rows (2 ^ lo) l) = (2 ^ (M - Nat.min lo M))%nat
  /\ Forall (fun r => (List.length r <= 2 ^ lo)%nat) (split_rows (2 ^ lo) l).
Proof.
  intros lo M l hl. unfold split_rows. destruct (Nat.leb_spec (List.length l) (2 ^ lo)) as [hle | hgt].
  + assert (hM : (M <= lo)%nat).
    { destruct (Nat.le_gt_cases M lo) as [h | h]; [exact h |].
      assert (2 ^ lo < 2 ^ M)%nat by (apply Nat.pow_lt_mono_r; lia). lia. }
    replace (M - Nat.min lo M)%nat with 0%nat by lia. split; [reflexivity | constructor; [exact hle | constructor]].
  + assert (hM : (lo < M)%nat).
    { destruct (Nat.le_gt_cases M lo) as [h | h]; [| exact h].
      assert (2 ^ M <= 2 ^ lo)%nat by (apply Nat.pow_le_mono_r; lia). lia. }
    replace (Nat.min lo M) with lo by lia.
    assert (hq : List.length l = (2 ^ (M - lo) * 2 ^ lo)%nat) by (rewrite hl, <-Nat.pow_add_r; f_equal; lia).
    destruct (chunks_shape (2 ^ lo) (2 ^ (M - lo)) (List.length l) l ltac:(apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia)
                hq ltac:(rewrite hq; apply Nat.le_mul_r, Nat.pow_nonzero; lia)) as [h1 h2].
    split; [exact h1 |]. eapply Forall_impl; [| exact h2]. intros r hr. cbv beta in *. rewrite hr. apply le_n.
Qed.

Lemma padrow_length : forall C row pads, (List.length row <= C)%nat ->
  List.length (padrow C row pads) = (C + List.length pads)%nat.
Proof. intros C row pads h. unfold padrow. rewrite !length_app, length_map, repeat_length. lia. Qed.

Lemma padrows_shape : forall C (rows pads : list (list Z)) nq,
  Forall (fun r => (List.length r <= C)%nat) rows -> Forall (fun p => List.length p = nq) pads ->
  List.length pads = List.length rows ->
  List.length (map (fun p => padrow C (fst p) (snd p)) (combine rows pads)) = List.length rows
  /\ Forall (fun r => List.length r = (C + nq)%nat) (map (fun p => padrow C (fst p) (snd p)) (combine rows pads)).
Proof.
  intros C rows pads nq hr hp hl. split; [rewrite length_map, length_combine; lia |].
  apply Forall_map, Forall_forall. intros [r p] hin. cbn [fst snd].
  rewrite padrow_length by (rewrite Forall_forall in hr; apply hr, (in_combine_l _ _ _ _ hin)).
  rewrite Forall_forall in hp. rewrite (hp p (in_combine_r _ _ _ _ hin)). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the rows the claims' terms refer to *)

Lemma xhi_length : forall lo x, List.length (xhi_coefs lo x) = (2 ^ (List.length x - Nat.min lo (List.length x)))%nat.
Proof.
  intros lo x. unfold xhi_coefs. destruct (Nat.ltb_spec lo (List.length x)) as [h | h].
  + rewrite xeq_table_length, length_skipn. f_equal. lia.
  + replace (List.length x - Nat.min lo (List.length x))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma xtabt_rows : forall slot start coef lo x t, In t (xtabt slot start coef lo x) ->
  tslotx t = slot /\ (start <= trowx t < start + List.length (xhi_coefs lo x))%nat.
Proof.
  intros slot start coef lo x t h. unfold xtabt in h. apply in_map_iff in h. destruct h as (i & <- & hi).
  apply in_seq in hi. unfold tslotx, trowx. cbn. lia.
Qed.

Section Rows.

  Variables n1 ell lo1 lo2 : nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation rw := (MixLayout.rw n1 ell lo1).
  Local Notation rs := (MixLayout.rs ell lo2).
  Variable SO : nat.
  Variables (dA dB dC : list nat) (invN : xf) (r ry rz : list xf) (rhoB mrp1 mrp2 mrp3 : xf).
  Hypothesis Hr : List.length r = ell.
  Hypothesis Hry : List.length ry = n1.
  Hypothesis Hrz : List.length rz = m.

  (* slots 1, 2 live on the first 3 rw rows (big matrix); slots 3, 4 on the small matrix *)
  Definition row_ok (t : xterm) : Prop :=
    (1 <= tslotx t <= 4)%nat
    /\ ((tslotx t <= 2)%nat -> (trowx t < 3 * rw)%nat)
    /\ ((3 <= tslotx t)%nat -> (SO <= trowx t < SO + (rs + 6) + (4 * rs + 1))%nat).

  Theorem xclaims9_rows : forall cl t, In cl (xclaims9 n1 ell lo1 lo2 SO dA dB dC invN r ry rz rhoB mrp1 mrp2 mrp3) ->
    In t cl -> row_ok t.
  Proof.
    assert (hb : forall slot k coef x t, (slot = 1 \/ slot = 2)%nat -> (k < 3)%nat -> List.length x = m ->
              In t (xtabt slot (rW n1 ell lo1 k) coef lo1 x) -> row_ok t).
    { intros slot k coef x t hs hk hx h. destruct (xtabt_rows _ _ _ _ _ _ h) as [e1 e2].
      rewrite xhi_length, hx in e2. unfold row_ok, MixLayout.rw, rW, MixLayout.rw, RowLayout.hiE in *.
      rewrite e1. split; [lia |]. split; [| lia]. intros _. nia. }
    assert (hs : forall start coef t, (SO <= start)%nat -> (start + rs <= SO + (rs + 6) + (4 * rs + 1))%nat ->
              In t (xtabt 3 start coef lo2 r) -> row_ok t).
    { intros start coef t h1 h2 h. destruct (xtabt_rows _ _ _ _ _ _ h) as [e1 e2].
      rewrite xhi_length, Hr in e2. unfold row_ok, MixLayout.rs, RowLayout.hiE in *. rewrite e1. lia. }
    assert (h4 : forall coef lv t, t = xgt4 ell lo2 SO coef lv -> row_ok t).
    { intros coef lv t ->. unfold row_ok, xgt4, tslotx, trowx, MixLayout.rM. cbn. lia. }
    assert (hyr : List.length (ry ++ r) = m) by (rewrite length_app; lia).
    intros cl t hcl ht. unfold xclaims9 in hcl. cbn [In] in hcl.
    unfold MixLayout.rU0, MixLayout.rU1, MixLayout.rUh0, MixLayout.rUh1, MixLayout.rSg in *.
    destruct hcl as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]];
      unfold xcl1, xcl2, xcl3, xcl4, xcl5, xcl6, xcl7, xcl8, xcl9 in ht;
      repeat (apply in_app_or in ht; destruct ht as [ht | ht]);
      first [ eapply hs; [| | exact ht]; unfold MixLayout.rU0, MixLayout.rU1, MixLayout.rUh0, MixLayout.rUh1, MixLayout.rSg; lia
            | eapply hb; [| | | exact ht]; [lia | lia | assumption]
            | destruct ht as [ht | ht]; [eapply h4; symmetry; exact ht | destruct ht as [ht | []]; eapply h4; symmetry; exact ht]
            | destruct ht as [ht | []]; eapply h4; symmetry; exact ht
            ].
  Qed.

End Rows.

Lemma xgbatch_rows : forall kp cls v iw, In iw (xgbatch kp cls v) ->
  exists cl t, In cl cls /\ In t cl /\ tslotx t = v /\ fst iw = trowx t.
Proof.
  induction kp as [| k0 kp ih]; intros cls v iw h; [destruct h |]. destruct cls as [| cl cls]; [destruct h |].
  cbn [xgbatch] in h. apply in_app_or in h. destruct h as [h | h].
  + exists cl. induction cl as [| t cl ihc]; [destruct h |]. cbn [xgsel] in h.
    destruct (Nat.eqb_spec (tslotx t) v) as [e | ne].
    * destruct h as [<- | h]; [exists t; split; [left; reflexivity | split; [left; reflexivity | split; [exact e | reflexivity]]] |].
      destruct (ihc h) as (t' & _ & ht' & e1 & e2). exists t'. split; [left; reflexivity | split; [right; exact ht' | split; assumption]].
    * destruct (ihc h) as (t' & _ & ht' & e1 & e2). exists t'. split; [left; reflexivity | split; [right; exact ht' | split; assumption]].
  + destruct (ih cls v iw h) as (cl' & t & h1 & h2 & h3 & h4). exists cl', t. split; [right; exact h1 | split; [exact h2 | split; assumption]].
Qed.

Lemma degs_pos : forall ell n1, (forall d, In d (dAE ell) -> (1 <= d)%nat) /\ (forall d, In d (dBE n1) -> (1 <= d)%nat)
  /\ (forall d, In d (dCE n1 ell) -> (1 <= d)%nat).
Proof.
  intros ell n1. unfold dAE, dBE, dCE. split; [| split]; intros d h; apply in_map_iff in h; destruct h as (i & <- & _);
    try (destruct (Nat.eqb _ _)); lia.
Qed.
