(* Zero knowledge, step Z4: the opening of the shuffle proof with the honest
   prover instantiated (paper, Theorem 5.3, steps (4) to (6)).

   ZkJoin.open3_zk with K = Z_q, F = GF(q^2), emb x = (x, 0):
     data rows     the rows of the extracted prover that hold data (W, sigma,
                   the two halves of u and uhat, the mask table), without
                   their pads; the pads are the coins;
     slot vectors  v1, v2 (big matrix) and v3, v4 (small matrix): shift
                   c * (the batched rows of the slot); their masks are the
                   F-rows stored as two rows over Z_q;
     proximity     gamma-combination of the data rows (tp) plus the part of
                   the rows that hold the slot masks (G: their two
                   coordinates, re and im);
   and the check equations Hmu, Hsh, Hsp, HG proven from the layout
   (batch_honest of ExecBackO.v for Hmu, linearity of the encoding for the
   others). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Utility Require Import Zpstar.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks ZkSumcheck ZkOpen ZkTranscript ZkOpenTranscript ZkJoin SlotKinds Opening MixLayout OpenClaims. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecVerify ExecProveBase ExecFold ExecProve ExecRows ExecNtt ExecBack ExecBackD ExecBackO.
Import ListNotations.

Add Field fieldF2m : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Add Field fieldZq : (@field_theory_for_stdlib_tactic Zq eq qzero qone qopp qadd qmul qsub qinv qdiv Zq_field).

Local Notation F := Fq2.
Local Notation peval := (@eval Fq2 fzero fadd fmul).
Local Notation pwF := (@pw Fq2 fone fmul).
Local Notation pwK := (@pw Zq qone qmul).
Local Notation padd := (@LogDer.padd Fq2 fadd).
Local Notation pscale := (@LogDer.pscale Fq2 fmul).
Local Notation vadd := (@LogDer.vadd Fq2 fadd).
Local Notation msumF := (@msum Fq2 fadd fmul).

(* ---------------------------------------------------------------------- *)
(* the base field inside GF(q^2) *)

Definition emb (x : Zq) : F := (x, qzero).
Definition re (x : F) : F := (fst x, qzero).
Definition im (x : F) : F := (snd x, qzero).

Lemma emb_add : forall x y, emb (qadd x y) = fadd (emb x) (emb y).
Proof.
  intros x y. unfold emb, fadd, eadd. cbn [fst snd]. f_equal. ring.
Qed.

Lemma emb_bx : forall z, to_F (bx z) = emb (zq_of z).
Proof. intro z. unfold to_F, bx, emb. cbn [fst snd]. rewrite zq_of_0. reflexivity. Qed.

Lemma re_add : forall x y, re (fadd x y) = fadd (re x) (re y).
Proof.
  intros [a b] [c d]. unfold re, fadd, eadd. cbn [fst snd]. f_equal. ring.
Qed.
Lemma im_add : forall x y, im (fadd x y) = fadd (im x) (im y).
Proof.
  intros [a b] [c d]. unfold im, fadd, eadd. cbn [fst snd]. f_equal. ring.
Qed.

(* multiplying by a base-field element commutes with taking a coordinate *)
Lemma re_emb_mul : forall a x, re (fmul (emb a) x) = fmul (emb a) (re x).
Proof.
  intros a [x1 x2]. unfold re, emb, fmul, emul. cbn [fst snd]. f_equal; ring.
Qed.
Lemma im_emb_mul : forall a x, im (fmul (emb a) x) = fmul (emb a) (im x).
Proof.
  intros a [x1 x2]. unfold im, emb, fmul, emul. cbn [fst snd]. f_equal; ring.
Qed.

Lemma re_zero : re fzero = fzero. Proof. reflexivity. Qed.
Lemma im_zero : im fzero = fzero. Proof. reflexivity. Qed.

Lemma emb_pw : forall a k, pwF (emb a) k = emb (pwK a k).
Proof.
  intros a k. induction k as [| k ih]; [reflexivity |]. cbn [Negacyclic.pw]. rewrite ih.
  unfold emb, fmul, emul. cbn [fst snd]. f_equal; ring.
Qed.

Lemma eval_re : forall p om, re (peval p (emb om)) = peval (map re p) (emb om).
Proof.
  induction p as [| c p ih]; intro om; [reflexivity |].
  cbn [map PolyRoots.eval]. rewrite re_add, re_emb_mul, ih. reflexivity.
Qed.
Lemma eval_im : forall p om, im (peval p (emb om)) = peval (map im p) (emb om).
Proof.
  induction p as [| c p ih]; intro om; [reflexivity |].
  cbn [map PolyRoots.eval]. rewrite im_add, im_emb_mul, ih. reflexivity.
Qed.

(* the encoding of an embedded row is the embedding of its encoding *)
Lemma emb_mul : forall x y, emb (qmul x y) = fmul (emb x) (emb y).
Proof.
  intros x y. unfold emb, fmul, emul. cbn [fst snd]. f_equal; ring.
Qed.

Lemma eval_emb : forall p om, peval (map emb p) (emb om) = emb (@eval Zq qzero qadd qmul p om).
Proof.
  induction p as [| c p ih]; intro om; [reflexivity |].
  cbn [map PolyRoots.eval]. rewrite ih, emb_add, emb_mul. reflexivity.
Qed.

Definition Zof (x : Zq) : Z := @Zpfield.v Q x.

Lemma zq_of_Zof : forall x, zq_of (Zof x) = x.
Proof. intro x. apply zq_eq. unfold Zof, zq_of. cbn. apply Z.mod_small. apply zq_bound. Qed.

Lemma emb_bx_Zof : forall x, to_F (bx (Zof x)) = emb x.
Proof. intro x. rewrite emb_bx, zq_of_Zof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* encoding at the opened columns *)

Section Enc.

  Variable om : Zq.
  Variable J : list nat.

  Local Notation enc := (@encJ Fq2 fzero fone fadd fmul (emb om) J).

  Lemma rs_enc_emb : forall p j, @rs_enc Fq2 fzero fone fadd fmul (emb om) (map emb p) j
                                 = emb (@rs_enc Zq qzero qone qadd qmul om p j).
  Proof. intros p j. unfold ReedSolomon.rs_enc. rewrite emb_pw, eval_emb. reflexivity. Qed.

  Lemma enc_emb : forall d pads, enc (map emb (d ++ pads)) = map emb (@opened Zq qzero qone qadd qmul om d pads J).
  Proof.
    intros d pads. unfold ZkOpenTranscript.encJ, ReedSolomon.opened. rewrite map_map. apply map_ext. intro j.
    apply rs_enc_emb.
  Qed.

  Lemma enc_re : forall m, enc (map re m) = map re (enc m).
  Proof.
    intro m. unfold ZkOpenTranscript.encJ. rewrite map_map. apply map_ext. intro j.
    unfold ReedSolomon.rs_enc. rewrite emb_pw, eval_re. reflexivity.
  Qed.
  Lemma enc_im : forall m, enc (map im m) = map im (enc m).
  Proof.
    intro m. unfold ZkOpenTranscript.encJ. rewrite map_map. apply map_ext. intro j.
    unfold ReedSolomon.rs_enc. rewrite emb_pw, eval_im. reflexivity.
  Qed.

  Lemma enc_pscale : forall c p, enc (pscale c p) = map (fmul c) (enc p).
  Proof.
    intros c p. unfold ZkOpenTranscript.encJ. rewrite map_map. apply map_ext. intro j.
    unfold ReedSolomon.rs_enc. apply (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
  Qed.

  Lemma enc_nil : enc [] = map (fun _ => fzero) J.
  Proof. reflexivity. Qed.

  (* the batched combination of rows, at the opened columns *)
  Fixpoint msumJ (E : nat -> list F) (cb : list (nat * F)) : list F :=
    match cb with
    | [] => map (fun _ => fzero) J
    | iw :: cb' => vadd (map (fmul (snd iw)) (E (fst iw))) (msumJ E cb')
    end.

  Lemma enc_msum : forall (P : nat -> list F) cb, enc (msumF P cb) = msumJ (fun i => enc (P i)) cb.
  Proof.
    intro P. induction cb as [| [i w] cb ih]; [reflexivity |].
    cbn [Opening.msum msumJ fst snd]. rewrite (@encJ_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), enc_pscale, ih.
    reflexivity.
  Qed.

End Enc.

Lemma padrow_split : forall C row pads, padrow C row pads = padrow C row [] ++ pads.
Proof. intros C row pads. unfold padrow. rewrite app_nil_r, app_assoc. reflexivity. Qed.

Lemma rowF : forall C row p, map to_F (map bx (padrow C row (map Zof p))) = map emb (map zq_of (padrow C row []) ++ p).
Proof.
  intros C row p. rewrite padrow_split, !map_app, !map_map. f_equal.
  + apply map_ext. intro z. apply emb_bx.
  + apply map_ext. intro x. apply emb_bx_Zof.
Qed.

Lemma msum_ext : forall (P P' : nat -> list F) cb, (forall iw, In iw cb -> P (fst iw) = P' (fst iw)) ->
  msumF P cb = msumF P' cb.
Proof.
  intros P P'; induction cb as [| iw cb ih]; intro h; [reflexivity |]. cbn [Opening.msum].
  rewrite (h iw (or_introl eq_refl)), ih by (intros iw' hi; apply h; right; exact hi). reflexivity.
Qed.

Lemma msumJ_ext : forall J (E E' : nat -> list F) cb, (forall iw, In iw cb -> E (fst iw) = E' (fst iw)) ->
  msumJ J E cb = msumJ J E' cb.
Proof.
  intros J E E'; induction cb as [| iw cb ih]; intro h; [reflexivity |]. cbn [msumJ].
  rewrite (h iw (or_introl eq_refl)), ih by (intros iw' hi; apply h; right; exact hi). reflexivity.
Qed.

Lemma msum_length : forall (P : nat -> list F) cb L, (forall iw, In iw cb -> (length (P (fst iw)) <= L)%nat) ->
  (length (msumF P cb) <= L)%nat.
Proof.
  intros P; induction cb as [| iw cb ih]; intros L h; [cbn; lia |]. cbn [Opening.msum].
  rewrite (@length_padd Fq2 fadd), (@length_pscale Fq2 fmul).
  pose proof (h iw (or_introl eq_refl)). pose proof (ih L (fun iw' hi => h iw' (or_intror hi))). lia.
Qed.

Lemma nth_zipw : forall {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B) i da db dc,
  (i < length la)%nat -> length la = length lb -> nth i (zipw f la lb) dc = f (nth i la da) (nth i lb db).
Proof.
  intros A B C f; induction la as [| x la ih]; intros lb i da db dc hi hl; destruct lb as [| y lb]; cbn in hl, hi; try lia.
  destruct i as [| i]; [reflexivity |]. cbn [zipw nth]. apply ih; lia.
Qed.

Lemma nth_rep : forall {A : Type} (x d : A) m i, (i < m)%nat -> nth i (repeat x m) d = x.
Proof.
  intros A x d m; induction m as [| m ih]; intros i hi; [lia |].
  destruct i as [| i]; [reflexivity |]. cbn [repeat nth]. apply ih. lia.
Qed.

Section MixOpen.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable k : coins.                   (* only its mask table and salts are used *)
  Variable T : ptrace.                  (* the challenges *)

  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation SO := (SOE n1 ell lo1).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).
  Local Notation pok := (params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS).
  Local Notation PFx := (PF ell lo1 lo2 nB nS omB omS pplain a b cin cout sig wr we1 we2).

  (* the data rows, without their pads *)
  Definition dB (i : nat) : list Zq :=
    map zq_of (padrow C1 (nth (i mod rw) (split_rows C1 (nth (i / rw) (Wk wr we1 we2) [])) []) []).
  Definition datasB : list (list Zq) := map dB (seq 0 (3 * rw)).

  Definition dS (j : nat) : list Zq :=
    if Nat.ltb j rs then map zq_of (padrow C2 (nth j (split_rows C2 (sigZ sig)) []) [])
    else if Nat.ltb j (rs + 4 * rs) then
      map zq_of (padrow C2 (nth ((j - rs) mod rs) (split_rows C2 (nth ((j - rs) / rs) (s2rows ell pplain a b cin cout sig wr we1 we2 T) [])) []) [])
    else map zq_of (padrow C2 (mrow (kmask k)) []).
  Definition datasS : list (list Zq) := map dS (seq 0 (rs + (4 * rs + 1))).

  (* the data index of a row of the small matrix *)
  Definition sidx (i : nat) : nat := if Nat.ltb (i - SO) rs then (i - SO)%nat else (i - SO - 6)%nat.

  (* the coins of the extracted prover, from the coins of the opening *)
  Definition reZ (m : list F) : list Z := map (fun x => Zof (fst x)) m.
  Definition imZ (m : list F) : list Z := map (fun x => Zof (snd x)) m.

  Definition kz (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F) : coins :=
    let m1 := nth 0 mB [] in let m2 := nth 1 mB [] in let m3 := nth 0 mS [] in let m4 := nth 1 mS [] in
    mk_coins
      (map (firstn C1) [reZ m1; imZ m1; reZ m2; imZ m2; reZ qB; imZ qB])
      (map (map Zof) pB ++ map (skipn C1) [reZ m1; imZ m1; reZ m2; imZ m2; reZ qB; imZ qB])
      (ksB k)
      (map (firstn C2) [reZ m3; imZ m3; reZ m4; imZ m4; reZ qS; imZ qS])
      (map (map Zof) (firstn rs pS) ++ map (skipn C2) [reZ m3; imZ m3; reZ m4; imZ m4; reZ qS; imZ qS])
      (ksS1 k) (kmask k) (map (map Zof) (skipn rs pS)) (ksS2 k).

  Definition shapedZ (pB pS : list (list Zq)) (mB : list (list F)) (qB : list F) (mS : list (list F)) (qS : list F) : Prop :=
    length pB = (3 * rw)%nat /\ Forall (fun p => length p = nqB) pB
    /\ length pS = (rs + (4 * rs + 1))%nat /\ Forall (fun p => length p = nqS) pS
    /\ length mB = 2%nat /\ Forall (fun m => length m = kB) mB /\ length qB = kB
    /\ length mS = 2%nat /\ Forall (fun m => length m = kS) mS /\ length qS = kS.

  Lemma kz_ok : pok -> coins_ok n1 ell lo1 lo2 nB nqB nS nqS k -> forall pB pS mB qB mS qS,
    shapedZ pB pS mB qB mS qS -> coins_ok n1 ell lo1 lo2 nB nqB nS nqS (kz pB pS mB qB mS qS).
  Proof.
    intros hp hk pB pS mB qB mS qS (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    destruct hp as (hkB & hkS & _). destruct hk as (_ & _ & hsB & _ & _ & hsS1 & hm & _ & hsS2).
    rewrite Forall_forall in h2, h4, h6, h9.
    assert (hm1 : forall i, (i < 2)%nat -> length (nth i mB []) = kB) by (intros i hi; apply h6, nth_In; lia).
    assert (hm3 : forall i, (i < 2)%nat -> length (nth i mS []) = kS) by (intros i hi; apply h9, nth_In; lia).
    pose proof (hm1 0%nat ltac:(lia)) as e1. pose proof (hm1 1%nat ltac:(lia)) as e2.
    pose proof (hm3 0%nat ltac:(lia)) as e3. pose proof (hm3 1%nat ltac:(lia)) as e4.
    assert (f1 : @length (Zq * Zq) (nth 0 mB []) = kB) by exact e1.
    assert (f2 : @length (Zq * Zq) (nth 1 mB []) = kB) by exact e2.
    assert (f3 : @length (Zq * Zq) (nth 0 mS []) = kS) by exact e3.
    assert (f4 : @length (Zq * Zq) (nth 1 mS []) = kS) by exact e4.
    assert (f7 : @length (Zq * Zq) qB = kB) by exact h7.
    assert (f10 : @length (Zq * Zq) qS = kS) by exact h10.
    unfold kz, coins_ok, rows_ok, reZ, imZ. cbn [kfB kpB ksB kfS kpS1 ksS1 kmask kpS2 ksS2 map].
    assert (hfin : forall n (l : list (list Zq)) x, In x (firstn n l) -> In x l)
      by (intros n l x hx; rewrite <-(firstn_skipn n l); apply in_or_app; left; exact hx).
    assert (hsin : forall n (l : list (list Zq)) x, In x (skipn n l) -> In x l)
      by (intros n l x hx; rewrite <-(firstn_skipn n l); apply in_or_app; right; exact hx).
    destruct hsB as [hsB1 hsB2], hsS1 as [hs11 hs12], hsS2 as [hs21 hs22].
    repeat split; try assumption.
    all: first [ assumption
      | solve [rewrite ?length_firstn, ?length_skipn, length_map; lia]
      | (repeat (constructor; [rewrite ?length_firstn, ?length_skipn, length_map; lia |]); constructor)
      | (rewrite length_app, !length_map, ?length_firstn; cbn [length]; lia)
      | (rewrite !length_map, length_skipn; lia)
      | (apply Forall_app; split;
         [apply Forall_map, Forall_forall; intros p hpin; rewrite length_map; first [apply h2, hpin | apply h4, (hfin _ _ _ hpin)]
         | repeat (constructor; [rewrite length_skipn, length_map; lia |]); constructor])
      | (apply Forall_map, Forall_forall; intros p hpin; rewrite length_map; apply h4, (hsin _ _ _ hpin)) ].
    all: repeat (match goal with
                 | |- Forall _ (_ :: _) => constructor
                 | |- Forall _ [] => constructor
                 end).
    all: first [rewrite length_firstn, length_map | rewrite length_skipn, length_map];
         first [rewrite f1 | rewrite f2 | rewrite f3 | rewrite f4 | rewrite f7 | rewrite f10]; lia.
  Qed.


  Local Notation kzx := (fun pB pS mB qB mS qS => kz pB pS mB qB mS qS).

  Lemma rw_pos : (0 < rw)%nat.
  Proof. unfold rwE, MixLayout.rw. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.
  Lemma rs_pos : (0 < rs)%nat.
  Proof. unfold rsE, MixLayout.rs. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

  Lemma rowsB : pok -> wshape -> coins_ok n1 ell lo1 lo2 nB nqB nS nqS k -> forall pB pS mB qB mS qS,
    shapedZ pB pS mB qB mS qS -> forall i, (i < 3 * rw)%nat ->
    PFx (kz pB pS mB qB mS qS) T i = map emb (nth i datasB [] ++ nth i pB []).
  Proof.
    intros hp hw hk pB pS mB qB mS qS hsh i hi.
    pose proof (kz_ok hp hk pB pS mB qB mS qS hsh) as hkz. pose proof rw_pos as hrw.
    destruct hsh as (h1 & _).
    assert (hx : i = (i / rw * rw + i mod rw)%nat) by (pose proof (Nat.div_mod i rw ltac:(lia)); lia).
    assert (hq : (i / rw < 3)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (ht : (i mod rw < rw)%nat) by (apply Nat.mod_upper_bound; lia).
    rewrite hx at 1.
    rewrite (PF_W n1 ell lo1 lo2 nB nqB nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ hw hkz T _ _ hq ht).
    rewrite <-hx. cbn [kz kpB].
    rewrite app_nth1 by (rewrite length_map; lia).
    rewrite (nth_indep (map (map Zof) pB) [] (map Zof [])) by (rewrite length_map; lia). rewrite map_nth.
    rewrite rowF. unfold datasB. rewrite (nth_map_seq_any dB (3 * rw) i [] hi). reflexivity.
  Qed.

  (* the row of the small matrix that holds data row j *)
  Definition sx (j : nat) : nat := (SO + (if Nat.ltb j rs then j else j + 6))%nat.

  Lemma rowsS : pok -> wshape -> coins_ok n1 ell lo1 lo2 nB nqB nS nqS k -> forall pB pS mB qB mS qS,
    shapedZ pB pS mB qB mS qS -> forall j, (j < rs + (4 * rs + 1))%nat ->
    PFx (kz pB pS mB qB mS qS) T (sx j) = map emb (nth j datasS [] ++ nth j pS []).
  Proof.
    intros hp hw hk pB pS mB qB mS qS hsh j hj.
    pose proof (kz_ok hp hk pB pS mB qB mS qS hsh) as hkz. pose proof rs_pos as hrs.
    destruct hsh as (_ & _ & h3 & _).
    unfold datasS. rewrite (nth_map_seq_any dS _ j [] hj). unfold sx, dS.
    destruct (Nat.ltb_spec j rs) as [h | h].
    - rewrite (PF_S1 n1 ell lo1 lo2 nB nqB nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ hw hkz T j h).
      cbn [kz kpS1]. rewrite app_nth1 by (rewrite length_map, length_firstn; lia).
      rewrite (nth_indep (map (map Zof) (firstn rs pS)) [] (map Zof [])) by (rewrite length_map, length_firstn; lia).
      rewrite map_nth, nth_firstn.
      destruct (Nat.ltb_spec j rs); [| lia]. apply rowF.
    - destruct (Nat.ltb_spec j (rs + 4 * rs)) as [h' | h'].
      + set (q := ((j - rs) / rs)%nat). set (t := ((j - rs) mod rs)%nat).
        assert (hq : (q < 4)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).
        assert (ht : (t < rs)%nat) by (apply Nat.mod_upper_bound; lia).
        assert (hx : (j - rs = q * rs + t)%nat) by (pose proof (Nat.div_mod (j - rs) rs ltac:(lia)); unfold q, t; lia).
        replace (SO + (j + 6))%nat with (SO + (rs + 6) + q * rs + t)%nat by lia.
        rewrite (PF_S2 n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ hp hw hkz T q t hq ht).
        cbn [kz kpS2].
        rewrite (nth_indep (map (map Zof) (skipn rs pS)) [] (map Zof [])) by (rewrite length_map, length_skipn; lia).
        rewrite map_nth, nth_skipn.
        replace (rs + (q * rs + t))%nat with j by lia. apply rowF.
      + assert (ej : j = (rs + 4 * rs)%nat) by lia. subst j.
        replace (SO + (rs + 4 * rs + 6))%nat with (SO + (rs + 6) + 4 * rs)%nat by lia.
        rewrite (PF_M n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ hp hw hkz T).
        cbn [kz kpS2 kmask].
        rewrite (nth_indep (map (map Zof) (skipn rs pS)) [] (map Zof [])) by (rewrite length_map, length_skipn; lia).
        rewrite map_nth, nth_skipn. apply rowF.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the instance of OpenMix *)

  Hypothesis Hp : pok.
  Hypothesis Hw : wshape.
  Hypothesis Hk : coins_ok n1 ell lo1 lo2 nB nqB nS nqS k.
  Hypothesis Hs : stmt_ok n1 ell a b cin.
  Hypothesis Hu : List.length (tru T) = (2 ^ n1)%nat.
  Hypothesis Hv : List.length (trv T) = (2 ^ n1)%nat.
  Hypothesis HrA : List.length (trA T) = ell.
  Hypothesis Hry : List.length (try T) = n1.
  Hypothesis Hrz : List.length (trz T) = (n1 + ell)%nat.
  Hypothesis Hkp : List.length (tkp T) = 9%nat.

  Local Notation cc := (to_F (nth 0 (tcl T) xzero)).
  Local Notation clsFx := (map (map ExecClaims.tF) (clsP n1 ell lo1 lo2 pplain a b sig k T)).

  Definition cbF (v : nat) : list (nat * F) :=
    @cbk Fq2 fone fmul kindM (frowM ell lo2 SO) (map to_F (tkp T)) clsFx v.

  Definition rowB (pB : list (list Zq)) (i : nat) : list F := map emb (nth i datasB [] ++ nth i pB []).
  Definition rowS (pS : list (list Zq)) (i : nat) : list F := map emb (nth (sidx i) datasS [] ++ nth (sidx i) pS []).

  Lemma sidx_sx : forall j, (j < rs + (4 * rs + 1))%nat -> sidx (sx j) = j.
  Proof.
    intros j hj. unfold sidx, sx. destruct (Nat.ltb_spec j rs).
    + replace (SO + j - SO)%nat with j by lia. destruct (Nat.ltb_spec j rs); [reflexivity | lia].
    + replace (SO + (j + 6) - SO)%nat with (j + 6)%nat by lia. destruct (Nat.ltb_spec (j + 6) rs); [lia | lia].
  Qed.

  (* the rows of the slots are data rows *)
  Lemma cbF_rows : forall v iw, In iw (cbF v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < 3 * rw)%nat) /\
    ((v = 3 \/ v = 4)%nat -> exists j, (j < rs + (4 * rs + 1))%nat /\ fst iw = sx j).
  Proof.
    intros v iw h. unfold cbF in h.
    rewrite (clsF_eq n1 ell lo1 lo2 pplain a b cin sig k T Hu Hv HrA Hry Hrz Hs) in h.
    apply in_map with (f := fst) in h.
    destruct (@cbk_rows Fq2 fone fmul kindM (frowM ell lo2 SO) _ _ v (fst iw) h) as [[hk e] | (cl & t & hcl & ht & e1 & e2)].
    - split; intro hv.
      + destruct hv as [-> | ->]; cbn in hk; discriminate.
      + exists (rs + 4 * rs)%nat. split; [lia |]. rewrite e. unfold frowM, MixLayout.rM, sx.
        destruct (Nat.ltb_spec (rs + 4 * rs) rs); [pose proof rs_pos; lia |]. change (MixLayout.rs ell lo2) with rs. lia.
    - destruct (@claims9_terms Fq2 fzero fone fadd fmul fsub ftg _ n1 ell lo1 lo2 SO (dAE ell) (dBE n1) (dCE n1 ell)
                  _ _ _ _ _ _ _ ltac:(rewrite length_map; exact HrA) ltac:(rewrite length_map; exact Hry)
                  ltac:(rewrite length_map; exact Hrz) (dA_len ell) (dB_len n1) (dC_len n1 ell) cl t hcl ht)
        as [[es hr] | [[es hr] | [[es hr] | [es er]]]];
        rewrite e1 in es; subst v; split; intro hv; try (destruct hv as [hv | hv]; discriminate hv).
      all: try (exfalso; lia).
      all: first
        [ solve [destruct hr as (kk & j & hk & hj & er); rewrite <-e2, er; change (MixLayout.rw n1 ell lo1) with rw in *; nia]
        | solve [destruct hr as (j & hj & hr); change (MixLayout.rs ell lo2) with rs in *; rewrite <-e2;
                 destruct hr as [er | (a0 & ha0 & er)]; rewrite er;
                 [ exists j; split; [lia |]; unfold sx; destruct (Nat.ltb_spec j rs); lia
                 | exists (rs + a0 * rs + j)%nat; split; [nia |]; unfold sx;
                   destruct (Nat.ltb_spec (rs + a0 * rs + j) rs); lia ]]
        | solve [rewrite <-e2, er; exists (rs + 4 * rs)%nat; split; [lia |]; unfold MixLayout.rM, sx;
                 destruct (Nat.ltb_spec (rs + 4 * rs) rs); [pose proof rs_pos; lia |];
                 change (MixLayout.rs ell lo2) with rs; lia] ].
  Qed.


  Definition tfunB (pB : list (list Zq)) : list (list F) :=
    [pscale cc (msumF (rowB pB) (cbF 1)); pscale cc (msumF (rowB pB) (cbF 2))].
  Definition tfunS (pS : list (list Zq)) : list (list F) :=
    [pscale cc (msumF (rowS pS) (cbF 3)); pscale cc (msumF (rowS pS) (cbF 4))].
  Definition LsB : list (list F) :=
    [map to_F (LP n1 ell lo1 lo2 pplain a b sig k T 1); map to_F (LP n1 ell lo1 lo2 pplain a b sig k T 2)].
  Definition LsS : list (list F) :=
    [map to_F (LP n1 ell lo1 lo2 pplain a b sig k T 3); map to_F (LP n1 ell lo1 lo2 pplain a b sig k T 4)].
  Definition cvT : F := fmul cc (@LogDer.dot Fq2 fzero fadd fmul (map to_F (tkp T)) (targets n1 ell pplain a b cin cout sig wr we1 we2 k T)).

  Definition zmasks (kk : nat) : list (list F) := [repeat fzero kk; repeat fzero kk].

  Lemma shapedZ_zero : forall pB pS, length pB = (3 * rw)%nat -> Forall (fun p => length p = nqB) pB ->
    length pS = (rs + (4 * rs + 1))%nat -> Forall (fun p => length p = nqS) pS ->
    shapedZ pB pS (zmasks kB) (repeat fzero kB) (zmasks kS) (repeat fzero kS).
  Proof.
    intros pB pS h1 h2 h3 h4. unfold shapedZ, zmasks. repeat split; try assumption; try apply repeat_length.
    + repeat constructor; apply repeat_length.
    + repeat constructor; apply repeat_length.
  Qed.

  Lemma tfun_usP : forall pB pS mB qB mS qS, shapedZ pB pS mB qB mS qS -> forall v, (1 <= v <= 4)%nat ->
    msumF (if Nat.leb v 2 then rowB pB else rowS pS) (cbF v)
    = map to_F (usP n1 ell lo1 lo2 pplain a b sig (kz pB pS mB qB mS qS)
                    (btB lo1 nB omB wr we1 we2 (kz pB pS mB qB mS qS)) (btS1 lo2 nS omS sig (kz pB pS mB qB mS qS))
                    (b2x ell lo2 nS omS pplain a b cin cout sig wr we1 we2 (kz pB pS mB qB mS qS) T) T v).
  Proof.
    intros pB pS mB qB mS qS hsh v hv. unfold usP.
    rewrite (comb_msum ell lo1 lo2 nB nS omB omS pplain a b cin cout sig wr we1 we2 (kz pB pS mB qB mS qS) T).
    rewrite (to_F_cbk kindE (frowE n1 ell lo1 lo2)). fold (cbF v).
    apply msum_ext. intros iw hiw. destruct (cbF_rows v iw hiw) as [h12 h34].
    destruct (Nat.leb_spec v 2) as [hle | hgt].
    - symmetry. apply rowsB; [exact Hp | exact Hw | exact Hk | exact hsh | apply h12; lia].
    - destruct (h34 ltac:(lia)) as (j & hj & e). rewrite e. unfold rowS. rewrite sidx_sx by exact hj.
      symmetry. apply rowsS; [exact Hp | exact Hw | exact Hk | exact hsh | exact hj].
  Qed.

  Theorem Hmu_mix : forall pB pS, length pB = (3 * rw)%nat -> Forall (fun p => length p = nqB) pB ->
    length pS = (rs + (4 * rs + 1))%nat -> Forall (fun p => length p = nqS) pS ->
    fadd (@LogDer.fsum Fq2 fzero fadd (zipw (@LogDer.dot Fq2 fzero fadd fmul) (tfunB pB) LsB))
         (@LogDer.fsum Fq2 fzero fadd (zipw (@LogDer.dot Fq2 fzero fadd fmul) (tfunS pS) LsS)) = cvT.
  Proof.
    intros pB pS h1 h2 h3 h4.
    pose proof (shapedZ_zero pB pS h1 h2 h3 h4) as hsh.
    set (kk := kz pB pS (zmasks kB) (repeat fzero kB) (zmasks kS) (repeat fzero kS)).
    pose proof (kz_ok Hp Hk _ _ _ _ _ _ hsh) as hkk. fold kk in hkk.
    pose proof (batch_honest n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 kk
                  Hp Hw hkk Hs T Hu Hv HrA Hry Hrz Hkp) as hb.
    cbn [map LogDer.fsum] in hb.
    pose proof (tfun_usP _ _ _ _ _ _ hsh 1 ltac:(lia)) as u1. pose proof (tfun_usP _ _ _ _ _ _ hsh 2 ltac:(lia)) as u2.
    pose proof (tfun_usP _ _ _ _ _ _ hsh 3 ltac:(lia)) as u3. pose proof (tfun_usP _ _ _ _ _ _ hsh 4 ltac:(lia)) as u4.
    cbn [Nat.leb] in u1, u2, u3, u4. fold kk in u1, u2, u3, u4.
    unfold tfunB, tfunS, LsB, LsS, cvT. cbn [zipw LogDer.fsum].
    rewrite !(@dot_pscale_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite u1, u2, u3, u4.
    change (targets n1 ell pplain a b cin cout sig wr we1 we2 k T) with (targets n1 ell pplain a b cin cout sig wr we1 we2 kk T).
    change (LP n1 ell lo1 lo2 pplain a b sig k T) with (LP n1 ell lo1 lo2 pplain a b sig kk T).
    rewrite <-hb. field.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the shifts at the opened columns, from the opened entries *)

  Local Notation omBK := (zq_of omB).
  Local Notation omSK := (zq_of omS).
  Local Notation JBn := (map Z.to_nat (tJB T)).
  Local Notation JSn := (map Z.to_nat (tJS T)).
  Local Notation encB := (@encJ Fq2 fzero fone fadd fmul (emb omBK) JBn).
  Local Notation encS := (@encJ Fq2 fzero fone fadd fmul (emb omSK) JSn).
  Local Notation openedK := (@opened Zq qzero qone qadd qmul).

  Definition shJB (ys : list (list Zq)) : list (list F) :=
    [map (fmul cc) (msumJ JBn (fun i => map emb (nth i ys [])) (cbF 1));
     map (fmul cc) (msumJ JBn (fun i => map emb (nth i ys [])) (cbF 2))].
  Definition shJS (ys : list (list Zq)) : list (list F) :=
    [map (fmul cc) (msumJ JSn (fun i => map emb (nth (sidx i) ys [])) (cbF 3));
     map (fmul cc) (msumJ JSn (fun i => map emb (nth (sidx i) ys [])) (cbF 4))].

  Theorem HshB_mix : forall pB, length pB = length datasB ->
    map encB (tfunB pB) = shJB (zipw (fun d p => openedK omBK d p JBn) datasB pB).
  Proof.
    intros pB hl. unfold tfunB, shJB. cbn [map]. rewrite !enc_pscale, !enc_msum.
    assert (e : forall v, (v = 1 \/ v = 2)%nat -> msumJ JBn (fun i => encB (rowB pB i)) (cbF v)
                  = msumJ JBn (fun i => map emb (nth i (zipw (fun d p => openedK omBK d p JBn) datasB pB) [])) (cbF v)).
    { intros v hv. apply msumJ_ext. intros iw hiw. destruct (cbF_rows v iw hiw) as [h _].
      unfold rowB. rewrite enc_emb. f_equal. symmetry.
      refine (nth_zipw (fun d p => openedK omBK d p JBn) datasB pB _ [] [] [] _ _);
        [unfold datasB; rewrite length_map, length_seq; apply h; exact hv | symmetry; exact hl]. }
    rewrite (e 1%nat), (e 2%nat) by tauto. reflexivity.
  Qed.

  Theorem HshS_mix : forall pS, length pS = length datasS ->
    map encS (tfunS pS) = shJS (zipw (fun d p => openedK omSK d p JSn) datasS pS).
  Proof.
    intros pS hl. unfold tfunS, shJS. cbn [map]. rewrite !enc_pscale, !enc_msum.
    assert (e : forall v, (v = 3 \/ v = 4)%nat -> msumJ JSn (fun i => encS (rowS pS i)) (cbF v)
                  = msumJ JSn (fun i => map emb (nth (sidx i) (zipw (fun d p => openedK omSK d p JSn) datasS pS) [])) (cbF v)).
    { intros v hv. apply msumJ_ext. intros iw hiw. destruct (cbF_rows v iw hiw) as [_ h].
      destruct (h hv) as (j & hj & ej). rewrite ej, sidx_sx by exact hj.
      unfold rowS. rewrite sidx_sx by exact hj. rewrite enc_emb. f_equal. symmetry.
      refine (nth_zipw (fun d p => openedK omSK d p JSn) datasS pS _ [] [] [] _ _);
        [unfold datasS; rewrite length_map, length_seq; exact hj | symmetry; exact hl]. }
    rewrite (e 3%nat), (e 4%nat) by tauto. reflexivity.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the proximity vectors *)

  Definition cbPB : list (nat * F) := combine (seq 0 (3 * rw)) (map to_F (firstn (3 * rw) (tgB T))).
  Definition cbPS : list (nat * F) :=
    combine (map sx (seq 0 rs)) (map to_F (firstn rs (tgS T)))
    ++ combine (map sx (seq rs (4 * rs + 1))) (map to_F (skipn (rs + 6) (tgS T))).

  Definition tpB (pB : list (list Zq)) : list F := msumF (rowB pB) cbPB.
  Definition tpS (pS : list (list Zq)) : list F := msumF (rowS pS) cbPS.
  Definition shpB (ys : list (list Zq)) : list F := msumJ JBn (fun i => map emb (nth i ys [])) cbPB.
  Definition shpS (ys : list (list Zq)) : list F := msumJ JSn (fun i => map emb (nth (sidx i) ys [])) cbPS.

  Lemma cbPB_rows : forall iw, In iw cbPB -> (fst iw < 3 * rw)%nat.
  Proof. intros [i w] h. apply in_combine_l in h. apply in_seq in h. cbn. lia. Qed.

  Lemma cbPS_rows : forall iw, In iw cbPS -> exists j, (j < rs + (4 * rs + 1))%nat /\ fst iw = sx j.
  Proof.
    intros [i w] h. apply in_app_or in h. destruct h as [h | h]; apply in_combine_l in h; apply in_map_iff in h;
      destruct h as (j & <- & hj); apply in_seq in hj; exists j; split; try reflexivity; lia.
  Qed.

  Theorem HspB_mix : forall pB, length pB = length datasB ->
    encB (tpB pB) = shpB (zipw (fun d p => openedK omBK d p JBn) datasB pB).
  Proof.
    intros pB hl. unfold tpB, shpB. rewrite enc_msum. apply msumJ_ext. intros iw hiw.
    pose proof (cbPB_rows iw hiw) as h. unfold rowB. rewrite enc_emb. f_equal. symmetry.
    refine (nth_zipw (fun d p => openedK omBK d p JBn) datasB pB _ [] [] [] _ _);
      [unfold datasB; rewrite length_map, length_seq; exact h | symmetry; exact hl].
  Qed.

  Theorem HspS_mix : forall pS, length pS = length datasS ->
    encS (tpS pS) = shpS (zipw (fun d p => openedK omSK d p JSn) datasS pS).
  Proof.
    intros pS hl. unfold tpS, shpS. rewrite enc_msum. apply msumJ_ext. intros iw hiw.
    destruct (cbPS_rows iw hiw) as (j & hj & ej). rewrite ej, sidx_sx by exact hj.
    unfold rowS. rewrite sidx_sx by exact hj. rewrite enc_emb. f_equal. symmetry.
    refine (nth_zipw (fun d p => openedK omSK d p JSn) datasS pS _ [] [] [] _ _);
      [unfold datasS; rewrite length_map, length_seq; exact hj | symmetry; exact hl].
  Qed.

  (* the rows holding the slot masks enter the proximity vector through their two coordinates *)
  Definition gBi (i : nat) : F := to_F (nth (3 * rw + i) (tgB T) xzero).
  Definition gSi (i : nat) : F := to_F (nth (rs + i) (tgS T) xzero).

  Definition Gm (g : nat -> F) (m1 m2 : list F) : list F :=
    padd (padd (pscale (g 0%nat) (map re m1)) (pscale (g 1%nat) (map im m1)))
         (padd (pscale (g 2%nat) (map re m2)) (pscale (g 3%nat) (map im m2))).
  Definition Ghm (g : nat -> F) (e1 e2 : list F) : list F :=
    vadd (vadd (map (fmul (g 0%nat)) (map re e1)) (map (fmul (g 1%nat)) (map im e1)))
         (vadd (map (fmul (g 2%nat)) (map re e2)) (map (fmul (g 3%nat)) (map im e2))).

  Definition GB (ms : list (list F)) : list F := Gm gBi (nth 0 ms []) (nth 1 ms []).
  Definition GS (ms : list (list F)) : list F := Gm gSi (nth 0 ms []) (nth 1 ms []).
  Definition GhB (es : list (list F)) : list F :=
    Ghm gBi (nth 0 es (map (fun _ => fzero) JBn)) (nth 1 es (map (fun _ => fzero) JBn)).
  Definition GhS (es : list (list F)) : list F :=
    Ghm gSi (nth 0 es (map (fun _ => fzero) JSn)) (nth 1 es (map (fun _ => fzero) JSn)).

  Lemma enc_Gm : forall om J g m1 m2,
    @encJ Fq2 fzero fone fadd fmul (emb om) J (Gm g m1 m2)
    = Ghm g (@encJ Fq2 fzero fone fadd fmul (emb om) J m1) (@encJ Fq2 fzero fone fadd fmul (emb om) J m2).
  Proof.
    intros om J g m1 m2. unfold Gm, Ghm.
    rewrite !(@encJ_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), !enc_pscale, !enc_re, !enc_im.
    reflexivity.
  Qed.

  Theorem HGB_mix : forall ms, encB (GB ms) = GhB (map encB ms).
  Proof.
    intro ms. unfold GB, GhB. rewrite enc_Gm. f_equal; symmetry;
      exact (map_nth (fun m => encB m) ms [] _).
  Qed.

  Theorem HGS_mix : forall ms, encS (GS ms) = GhS (map encS ms).
  Proof.
    intro ms. unfold GS, GhS. rewrite enc_Gm. f_equal; symmetry;
      exact (map_nth (fun m => encS m) ms [] _).
  Qed.


  (* ------------------------------------------------------------------ *)
  (* lengths of the data rows *)

  Definition pB0 : list (list Zq) := repeat (repeat qzero nqB) (3 * rw).
  Definition pS0 : list (list Zq) := repeat (repeat qzero nqS) (rs + (4 * rs + 1)).

  Lemma sh0 : shapedZ pB0 pS0 (zmasks kB) (repeat fzero kB) (zmasks kS) (repeat fzero kS).
  Proof.
    apply shapedZ_zero; unfold pB0, pS0; try apply repeat_length;
      apply Forall_forall; intros p hp; apply repeat_spec in hp; subst p; apply repeat_length.
  Qed.

  Lemma dB_len : forall i, (i < 3 * rw)%nat -> length (nth i datasB []) = C1.
  Proof.
    intros i hi. pose proof (rowsB Hp Hw Hk _ _ _ _ _ _ sh0 i hi) as e.
    apply (f_equal (@length F)) in e.
    pose proof (kz_ok Hp Hk _ _ _ _ _ _ sh0) as hkz.
    unfold PF in e. rewrite AM_eq in e. rewrite !length_map, length_app in e.
    rewrite (nth_rep _ _ _ _ hi : nth i pB0 [] = _) in e. rewrite repeat_length in e.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 _ Hw hkz) as [hl hf].
    rewrite app_nth1 in e by (rewrite hl; lia).
    rewrite Forall_forall in hf. rewrite (hf (nth i _ [])) in e by (apply nth_In; rewrite hl; lia). lia.
  Qed.

  Lemma dS_len : forall j, (j < rs + (4 * rs + 1))%nat -> length (nth j datasS []) = C2.
  Proof.
    intros j hj. pose proof (rowsS Hp Hw Hk _ _ _ _ _ _ sh0 j hj) as e.
    apply (f_equal (@length F)) in e.
    pose proof (kz_ok Hp Hk _ _ _ _ _ _ sh0) as hkz.
    unfold PF in e. rewrite AM_eq in e. rewrite !length_map, length_app in e.
    rewrite (nth_rep _ _ _ _ hj : nth j pS0 [] = _) in e. rewrite repeat_length in e.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 _ Hw hkz) as [hl _].
    destruct (msgsS1_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 _ Hw hkz) as [hl1 hf1].
    rewrite app_nth2 in e by (rewrite hl; unfold sx, SOE; lia).
    match type of e with context [nth _ (_ ++ msgsS2 _ _ _ _ _ _ _ _ _ _ _ _ ?ru ?rv ?al ?be) _] =>
      destruct (msgsS2_shape n1 ell lo1 lo2 kB nB nqB kS nS nqS pplain a b cin cout sig wr we1 we2 _ ru rv al be Hp Hw hkz)
        as [hl2 hf2] end.
    assert (hf := proj2 (Forall_app _ _ _) (conj hf1 hf2)).
    rewrite Forall_forall in hf. rewrite hl in e.
    rewrite (hf (nth (sx j - _) _ [])) in e by (apply nth_In; rewrite length_app, hl1, hl2; unfold sx, SOE; destruct (Nat.ltb_spec j rs); lia). lia.
  Qed.


  (* ------------------------------------------------------------------ *)
  (* the instance *)

  (* the public parameters: omB and omS have order at least nB and nS; the opened columns are
     distinct, in range, and as many as the pads (fp_core draws them without repetition) *)
  Hypothesis HnB : forall i j, (i < nB)%nat -> (j < nB)%nat -> pwK omBK i = pwK omBK j -> i = j.
  Hypothesis HnS : forall i j, (i < nS)%nat -> (j < nS)%nat -> pwK omSK i = pwK omSK j -> i = j.
  Hypothesis HomB0 : omBK <> qzero.
  Hypothesis HomS0 : omSK <> qzero.
  Hypothesis HJBnd : NoDup JBn.
  Hypothesis HJSnd : NoDup JSn.
  Hypothesis HJBlt : forall j, In j JBn -> (j < nB)%nat.
  Hypothesis HJSlt : forall j, In j JSn -> (j < nS)%nat.
  Hypothesis HJBlen : length JBn = nqB.
  Hypothesis HJSlen : length JSn = nqS.

  Local Notation shapedPB := (@shapedP Zq datasB JBn).
  Local Notation shapedPS := (@shapedP Zq datasS JSn).

  Lemma pad_len : forall (datas p : list (list Zq)) J i, @shapedP Zq datas J p -> (i < length datas)%nat ->
    length (nth i p []) = length J.
  Proof.
    intros datas p J i [hl hs] hi. unfold ZkOpen.lens in hs. rewrite Forall_forall in hs.
    apply hs, nth_In. lia.
  Qed.

  Lemma kB_eq : kB = (C1 + nqB)%nat.
  Proof. exact (proj1 Hp). Qed.
  Lemma kS_eq : kS = (C2 + nqS)%nat.
  Proof. exact (proj1 (proj2 Hp)). Qed.

  Lemma rowB_len : forall p i, shapedPB p -> (i < 3 * rw)%nat -> (length (rowB p i) <= kB)%nat.
  Proof.
    intros p i hp hi. unfold rowB. rewrite length_map, length_app, dB_len by exact hi.
    rewrite (pad_len datasB p JBn i hp) by (unfold datasB; rewrite length_map, length_seq; exact hi).
    rewrite HJBlen, kB_eq. lia.
  Qed.

  Lemma rowS_len : forall p j, shapedPS p -> (j < rs + (4 * rs + 1))%nat -> (length (rowS p (sx j)) <= kS)%nat.
  Proof.
    intros p j hp hj. unfold rowS. rewrite sidx_sx by exact hj. rewrite length_map, length_app, dS_len by exact hj.
    rewrite (pad_len datasS p JSn j hp) by (unfold datasS; rewrite length_map, length_seq; exact hj).
    rewrite HJSlen, kS_eq. lia.
  Qed.

  Lemma HtkB_mix : forall p, shapedPB p -> Forall (fun t => (length t <= kB)%nat) (tfunB p).
  Proof.
    intros p hp. unfold tfunB.
    repeat constructor; rewrite (@length_pscale Fq2 fmul); apply msum_length; intros iw hiw;
      apply rowB_len; [exact hp | | exact hp |]; apply (proj1 (cbF_rows _ iw hiw)); tauto.
  Qed.

  Lemma HtkS_mix : forall p, shapedPS p -> Forall (fun t => (length t <= kS)%nat) (tfunS p).
  Proof.
    intros p hp. unfold tfunS.
    repeat constructor; rewrite (@length_pscale Fq2 fmul); apply msum_length; intros iw hiw;
      destruct (proj2 (cbF_rows _ iw hiw) ltac:(tauto)) as (j & hj & e); rewrite e; apply rowS_len; assumption.
  Qed.

  Lemma HtpB_mix : forall p, shapedPB p -> (length (tpB p) <= kB)%nat.
  Proof. intros p hp. apply msum_length. intros iw hiw. apply rowB_len; [exact hp | exact (cbPB_rows iw hiw)]. Qed.

  Lemma HtpS_mix : forall p, shapedPS p -> (length (tpS p) <= kS)%nat.
  Proof.
    intros p hp. apply msum_length. intros iw hiw. destruct (cbPS_rows iw hiw) as (j & hj & e). rewrite e.
    apply rowS_len; assumption.
  Qed.

  Lemma Gm_len : forall g m1 m2 kk, length m1 = kk -> length m2 = kk -> (length (Gm g m1 m2) <= kk)%nat.
  Proof.
    intros g m1 m2 kk h1 h2. unfold Gm.
    rewrite !(@length_padd Fq2 fadd), !(@length_pscale Fq2 fmul), !length_map. lia.
  Qed.

  Lemma shapedM_nth : forall kk ms i, @shapedM Fq2 kk 2 ms -> (i < 2)%nat -> length (nth i ms []) = kk.
  Proof.
    intros kk ms i [hl hs] hi. unfold ZkOpen.lens in hs. rewrite Forall_forall in hs. apply hs, nth_In. lia.
  Qed.

  Lemma HGlB_mix : forall ms, @shapedM Fq2 kB 2 ms -> (length (GB ms) <= kB)%nat.
  Proof. intros ms h. apply Gm_len; apply (shapedM_nth kB ms); [exact h | lia | exact h | lia]. Qed.
  Lemma HGlS_mix : forall ms, @shapedM Fq2 kS 2 ms -> (length (GS ms) <= kS)%nat.
  Proof. intros ms h. apply Gm_len; apply (shapedM_nth kS ms); [exact h | lia | exact h | lia]. Qed.

  Lemma pads_Forall : forall (datas p : list (list Zq)) J, @shapedP Zq datas J p -> Forall (fun x => length x = length J) p.
  Proof. intros datas p J [_ h]. exact h. Qed.

  (* the honest opening and its simulator *)
  Definition honMix := @honO3 Zq qzero qone qadd qmul Fq2 fzero fone fadd fmul emb omBK omSK JBn JSn
                         datasB datasS tfunB tfunS tpB tpS GB GS LsB LsS.
  Definition simMix := @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omBK omSK JBn JSn LsB LsS cvT
                         shJB shJS shpB shpS GhB GhS.
  Definition coinsMix := @O3L Zq Fq2 lq lf2 JBn JSn datasB datasS kB 2 kB kS 2 kS.

  (* Theorem 5.3, steps (4) to (6): over all coins of the opening (pads, slot masks, proximity masks),
     the honest transcripts are a permutation of the simulated ones *)
  Theorem mix_open_zk : Permutation (map honMix coinsMix) (map simMix coinsMix).
  Proof.
    unfold honMix, simMix, coinsMix.
    refine (@open3_zk Zq qzero qone qadd qmul qsub qdiv qopp qinv Zq_dec Zq_field
              Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field
              emb lq lq_NoDup lq_all lf2 lf2_NoDup lf2_all omBK omSK nB nS HnB HnS HomB0 HomS0
              JBn JSn HJBnd HJSnd HJBlt HJSlt datasB datasS kB 2 kB kS 2 kS
              tfunB tfunS tpB tpS GB GS
              (fun _ => eq_refl) (fun _ => eq_refl) HtkB_mix HtkS_mix HtpB_mix HtpS_mix HGlB_mix HGlS_mix
              LsB LsS cvT shJB shJS shpB shpS GhB GhS _ _ _ _ _ (fun ms _ => HGB_mix ms) (fun ms _ => HGS_mix ms)).
    - intros pB pS hB hS. apply Hmu_mix.
      + destruct hB as [h _]. rewrite h. unfold datasB. rewrite length_map, length_seq. reflexivity.
      + rewrite <-HJBlen. exact (pads_Forall _ _ _ hB).
      + destruct hS as [h _]. rewrite h. unfold datasS. rewrite length_map, length_seq. reflexivity.
      + rewrite <-HJSlen. exact (pads_Forall _ _ _ hS).
    - intros pB [h _]. exact (HshB_mix pB h).
    - intros pS [h _]. exact (HshS_mix pS h).
    - intros pB [h _]. exact (HspB_mix pB h).
    - intros pS [h _]. exact (HspS_mix pS h).
  Qed.


  Definition oviewMix := @oview3 Zq qzero qone qadd qmul Fq2 fadd omBK omSK JBn JSn datasB datasS tfunB tfunS tpB tpS GB GS.

  (* the pieces of mix_open_zk, for the composition with the layer; cv is any value equal to cvT *)
  Theorem mix_open_parts : forall cv, cv = cvT ->
    NoDup coinsMix
    /\ (forall x, In x coinsMix -> In (oviewMix x) coinsMix)
    /\ (forall x x', In x coinsMix -> In x' coinsMix -> oviewMix x = oviewMix x' -> x = x')
    /\ (forall v, In v coinsMix -> exists x, In x coinsMix /\ oviewMix x = v)
    /\ (forall x, In x coinsMix ->
          honMix x = @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omBK omSK JBn JSn LsB LsS cv
                       shJB shJS shpB shpS GhB GhS (oviewMix x)).
  Proof.
    intros cv ->. unfold honMix, coinsMix, oviewMix.
    refine (@open3_parts Zq qzero qone qadd qmul qsub qdiv qopp qinv Zq_dec Zq_field
              Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field
              emb lq lq_NoDup lq_all lf2 lf2_NoDup lf2_all omBK omSK nB nS HnB HnS HomB0 HomS0
              JBn JSn HJBnd HJSnd HJBlt HJSlt datasB datasS kB 2 kB kS 2 kS
              tfunB tfunS tpB tpS GB GS
              (fun _ => eq_refl) (fun _ => eq_refl) HtkB_mix HtkS_mix HtpB_mix HtpS_mix HGlB_mix HGlS_mix
              LsB LsS cvT shJB shJS shpB shpS GhB GhS _ _ _ _ _ (fun ms _ => HGB_mix ms) (fun ms _ => HGS_mix ms)).
    - intros pB pS hB hS. apply Hmu_mix.
      + destruct hB as [h _]. rewrite h. unfold datasB. rewrite length_map, length_seq. reflexivity.
      + rewrite <-HJBlen. exact (pads_Forall _ _ _ hB).
      + destruct hS as [h _]. rewrite h. unfold datasS. rewrite length_map, length_seq. reflexivity.
      + rewrite <-HJSlen. exact (pads_Forall _ _ _ hS).
    - intros pB [h _]. exact (HshB_mix pB h).
    - intros pS [h _]. exact (HshS_mix pS h).
    - intros pB [h _]. exact (HspB_mix pB h).
    - intros pS [h _]. exact (HspS_mix pS h).
  Qed.

End MixOpen.
