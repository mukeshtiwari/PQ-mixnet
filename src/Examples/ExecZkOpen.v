(* The extracted prover against the model (zero knowledge for the running
   code, step 4): the opening of a prover run.

   With the prover's coins kz pB pS mB qB mS qS (ZkOpenMix.v: the pads pB,
   pS, the slot masks mB, mS and the proximity masks qB, qS of the model),
   the rows of the committed matrices that hold the masks are the masks:

     PF_mB, PF_mS     the rows 3 rw + j and SO + rs + j (j < 6) are the real
                      and imaginary parts of m1, m2, qB (resp. m3, m4, qS);
     msP_mask         the mask part msP v of slot vector v is m_v;

   and hence the slot vectors, the proximity vectors and mu of parts_of are
   those of the model's honest opening honMix. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Utility Require Import Zpstar.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks ZkSumcheck ZkOpen ZkTranscript ZkOpenTranscript ZkJoin SlotKinds Opening MixLayout OpenClaims.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecVerify ExecProveBase ExecFold ExecProve ExecRows ExecNtt ExecBack ExecBackD ExecBackO ZkOpenMix.
Import ListNotations.

Add Field fieldF2o : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Add Field fieldZqo : (@field_theory_for_stdlib_tactic Zq eq qzero qone qopp qadd qmul qsub qinv qdiv Zq_field).

Local Notation F := Fq2.
Local Notation padd := (@LogDer.padd Fq2 fadd).
Local Notation pscale := (@LogDer.pscale Fq2 fmul).
Local Notation msumF := (@msum Fq2 fadd fmul).

Lemma padd_nil : forall p, padd p [] = p.
Proof. intros [| x p]; reflexivity. Qed.

Lemma padd_assoc : forall p q r, padd (padd p q) r = padd p (padd q r).
Proof.
  induction p as [| x p ih]; intros q r; [reflexivity |].
  destruct q as [| y q]; [reflexivity |]. destruct r as [| z r]; [reflexivity |].
  cbn [LogDer.padd]. rewrite ih. f_equal. ring.
Qed.

Lemma padd_comm : forall p q, padd p q = padd q p.
Proof.
  induction p as [| x p ih]; intros q; destruct q as [| y q]; try reflexivity.
  cbn [LogDer.padd]. rewrite ih. f_equal. ring.
Qed.

Lemma msum_app : forall P l1 l2, msumF P (l1 ++ l2) = padd (msumF P l1) (msumF P l2).
Proof.
  intros P l1 l2. induction l1 as [| iw l1 ih]; [reflexivity |].
  cbn [app Opening.msum]. rewrite ih, padd_assoc. reflexivity.
Qed.

Lemma map_pairF_combine : forall (l : list nat) (t : list xf), map pairF (combine l t) = combine l (map to_F t).
Proof.
  induction l as [| i l ih]; intros t; [reflexivity |]. destruct t as [| x t]; [reflexivity |].
  cbn [combine map pairF fst snd]. rewrite ih. reflexivity.
Qed.

Lemma combine_split : forall {A B : Type} (l1 l2 : list A) (t : list B), List.length t = (List.length l1 + List.length l2)%nat ->
  combine (l1 ++ l2) t = combine l1 (firstn (List.length l1) t) ++ combine l2 (skipn (List.length l1) t).
Proof.
  intros A B l1; induction l1 as [| x l1 ih]; intros l2 t ht; [reflexivity |].
  destruct t as [| y t]; [cbn in ht; lia |]. cbn [app combine List.length firstn skipn].
  rewrite ih by (cbn in ht; lia). reflexivity.
Qed.

Lemma skipn_firstn4 : forall {A : Type} n (l : list A) d, (n + 4 <= List.length l)%nat ->
  skipn n (firstn (n + 4) l) = [nth n l d; nth (n + 1) l d; nth (n + 2) l d; nth (n + 3) l d].
Proof.
  intros A n; induction n as [| n ih]; intros l d hl.
  - destruct l as [| x0 [| x1 [| x2 [| x3 l]]]]; cbn in hl; try lia. reflexivity.
  - destruct l as [| x l]; [cbn in hl; lia |]. cbn [Nat.add firstn skipn nth]. apply ih. cbn in hl. lia.
Qed.

(* an element of GF(q^2) from its two coordinates *)
Lemma re_im : forall x, fadd (fmul fone (re x)) (fmul ftg (im x)) = x.
Proof.
  intros [x1 x2]. unfold re, im, fadd, fmul, fone, ftg, eadd, emul, eone, egen. cbn [fst snd]. f_equal; ring.
Qed.

Lemma re_im_list : forall m, padd (pscale fone (map re m)) (pscale ftg (map im m)) = m.
Proof.
  induction m as [| x m ih]; [reflexivity |]. cbn [map]. unfold LogDer.pscale in *. cbn [map LogDer.padd].
  rewrite re_im, ih. reflexivity.
Qed.

Lemma reZ_F : forall m, map to_F (map bx (reZ m)) = map re m.
Proof. intro m. unfold reZ. rewrite !map_map. apply map_ext. intro x. rewrite emb_bx_Zof. reflexivity. Qed.

Lemma imZ_F : forall m, map to_F (map bx (imZ m)) = map im m.
Proof. intro m. unfold imZ. rewrite !map_map. apply map_ext. intro x. rewrite emb_bx_Zof. reflexivity. Qed.

Lemma padrow_full : forall C (L : list Z), (C <= List.length L)%nat ->
  map to_F (map bx (padrow C (firstn C L) (skipn C L))) = map to_F (map bx L).
Proof.
  intros C L hl. unfold padrow. rewrite length_firstn.
  replace (C - Nat.min C (List.length L))%nat with 0%nat by lia. cbn [repeat app].
  rewrite <-(firstn_skipn C L) at 3. rewrite !map_app, !map_map. f_equal.
  apply map_ext. intro z. apply to_F_bx_zm.
Qed.

Section Open.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable k : coins.
  Variable T : ptrace.

  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation SO := (SOE n1 ell lo1).
  Local Notation wshape := (witness_shape n1 ell cout sig wr we1 we2).
  Local Notation pok := (params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS).
  Local Notation cok := (fun kk => coins_ok n1 ell lo1 lo2 nB nqB nS nqS kk).
  Local Notation PFx := (fun kk => PF ell lo1 lo2 nB nS omB omS pplain a b cin cout sig wr we1 we2 kk T).
  Local Notation kzx := (kz ell lo1 lo2 k).
  Local Notation shZ := (shapedZ n1 ell lo1 lo2 kB nqB kS nqS).

  Hypothesis Hp : pok.
  Hypothesis Hw : wshape.
  Hypothesis Hk : cok k.
  Hypothesis Hs : stmt_ok n1 ell a b cin.
  Hypothesis Hu : List.length (tru T) = (2 ^ n1)%nat.
  Hypothesis Hv : List.length (trv T) = (2 ^ n1)%nat.
  Hypothesis HrA : List.length (trA T) = ell.
  Hypothesis Hry : List.length (try T) = n1.
  Hypothesis Hrz : List.length (trz T) = (n1 + ell)%nat.
  Hypothesis Hkp : List.length (tkp T) = 9%nat.

  Definition LB (mB : list (list F)) (qB : list F) : list (list Z) :=
    [reZ (nth 0 mB []); imZ (nth 0 mB []); reZ (nth 1 mB []); imZ (nth 1 mB []); reZ qB; imZ qB].
  Definition LS (mS : list (list F)) (qS : list F) : list (list Z) :=
    [reZ (nth 0 mS []); imZ (nth 0 mS []); reZ (nth 1 mS []); imZ (nth 1 mS []); reZ qS; imZ qS].

  Lemma PF_mB : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall j, (j < 6)%nat ->
    PFx (kzx pB pS mB qB mS qS) (3 * rw + j) = map to_F (map bx (nth j (LB mB qB) [])).
  Proof.
    intros pB pS mB qB mS qS hsh j hj.
    pose proof (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS k Hp Hk pB pS mB qB mS qS hsh) as hkz.
    pose proof hsh as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    pose proof (kB_eq n1 ell lo1 lo2 kB nB nqB kS nS nqS Hp) as hkB.
    cbv beta. unfold PF. rewrite AM_eq.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 _ Hw hkz) as [hlB _].
    rewrite app_nth1 by (rewrite hlB; lia).
    pose proof (Wk_rows n1 ell lo1 cout sig wr we1 we2 Hw 0%nat ltac:(lia)) as [_ r0].
    pose proof (Wk_rows n1 ell lo1 cout sig wr we1 we2 Hw 1%nat ltac:(lia)) as [_ r1].
    pose proof (Wk_rows n1 ell lo1 cout sig wr we1 we2 Hw 2%nat ltac:(lia)) as [_ r2].
    assert (hW : List.length (flat_map (split_rows C1) (Wk wr we1 we2)) = (3 * rw)%nat).
    { unfold Wk, Wpol in *. cbn [map flat_map] in *. rewrite ?app_nil_r, !length_app. cbn [nth] in r0, r1, r2. lia. }
    assert (hmB : forall i, (i < 2)%nat -> List.length (nth i mB []) = kB)
      by (intros i hi; rewrite Forall_forall in h6; apply h6, nth_In; lia).
    unfold msgsB. rewrite nth_msgs.
    2: { cbn [kz kfB kpB]. rewrite !length_app, hW, !length_map, h1. cbn. lia. }
    2: { cbn [kz kfB]. rewrite length_app, hW, length_map. cbn. lia. }
    cbn [kz kfB kpB].
    rewrite app_nth2 by (rewrite hW; lia). rewrite hW. replace (3 * rw + j - 3 * rw)%nat with j by lia.
    rewrite app_nth2 by (rewrite length_map, h1; lia). rewrite length_map, h1.
    replace (3 * rw + j - 3 * rw)%nat with j by lia.
    change (map (firstn C1) [reZ (nth 0 mB []); imZ (nth 0 mB []); reZ (nth 1 mB []); imZ (nth 1 mB []); reZ qB; imZ qB])
      with (map (firstn C1) (LB mB qB)).
    change (map (skipn C1) [reZ (nth 0 mB []); imZ (nth 0 mB []); reZ (nth 1 mB []); imZ (nth 1 mB []); reZ qB; imZ qB])
      with (map (skipn C1) (LB mB qB)).
    rewrite (nth_indep (map (firstn C1) (LB mB qB)) [] (firstn C1 [])) by (rewrite length_map; cbn; lia).
    rewrite (nth_indep (map (skipn C1) (LB mB qB)) [] (skipn C1 [])) by (rewrite length_map; cbn; lia).
    rewrite !map_nth. apply padrow_full.
    unfold LB, reZ, imZ.
    pose proof (hmB 0%nat ltac:(lia)) as e0. pose proof (hmB 1%nat ltac:(lia)) as e1.
    assert (f0 : @List.length (Zq * Zq) (nth 0 mB []) = kB) by exact e0.
    assert (f1 : @List.length (Zq * Zq) (nth 1 mB []) = kB) by exact e1.
    assert (f7 : @List.length (Zq * Zq) qB = kB) by exact h7.
    destruct j as [| [| [| [| [| [| j]]]]]]; try lia; cbn [nth]; rewrite length_map; lia.
  Qed.

  Lemma PF_mS : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall j, (j < 6)%nat ->
    PFx (kzx pB pS mB qB mS qS) (SO + rs + j) = map to_F (map bx (nth j (LS mS qS) [])).
  Proof.
    intros pB pS mB qB mS qS hsh j hj.
    pose proof (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS k Hp Hk pB pS mB qB mS qS hsh) as hkz.
    pose proof hsh as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    pose proof (kS_eq n1 ell lo1 lo2 kB nB nqB kS nS nqS Hp) as hkS.
    cbv beta. unfold PF. rewrite AM_eq.
    destruct (msgsB_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 _ Hw hkz) as [hlB _].
    destruct (msgsS1_shape n1 ell lo1 lo2 nB nqB nS nqS cout sig wr we1 we2 _ Hw hkz) as [hl1 _].
    rewrite app_nth2 by (rewrite hlB; unfold SOE; lia). rewrite hlB.
    replace (SO + rs + j - (3 * rw + 6))%nat with (rs + j)%nat by (unfold SOE; lia).
    rewrite app_nth1 by (rewrite hl1; lia).
    destruct (sigZ_rows n1 ell lo2 cout sig wr we1 we2 Hw) as [_ hr].
    assert (hmS : forall i, (i < 2)%nat -> List.length (nth i mS []) = kS)
      by (intros i hi; rewrite Forall_forall in h9; apply h9, nth_In; lia).
    unfold msgsS1. rewrite nth_msgs.
    2: { cbn [kz kfS kpS1]. rewrite !length_app, hr, !length_map, length_firstn, h3. cbn. lia. }
    2: { cbn [kz kfS]. rewrite length_app, hr, length_map. cbn. lia. }
    cbn [kz kfS kpS1].
    rewrite app_nth2 by (rewrite hr; lia). rewrite hr. replace (rs + j - rs)%nat with j by lia.
    rewrite app_nth2 by (rewrite length_map, length_firstn, h3; lia). rewrite length_map, length_firstn, h3.
    replace (rs + j - Nat.min rs (rs + (4 * rs + 1)))%nat with j by lia.
    change (map (firstn C2) [reZ (nth 0 mS []); imZ (nth 0 mS []); reZ (nth 1 mS []); imZ (nth 1 mS []); reZ qS; imZ qS])
      with (map (firstn C2) (LS mS qS)).
    change (map (skipn C2) [reZ (nth 0 mS []); imZ (nth 0 mS []); reZ (nth 1 mS []); imZ (nth 1 mS []); reZ qS; imZ qS])
      with (map (skipn C2) (LS mS qS)).
    rewrite (nth_indep (map (firstn C2) (LS mS qS)) [] (firstn C2 [])) by (rewrite length_map; cbn; lia).
    rewrite (nth_indep (map (skipn C2) (LS mS qS)) [] (skipn C2 [])) by (rewrite length_map; cbn; lia).
    rewrite !map_nth. apply padrow_full.
    unfold LS, reZ, imZ.
    pose proof (hmS 0%nat ltac:(lia)) as e0. pose proof (hmS 1%nat ltac:(lia)) as e1.
    assert (f0 : @List.length (Zq * Zq) (nth 0 mS []) = kS) by exact e0.
    assert (f1 : @List.length (Zq * Zq) (nth 1 mS []) = kS) by exact e1.
    assert (f10 : @List.length (Zq * Zq) qS = kS) by exact h10.
    destruct j as [| [| [| [| [| [| j]]]]]]; try lia; cbn [nth]; rewrite length_map; lia.
  Qed.

  Local Notation bBk := (fun kk => btB lo1 nB omB wr we1 we2 kk).
  Local Notation b1k := (fun kk => btS1 lo2 nS omS sig kk).
  Local Notation b2k := (fun kk => b2x ell lo2 nS omS pplain a b cin cout sig wr we1 we2 kk T).

  (* the mask part of slot vector v is the model's mask m_v *)
  Lemma msP_mask : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall v, (1 <= v <= 4)%nat ->
    map to_F (msP n1 ell lo1 lo2 (bBk (kzx pB pS mB qB mS qS)) (b1k (kzx pB pS mB qB mS qS)) (b2k (kzx pB pS mB qB mS qS)) v)
    = nth (v - 1) (mB ++ mS) [].
  Proof.
    intros pB pS mB qB mS qS hsh v hv.
    pose proof hsh as (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10).
    set (kk := kzx pB pS mB qB mS qS).
    unfold msP.
    rewrite (comb_msum ell lo1 lo2 nB nS omB omS pplain a b cin cout sig wr we1 we2 kk T).
    assert (eB : forall j, (j < 6)%nat -> PFx kk (3 * rw + j) = map to_F (map bx (nth j (LB mB qB) [])))
      by (intros j hj; apply PF_mB; assumption).
    assert (eS : forall j, (j < 6)%nat -> PFx kk (SO + rs + j) = map to_F (map bx (nth j (LS mS qS) [])))
      by (intros j hj; apply PF_mS; assumption).
    pose proof (eB 0%nat ltac:(lia)) as b0. rewrite Nat.add_0_r in b0.
    pose proof (eS 0%nat ltac:(lia)) as s0. rewrite Nat.add_0_r in s0.
    cbv beta in eB, eS, b0, s0.
    destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
    destruct mS as [| m3 [| m4 [| ? ?]]]; cbn in h8; try lia.
    destruct v as [| [| [| [| [| v]]]]]; try lia; unfold mcbE; cbn [map msum pairF fst snd].
    - rewrite b0, (eB 1%nat) by lia. unfold LB. cbn [nth]. rewrite reZ_F, imZ_F, to_F_one, to_F_tg.
      rewrite padd_nil. apply re_im_list.
    - rewrite (eB 2%nat), (eB 3%nat) by lia. unfold LB. cbn [nth]. rewrite reZ_F, imZ_F, to_F_one, to_F_tg.
      rewrite padd_nil. apply re_im_list.
    - rewrite s0, (eS 1%nat) by lia. unfold LS. cbn [nth]. rewrite reZ_F, imZ_F, to_F_one, to_F_tg.
      rewrite padd_nil. apply re_im_list.
    - rewrite (eS 2%nat), (eS 3%nat) by lia. unfold LS. cbn [nth]. rewrite reZ_F, imZ_F, to_F_one, to_F_tg.
      rewrite padd_nil. apply re_im_list.
  Qed.

  Local Notation tfunBx := (tfunB n1 ell lo1 lo2 pplain a b sig wr we1 we2 k T).
  Local Notation tfunSx := (tfunS n1 ell lo1 lo2 pplain a b cin cout sig wr we1 we2 k T).
  Local Notation vecPk := (fun kk => vecP n1 ell lo1 lo2 pplain a b sig kk (bBk kk) (b1k kk) (b2k kk) T).

  (* the four slot vectors are those of the model's honest opening *)
  Theorem vecs_run : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS ->
    map (fun v => map to_F (vecPk (kzx pB pS mB qB mS qS) v)) [1; 2; 3; 4]%nat
    = zipw padd mB (tfunBx pB) ++ zipw padd mS (tfunSx pS).
  Proof.
    intros pB pS mB qB mS qS hsh.
    assert (hv : forall v, (1 <= v <= 4)%nat ->
      map to_F (vecPk (kzx pB pS mB qB mS qS) v)
      = padd (nth (v - 1) (mB ++ mS) [])
             (pscale (to_F (nth 0 (tcl T) xzero))
                     (msumF (if Nat.leb v 2 then rowB n1 ell lo1 wr we1 we2 pB
                             else rowS n1 ell lo1 lo2 pplain a b cin cout sig wr we1 we2 k T pS)
                            (cbF n1 ell lo1 lo2 pplain a b sig k T v)))).
    { intros v hv. cbv beta. unfold vecP. rewrite to_F_padd, to_F_pscale.
      rewrite (msP_mask pB pS mB qB mS qS hsh v hv).
      rewrite (tfun_usP n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k T
                 Hp Hw Hk Hs Hu Hv HrA Hry Hrz Hkp pB pS mB qB mS qS hsh v hv).
      reflexivity. }
    pose proof hsh as (_ & _ & _ & _ & h5 & _ & _ & h8 & _).
    cbn [map]. rewrite (hv 1%nat), (hv 2%nat), (hv 3%nat), (hv 4%nat) by lia.
    destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
    destruct mS as [| m3 [| m4 [| ? ?]]]; cbn in h8; try lia.
    unfold tfunB, tfunS. reflexivity.
  Qed.

  Local Notation muPk := (fun kk => muP n1 ell lo1 lo2 pplain a b sig kk (bBk kk) (b1k kk) (b2k kk) T).
  Local Notation LsBx := (LsB n1 ell lo1 lo2 pplain a b sig k T).
  Local Notation LsSx := (LsS n1 ell lo1 lo2 pplain a b sig k T).

  (* mu is the model's first component of honO3 *)
  Theorem mu_run : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS ->
    to_F (muPk (kzx pB pS mB qB mS qS))
    = fadd (@LogDer.fsum Fq2 fzero fadd (zipw (@LogDer.dot Fq2 fzero fadd fmul) mB LsBx))
           (@LogDer.fsum Fq2 fzero fadd (zipw (@LogDer.dot Fq2 fzero fadd fmul) mS LsSx)).
  Proof.
    intros pB pS mB qB mS qS hsh.
    pose proof hsh as (_ & _ & _ & _ & h5 & _ & _ & h8 & _).
    cbv beta. unfold muP. rewrite to_F_fsum. cbn [map]. rewrite !to_F_dot.
    rewrite !(msP_mask pB pS mB qB mS qS hsh) by lia.
    unfold LsB, LsS.
    change (LP n1 ell lo1 lo2 pplain a b sig (kzx pB pS mB qB mS qS) T) with (LP n1 ell lo1 lo2 pplain a b sig k T).
    destruct mB as [| m1 [| m2 [| ? ?]]]; cbn in h5; try lia.
    destruct mS as [| m3 [| m4 [| ? ?]]]; cbn in h8; try lia.
    cbn [zipw LogDer.fsum nth app Nat.sub]. ring.
  Qed.

  Local Notation pvBPk := (fun kk => pvBP n1 ell lo1 (bBk kk) (b1k kk) (b2k kk) T).
  Local Notation tpBx := (tpB n1 ell lo1 wr we1 we2 T).
  Local Notation GBx := (GB n1 ell lo1 T).

  Hypothesis HgB : List.length (tgB T) = (3 * rw + 6)%nat.

  (* the proximity vector of the big matrix: proximity mask, gamma-combination of the data rows, mask rows *)
  Theorem pvB_run : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS ->
    map to_F (pvBPk (kzx pB pS mB qB mS qS)) = padd qB (padd (tpBx pB) (GBx mB)).
  Proof.
    intros pB pS mB qB mS qS hsh.
    set (kk := kzx pB pS mB qB mS qS).
    assert (eB : forall j, (j < 6)%nat -> PFx kk (3 * rw + j) = map to_F (map bx (nth j (LB mB qB) [])))
      by (intros j hj; apply PF_mB; assumption).
    cbv beta in eB. cbv beta. unfold pvBP.
    rewrite to_F_padd, !(comb_msum ell lo1 lo2 nB nS omB omS pplain a b cin cout sig wr we1 we2 kk T).
    f_equal.
    { cbn [map msum pairF fst snd]. rewrite (eB 4%nat), (eB 5%nat) by lia. unfold LB. cbn [nth].
      rewrite reZ_F, imZ_F, to_F_one, to_F_tg, padd_nil. apply re_im_list. }
    rewrite map_pairF_combine. unfold rwsBE.
    rewrite seq_app.
    rewrite combine_split by (rewrite length_map, length_firstn, !length_seq; lia).
    rewrite msum_app. rewrite length_seq. f_equal.
    - unfold tpB, cbPB. rewrite firstn_map, firstn_firstn. replace (Nat.min (3 * rw) (3 * rw + 4)) with (3 * rw)%nat by lia.
      apply msum_ext. intros iw hiw. destruct iw as [i w]. cbn [fst].
      apply in_combine_l, in_seq in hiw.
      unfold rowB. apply (rowsB n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k T Hp Hw Hk
                           pB pS mB qB mS qS hsh i). lia.
    - rewrite skipn_map, (skipn_firstn4 (3 * rw) (tgB T) xzero) by lia. cbn [map].
      assert (es : seq (3 * rw) 4 = [3 * rw + 0; 3 * rw + 1; 3 * rw + 2; 3 * rw + 3]%nat) by (cbn [seq]; f_equal; [lia | f_equal; [lia | f_equal; [lia | f_equal; lia]]]).
      rewrite Nat.add_0_l, es. cbn [combine msum fst snd].
      rewrite (eB 0%nat), (eB 1%nat), (eB 2%nat), (eB 3%nat) by lia. unfold LB. cbn [nth].
      rewrite !reZ_F, !imZ_F, padd_nil.
      unfold GB, Gm, gBi. rewrite Nat.add_0_r, !padd_assoc. reflexivity.
  Qed.

  Local Notation pvSPk := (fun kk => pvSP n1 ell lo1 lo2 (bBk kk) (b1k kk) (b2k kk) T).
  Local Notation tpSx := (tpS n1 ell lo1 lo2 pplain a b cin cout sig wr we1 we2 k T).
  Local Notation GSx := (GS ell lo2 T).
  Local Notation sxx := (sx n1 ell lo1 lo2).

  Hypothesis HgS : List.length (tgS T) = (rs + 6 + (4 * rs + 1))%nat.

  Lemma seq_shift6 : forall n st, map (fun i => (SO + i)%nat) (seq (st + 6) n) = map (fun j => (SO + (j + 6))%nat) (seq st n).
  Proof. induction n as [| n ih]; intro st; [reflexivity |]. cbn [seq map]. f_equal. exact (ih (S st)). Qed.

  Theorem pvS_run : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS ->
    map to_F (pvSPk (kzx pB pS mB qB mS qS)) = padd qS (padd (tpSx pS) (GSx mS)).
  Proof.
    intros pB pS mB qB mS qS hsh.
    set (kk := kzx pB pS mB qB mS qS).
    assert (eS : forall j, (j < 6)%nat -> PFx kk (SO + rs + j) = map to_F (map bx (nth j (LS mS qS) [])))
      by (intros j hj; apply PF_mS; assumption).
    cbv beta in eS. cbv beta. unfold pvSP.
    rewrite to_F_padd, !(comb_msum ell lo1 lo2 nB nS omB omS pplain a b cin cout sig wr we1 we2 kk T).
    f_equal.
    { cbn [map msum pairF fst snd]. rewrite (eS 4%nat), (eS 5%nat) by lia. unfold LS. cbn [nth].
      rewrite reZ_F, imZ_F, to_F_one, to_F_tg, padd_nil. apply re_im_list. }
    rewrite map_pairF_combine. unfold rwsSE. rewrite map_app, map_app.
    rewrite combine_split by (rewrite !length_app, !length_map, length_firstn, length_skipn, !length_seq; lia).
    rewrite length_map, length_seq.
    rewrite firstn_app, skipn_app, !length_map, length_firstn.
    replace (rs + 4 - Nat.min (rs + 4) (List.length (tgS T)))%nat with 0%nat by lia.
    replace (rs + 4 - Nat.min (rs + 4) (List.length (tgS T)))%nat with 0%nat by lia.
    rewrite firstn_O, skipn_O, app_nil_r, firstn_all2 by (rewrite length_map, length_firstn; lia).
    rewrite skipn_all2 by (rewrite length_map, length_firstn; lia). cbn [app].
    rewrite seq_app, map_app.
    rewrite combine_split by (rewrite length_map, length_firstn, !length_map, !length_seq; lia).
    rewrite length_map, length_seq.
    rewrite !msum_app.
    (* the mask rows *)
    assert (hM : msumF (PFx kk) (combine (map (fun i => (SO + i)%nat) (seq rs 4)) (skipn rs (map to_F (firstn (rs + 4) (tgS T)))))
                 = GSx mS).
    { rewrite <-firstn_map, skipn_firstn4 with (d := fzero) by (rewrite length_map; lia).
      rewrite !(nth_indep _ fzero (to_F xzero)) by (rewrite length_map; lia). rewrite !map_nth.
      assert (es : map (fun i => (SO + i)%nat) (seq rs 4) = [SO + rs + 0; SO + rs + 1; SO + rs + 2; SO + rs + 3]%nat)
        by (cbn [seq map]; f_equal; [lia | f_equal; [lia | f_equal; [lia | f_equal; lia]]]).
      rewrite es. cbn [combine msum fst snd].
      rewrite (eS 0%nat), (eS 1%nat), (eS 2%nat), (eS 3%nat) by lia. unfold LS. cbn [nth].
      rewrite !reZ_F, !imZ_F, padd_nil.
      unfold GS, Gm, gSi. rewrite Nat.add_0_r, !padd_assoc. reflexivity. }
    rewrite Nat.add_0_l. cbv beta in hM. rewrite hM.
    (* the data rows *)
    assert (hD : padd (msumF (PFx kk) (combine (map (fun i => (SO + i)%nat) (seq 0 rs)) (firstn rs (map to_F (firstn (rs + 4) (tgS T))))))
                      (msumF (PFx kk) (combine (map (fun i => (SO + i)%nat) (seq (rs + 6) (4 * rs + 1))) (map to_F (skipn (rs + 6) (tgS T)))))
                 = tpSx pS).
    { unfold tpS, cbPS. rewrite msum_app. f_equal.
      - rewrite firstn_map, firstn_firstn. replace (Nat.min rs (rs + 4)) with rs by lia.
        rewrite (map_ext_in (fun i => (SO + i)%nat) sxx (seq 0 rs))
          by (intros i hi; apply in_seq in hi; unfold sx; destruct (Nat.ltb_spec i rs); lia).
        apply msum_ext. intros [i w] hiw. cbn [fst].
        apply in_combine_l, in_map_iff in hiw. destruct hiw as (j & <- & hj). apply in_seq in hj.
        unfold rowS. rewrite (sidx_sx n1 ell lo1 lo2 T Hu Hv HrA Hry Hrz Hkp) by lia.
        apply (rowsS n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k T Hp Hw Hk
                 pB pS mB qB mS qS hsh j). lia.
      - rewrite seq_shift6.
        rewrite (map_ext_in (fun j => (SO + (j + 6))%nat) sxx (seq rs (4 * rs + 1)))
          by (intros i hi; apply in_seq in hi; unfold sx; destruct (Nat.ltb_spec i rs); lia).
        apply msum_ext. intros [i w] hiw. cbn [fst].
        apply in_combine_l, in_map_iff in hiw. destruct hiw as (j & <- & hj). apply in_seq in hj.
        unfold rowS. rewrite (sidx_sx n1 ell lo1 lo2 T Hu Hv HrA Hry Hrz Hkp) by lia.
        apply (rowsS n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k T Hp Hw Hk
                 pB pS mB qB mS qS hsh j). lia. }
    cbv beta in hD. rewrite <-hD.
    rewrite !padd_assoc. f_equal. apply padd_comm.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the opened columns *)

  Local Notation omBK := (zq_of omB).
  Local Notation omSK := (zq_of omS).
  Local Notation JBn := (map Z.to_nat (tJB T)).
  Local Notation JSn := (map Z.to_nat (tJS T)).
  Local Notation encB := (@encJ Fq2 fzero fone fadd fmul (emb omBK) JBn).
  Local Notation encS := (@encJ Fq2 fzero fone fadd fmul (emb omSK) JSn).
  Local Notation openedK := (@opened Zq qzero qone qadd qmul).
  Local Notation partsk := (fun kk => parts_of n1 ell lo1 lo2 pplain a b sig kk (bBk kk) (b1k kk) (b2k kk) T).
  Local Notation XeP := (fun kk i j => to_F (fXe (fT n1 ell lo1 lo2 (partsk kk) T) i j)).
  Local Notation datasBx := (datasB n1 ell lo1 wr we1 we2).

  Hypothesis HJBlt : forall j, In j JBn -> (j < nB)%nat.
  Hypothesis HJSlt : forall j, In j JSn -> (j < nS)%nat.

  Lemma peval_emb_rs : forall om (p : list Zq) j,
    @eval Fq2 fzero fadd fmul (map emb p) (@pw Fq2 fone fmul (emb om) j) = emb (@rs_enc Zq qzero qone qadd qmul om p j).
  Proof. intros om p j. exact (rs_enc_emb om p j). Qed.

  Lemma peval_re : forall om (m : list F) j,
    @eval Fq2 fzero fadd fmul (map re m) (@pw Fq2 fone fmul (emb om) j) = re (@rs_enc Fq2 fzero fone fadd fmul (emb om) m j).
  Proof. intros om m j. unfold ReedSolomon.rs_enc. rewrite emb_pw, eval_re. reflexivity. Qed.

  Lemma peval_im : forall om (m : list F) j,
    @eval Fq2 fzero fadd fmul (map im m) (@pw Fq2 fone fmul (emb om) j) = im (@rs_enc Fq2 fzero fone fadd fmul (emb om) m j).
  Proof. intros om m j. unfold ReedSolomon.rs_enc. rewrite emb_pw, eval_im. reflexivity. Qed.

  (* a data row of the big matrix, at the opened columns: the model's opened entries *)
  Theorem colsB_data : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall i, (i < 3 * rw)%nat ->
    map (XeP (kzx pB pS mB qB mS qS) i) JBn = map emb (openedK omBK (nth i datasBx []) (nth i pB []) JBn).
  Proof.
    intros pB pS mB qB mS qS hsh i hi.
    pose proof (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS k Hp Hk pB pS mB qB mS qS hsh) as hkz.
    unfold ReedSolomon.opened. rewrite (map_map _ emb). apply map_ext_in. intros j hj. cbv beta.
    rewrite (XeB n1 ell lo1 lo2 nB nqB nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ Hw hkz T i j hj (HJBlt j hj))
      by (unfold SOE; lia).
    rewrite (rowsB n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k T Hp Hw Hk
               pB pS mB qB mS qS hsh i hi).
    rewrite emb_bx. apply peval_emb_rs.
  Qed.

  (* the mask rows of the big matrix, at the opened columns: the model's encoded masks *)
  Theorem colsB_mask : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall j', (j' < 6)%nat ->
    map (XeP (kzx pB pS mB qB mS qS) (3 * rw + j')) JBn
    = nth j' [map re (encB (nth 0 mB [])); map im (encB (nth 0 mB [])); map re (encB (nth 1 mB []));
              map im (encB (nth 1 mB [])); map re (encB qB); map im (encB qB)] [].
  Proof.
    intros pB pS mB qB mS qS hsh j' hj'.
    pose proof (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS k Hp Hk pB pS mB qB mS qS hsh) as hkz.
    assert (e : forall j, In j JBn -> XeP (kzx pB pS mB qB mS qS) (3 * rw + j') j
                = @eval Fq2 fzero fadd fmul (map to_F (map bx (nth j' (LB mB qB) []))) (@pw Fq2 fone fmul (emb omBK) j)).
    { intros j hj. cbv beta.
      rewrite (XeB n1 ell lo1 lo2 nB nqB nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ Hw hkz T _ j hj (HJBlt j hj))
        by (unfold SOE; lia).
      rewrite (PF_mB pB pS mB qB mS qS hsh j' hj'). rewrite emb_bx. reflexivity. }
    transitivity (map (fun j => @eval Fq2 fzero fadd fmul (map to_F (map bx (nth j' (LB mB qB) [])))
                                  (@pw Fq2 fone fmul (emb omBK) j)) JBn); [apply map_ext_in; exact e |].
    unfold ZkOpenTranscript.encJ.
    destruct j' as [| [| [| [| [| [| j']]]]]]; try lia; unfold LB; cbn [nth];
      rewrite ?reZ_F, ?imZ_F, ?(map_map _ re), ?(map_map _ im); apply map_ext; intro j;
      first [apply peval_re | apply peval_im].
  Qed.

  Local Notation datasSx := (datasS ell lo2 pplain a b cin cout sig wr we1 we2 k T).

  (* a data row of the small matrix (row sx j0), at the opened columns *)
  Theorem colsS_data : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall j0, (j0 < rs + (4 * rs + 1))%nat ->
    map (XeP (kzx pB pS mB qB mS qS) (sxx j0)) JSn = map emb (openedK omSK (nth j0 datasSx []) (nth j0 pS []) JSn).
  Proof.
    intros pB pS mB qB mS qS hsh j0 hj0.
    pose proof (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS k Hp Hk pB pS mB qB mS qS hsh) as hkz.
    unfold ReedSolomon.opened. rewrite (map_map _ emb). apply map_ext_in. intros j hj. cbv beta.
    rewrite (XeS n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ Hp Hw hkz T _ j hj (HJSlt j hj))
      by (unfold sx; destruct (Nat.ltb_spec j0 rs); unfold SOE in *; lia).
    rewrite (rowsS n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k T Hp Hw Hk
               pB pS mB qB mS qS hsh j0 hj0).
    rewrite emb_bx. apply peval_emb_rs.
  Qed.

  (* the mask rows of the small matrix, at the opened columns *)
  Theorem colsS_mask : forall pB pS mB qB mS qS, shZ pB pS mB qB mS qS -> forall j', (j' < 6)%nat ->
    map (XeP (kzx pB pS mB qB mS qS) (SO + rs + j')) JSn
    = nth j' [map re (encS (nth 0 mS [])); map im (encS (nth 0 mS [])); map re (encS (nth 1 mS []));
              map im (encS (nth 1 mS [])); map re (encS qS); map im (encS qS)] [].
  Proof.
    intros pB pS mB qB mS qS hsh j' hj'.
    pose proof (kz_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS k Hp Hk pB pS mB qB mS qS hsh) as hkz.
    assert (e : forall j, In j JSn -> XeP (kzx pB pS mB qB mS qS) (SO + rs + j') j
                = @eval Fq2 fzero fadd fmul (map to_F (map bx (nth j' (LS mS qS) []))) (@pw Fq2 fone fmul (emb omSK) j)).
    { intros j hj. cbv beta.
      rewrite (XeS n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 _ Hp Hw hkz T _ j hj (HJSlt j hj))
        by (unfold SOE in *; lia).
      rewrite (PF_mS pB pS mB qB mS qS hsh j' hj'). rewrite emb_bx. reflexivity. }
    transitivity (map (fun j => @eval Fq2 fzero fadd fmul (map to_F (map bx (nth j' (LS mS qS) [])))
                                  (@pw Fq2 fone fmul (emb omSK) j)) JSn); [apply map_ext_in; exact e |].
    unfold ZkOpenTranscript.encJ.
    destruct j' as [| [| [| [| [| [| j']]]]]]; try lia; unfold LS; cbn [nth];
      rewrite ?reZ_F, ?imZ_F, ?(map_map _ re), ?(map_map _ im); apply map_ext; intro j;
      first [apply peval_re | apply peval_im].
  Qed.

End Open.
