(* Zero knowledge of the decryption proof, the opening (paper, Theorem 7.1,
   zero-knowledge part; steps (4) to (6) of the argument of Theorem 5.3).

   ZkJoin.open3_zk with K = Z_q, F = GF(q^2), emb x = (x, 0), for the
   layout of dec_proof.py (DecLayout.v):
     big matrix    data rows: the kd * rw rows of the digit tables;
                   two slots S1, S2 (tensor); mask rows re/im of m_S1,
                   m_S2 and of the proximity mask;
     small matrix  data rows: s, e, the mask table (rows SO, SO+1, SO+2);
                   three slots Ss, Se, Sm (func); mask rows re/im of
                   their masks and of the proximity mask.
   The claims are claimsD of DecLayout.v, batched with kappa (cbk, Lk of
   SlotKinds.v). The data rows are arbitrary: the check equations hold for
   any data, with the batched target value cvD computed from the data
   rows (pads do not enter the claims). That cvD is what the verifier
   computes from the transcript, for a witness, is the join
   (ZkDecJoin.v). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks ZkSumcheck ZkOpen
  ZkTranscript ZkOpenTranscript ZkJoin SlotKinds Opening OpenClaims RowLayout DecLayout.
From Examples Require Import ConcreteField ZkOpenMix.
Import ListNotations.

Add Field fieldF2do : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation padd := (@LogDer.padd Fq2 fadd).
Local Notation pscale := (@LogDer.pscale Fq2 fmul).
Local Notation vadd := (@LogDer.vadd Fq2 fadd).
Local Notation msumF := (@msum Fq2 fadd fmul).
Local Notation dotF := (@LogDer.dot Fq2 fzero fadd fmul).

(* pads after the data do not change an inner product with a short vector *)
Lemma dot_app_short : forall (u p L : list F), (length L <= length u)%nat -> dotF (u ++ p) L = dotF u L.
Proof.
  induction u as [| x u ih]; intros p L h; destruct L as [| y L]; cbn in h; try lia.
  - destruct p; reflexivity.
  - destruct p; reflexivity.
  - cbn [app LogDer.dot]. rewrite ih by lia. reflexivity.
Qed.

(* three masks in the proximity vector *)
Definition G3 (g : nat -> F) (m1 m2 m3 : list F) : list F :=
  padd (Gm g m1 m2) (padd (pscale (g 4%nat) (map re m3)) (pscale (g 5%nat) (map im m3))).
Definition G3h (g : nat -> F) (e1 e2 e3 : list F) : list F :=
  vadd (Ghm g e1 e2) (vadd (map (fmul (g 4%nat)) (map re e3)) (map (fmul (g 5%nat)) (map im e3))).

Lemma enc_G3 : forall om J g m1 m2 m3,
  @ZkOpenTranscript.encJ Fq2 fzero fone fadd fmul (emb om) J (G3 g m1 m2 m3)
  = G3h g (@ZkOpenTranscript.encJ Fq2 fzero fone fadd fmul (emb om) J m1)
          (@ZkOpenTranscript.encJ Fq2 fzero fone fadd fmul (emb om) J m2)
          (@ZkOpenTranscript.encJ Fq2 fzero fone fadd fmul (emb om) J m3).
Proof.
  intros om J g m1 m2 m3. unfold G3, G3h.
  rewrite !(@encJ_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), enc_Gm, !enc_pscale, !enc_re, !enc_im.
  reflexivity.
Qed.

Lemma nth_map_seq_any2 : forall {A : Type} (f : nat -> A) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros A f n i d h. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact h).
  rewrite map_nth, seq_nth by exact h. reflexivity.
Qed.

Lemma Gm_len2 : forall g m1 m2 kk, length m1 = kk -> length m2 = kk -> (length (Gm g m1 m2) <= kk)%nat.
Proof.
  intros g m1 m2 kk h1 h2. unfold Gm.
  rewrite !(@length_padd Fq2 fadd), !(@length_pscale Fq2 fmul), !length_map. lia.
Qed.

Lemma shapedM_nth2 : forall kk nm ms i, @shapedM Fq2 kk nm ms -> (i < nm)%nat -> length (nth i ms []) = kk.
Proof.
  intros kk nm ms i [hl hs] hi. unfold ZkOpen.lens in hs. rewrite Forall_forall in hs. apply hs, nth_In. lia.
Qed.

Lemma pad_len2 : forall (datas p : list (list Zq)) J i, @shapedP Zq datas J p -> (i < length datas)%nat ->
  length (nth i p []) = length J.
Proof.
  intros datas p J i [hl hs] hi. unfold ZkOpen.lens in hs. rewrite Forall_forall in hs. apply hs, nth_In. lia.
Qed.

Lemma G3_len : forall g m1 m2 m3 kk, length m1 = kk -> length m2 = kk -> length m3 = kk -> (length (G3 g m1 m2 m3) <= kk)%nat.
Proof.
  intros g m1 m2 m3 kk h1 h2 h3. unfold G3.
  rewrite !(@length_padd Fq2 fadd), !(@length_pscale Fq2 fmul), !length_map.
  pose proof (Gm_len2 g m1 m2 kk h1 h2). lia.
Qed.

Section DecOpen.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (nqB nB nqS nS : nat) (omB omS : Zq).

  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwD n1 ell lo1).
  Local Notation SO := (kd * rwD n1 ell lo1 + 6)%nat.
  Local Notation kB := (C1 + nqB)%nat.
  Local Notation kS := (C2 + nqS)%nat.

  (* the data rows (any data) *)
  Variables dB dS : nat -> list Zq.
  Hypothesis HdB : forall i, (i < kd * rw)%nat -> length (dB i) = C1.
  Hypothesis HdS : forall j, (j < 3)%nat -> length (dS j) = C2.
  Definition datasB : list (list Zq) := map dB (seq 0 (kd * rw)).
  Definition datasS : list (list Zq) := map dS (seq 0 3).

  (* the public data and the challenges that the claims use *)
  Variables (aF : list F) (ppF : F) (usF : nat -> list F).
  Variables dG dT : list nat.
  Variables ptD th2 rz rt : list F.
  Hypothesis HptD : length ptD = m.
  Hypothesis Hth2 : length th2 = n1.
  Hypothesis Hrz : length rz = m.
  Hypothesis Hrt : length rt = n1.
  Hypothesis HdG : length dG = m.
  Hypothesis HdT : length dT = n1.
  Hypothesis Hlo1 : (lo1 <= m)%nat.

  (* the opening's challenges *)
  Variables (kp : list F) (cc : F) (gB gS : list F).
  Hypothesis Hkp : length kp = (kd + 6)%nat.
  Variables JB JS : list nat.

  Local Notation cls := (@claimsD Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt).
  Local Notation LtV := (@LtD Fq2 fzero fone fadd fmul fsub n1 ell lo1 ptD rz).
  Local Notation gtv := (fun P => @gtval Fq2 fzero fadd fmul P kindD LtV).

  (* func-slot vectors fit in a row of the small matrix *)
  Hypothesis HLS : forall cl t, In cl cls -> In t cl -> kindD (tslot t) = true -> (length (tlv t) <= C2)%nat.

  Definition cbD (v : nat) : list (nat * F) := @cbk Fq2 fone fmul kindD (frowD SO) kp cls v.
  Definition LkD (v : nat) : list F := @Lk Fq2 fadd fmul kindD LtV kp cls v.

  (* the rows as field elements *)
  Definition rowB (pB : list (list Zq)) (i : nat) : list F := map emb (nth i datasB [] ++ nth i pB []).
  Definition rowS (pS : list (list Zq)) (i : nat) : list F := map emb (nth (i - SO) datasS [] ++ nth (i - SO) pS []).
  Definition Prow (pB pS : list (list Zq)) (r : nat) : list F := if Nat.ltb r SO then rowB pB r else rowS pS r.
  Definition P0 (r : nat) : list F :=
    if Nat.ltb r SO then map emb (nth r datasB []) else map emb (nth (r - SO) datasS []).

  Definition tfunB (pB : list (list Zq)) : list (list F) :=
    [pscale cc (msumF (rowB pB) (cbD 1)); pscale cc (msumF (rowB pB) (cbD 2))].
  Definition tfunS (pS : list (list Zq)) : list (list F) :=
    [pscale cc (msumF (rowS pS) (cbD 3)); pscale cc (msumF (rowS pS) (cbD 4)); pscale cc (msumF (rowS pS) (cbD 5))].
  Definition LsB : list (list F) := [LkD 1; LkD 2].
  Definition LsS : list (list F) := [LkD 3; LkD 4; LkD 5].

  (* the batched target value, from the data rows *)
  Definition cvD : F := fmul cc (dotF kp (map (gtv P0) cls)).

  (* ------------------------------------------------------------------ *)
  (* where the compiled slots live *)

  Lemma cbD_rows : forall v iw, In iw (cbD v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < kd * rw)%nat) /\
    ((v = 3 \/ v = 4 \/ v = 5)%nat -> (SO <= fst iw < SO + 3)%nat).
  Proof.
    intros v iw h. unfold cbD in h. apply in_map with (f := fst) in h.
    destruct (cbk_rows kindD (frowD SO) cls kp v (fst iw) h) as [[hk e] | (cl & t & hcl & ht & e1 & e2)].
    - split; intro hv.
      + destruct hv as [-> | ->]; cbn in hk; discriminate.
      + rewrite e. unfold frowD. destruct hv as [-> | [-> | ->]]; cbn; unfold rS, rE, rMd; lia.
    - destruct (claimsD_terms ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdG HdT cl t hcl ht)
        as [(es & d & j & hd & hj & er) | [(es & d & j & hd & hj & er) | [(es & er) | [(es & er) | (es & er)]]]];
        rewrite e1 in es; subst v; split; intro hv;
        try (destruct hv as [hv | hv]; discriminate hv); try (destruct hv as [hv | [hv | hv]]; discriminate hv).
      all: rewrite <-e2, er; unfold rS, rE, rMd; nia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the batched claim *)

  Lemma len_lovec : forall x, length (@lovec Fq2 fzero fone fadd fmul fsub m lo1 x) = C1.
  Proof.
    intro x. unfold RowLayout.lovec. rewrite length_app, repeat_length.
    rewrite DecLayout.eqvec_length.
    unfold RowLayout.loE. replace (Nat.min lo1 m) with lo1 by lia. lia.
  Qed.

  Lemma Lof_len : forall cl t, In cl cls -> In t cl ->
    (length (@Lof Fq2 kindD LtV t) <= if Nat.ltb (trow t) SO then C1 else C2)%nat.
  Proof.
    intros cl t hcl ht. unfold SlotKinds.Lof.
    destruct (claimsD_terms ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdG HdT cl t hcl ht)
      as [(es & d & j & hd & hj & er) | [(es & d & j & hd & hj & er) | [(es & er) | [(es & er) | (es & er)]]]];
      rewrite es; cbn [kindD Nat.leb].
    - rewrite er. destruct (Nat.ltb_spec (d * rw + j) SO); [| nia]. unfold LtD. cbn. rewrite len_lovec. lia.
    - rewrite er. destruct (Nat.ltb_spec (d * rw + j) SO); [| nia]. unfold LtD. cbn. rewrite len_lovec. lia.
    - rewrite er. unfold rS. destruct (Nat.ltb_spec SO SO); [lia |].
      apply (HLS cl t hcl ht). rewrite es. reflexivity.
    - rewrite er. unfold rE. destruct (Nat.ltb_spec (SO + 1) SO); [lia |].
      apply (HLS cl t hcl ht). rewrite es. reflexivity.
    - rewrite er. unfold rMd. destruct (Nat.ltb_spec (SO + 2) SO); [lia |].
      apply (HLS cl t hcl ht). rewrite es. reflexivity.
  Qed.

  Lemma term_row : forall cl t, In cl cls -> In t cl -> (trow t < kd * rw)%nat \/ (SO <= trow t < SO + 3)%nat.
  Proof.
    intros cl t hcl ht.
    destruct (claimsD_terms ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdG HdT cl t hcl ht)
      as [(es & d & j & hd & hj & er) | [(es & d & j & hd & hj & er) | [(es & er) | [(es & er) | (es & er)]]]];
      rewrite er; unfold rS, rE, rMd; [left; nia | left; nia | right; lia | right; lia | right; lia].
  Qed.

  Lemma gtv_pads : forall pB pS, length pB = length datasB -> length pS = length datasS ->
    forall cl, In cl cls -> gtv (Prow pB pS) cl = gtv P0 cl.
  Proof.
    intros pB pS hB hS cl hcl.
    assert (gen : forall cl', (forall t, In t cl' -> In t cl) -> gtv (Prow pB pS) cl' = gtv P0 cl').
    { induction cl' as [| t cl' ih]; intro hsub; [reflexivity |].
      cbn [SlotKinds.gtval]. rewrite ih by (intros t' h'; apply hsub; right; exact h'). f_equal. f_equal.
      pose proof (hsub t (or_introl eq_refl)) as ht. pose proof (Lof_len cl t hcl ht) as hl.
      pose proof (term_row cl t hcl ht) as hr.
      unfold Prow, P0, rowB, rowS. destruct (Nat.ltb_spec (trow t) SO) as [h | h].
      - rewrite map_app. apply dot_app_short. rewrite length_map.
        destruct hr as [hr | hr]; [| lia].
        unfold datasB. rewrite (nth_map_seq_any2 dB (kd * rw) (trow t) [] hr), HdB by exact hr. exact hl.
      - rewrite map_app. apply dot_app_short. rewrite length_map.
        destruct hr as [hr | hr]; [lia |].
        unfold datasS. rewrite (nth_map_seq_any2 dS 3 (trow t - SO) [] ltac:(lia)), HdS by lia. exact hl. }
    apply gen. tauto.
  Qed.

  Lemma vsum_ext : forall (P P' : nat -> list F) cb L, (forall iw, In iw cb -> P (fst iw) = P' (fst iw)) ->
    @vsum Fq2 fzero fadd fmul P cb L = @vsum Fq2 fzero fadd fmul P' cb L.
  Proof.
    intros P P'; induction cb as [| iw cb ih]; intros L h; [reflexivity |]. cbn [Opening.vsum].
    rewrite (h iw (or_introl eq_refl)), ih by (intros iw' hi; apply h; right; exact hi). reflexivity.
  Qed.

  Theorem Hmu_dec : forall pB pS, length pB = length datasB -> length pS = length datasS ->
    fadd (@LogDer.fsum Fq2 fzero fadd (zipw dotF (tfunB pB) LsB))
         (@LogDer.fsum Fq2 fzero fadd (zipw dotF (tfunS pS) LsS)) = cvD.
  Proof.
    intros pB pS hB hS. unfold tfunB, tfunS, LsB, LsS, cvD. cbn [zipw LogDer.fsum].
    rewrite !(@dot_pscale_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite !(@dot_msum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    assert (eB : forall v, (v = 1 \/ v = 2)%nat ->
              @vsum Fq2 fzero fadd fmul (rowB pB) (cbD v) (LkD v) = @vsum Fq2 fzero fadd fmul (Prow pB pS) (cbD v) (LkD v)).
    { intros v hv. apply vsum_ext. intros iw hiw. destruct (cbD_rows v iw hiw) as [h _].
      unfold Prow. destruct (Nat.ltb_spec (fst iw) SO); [reflexivity | pose proof (h hv); lia]. }
    assert (eS : forall v, (v = 3 \/ v = 4 \/ v = 5)%nat ->
              @vsum Fq2 fzero fadd fmul (rowS pS) (cbD v) (LkD v) = @vsum Fq2 fzero fadd fmul (Prow pB pS) (cbD v) (LkD v)).
    { intros v hv. apply vsum_ext. intros iw hiw. destruct (cbD_rows v iw hiw) as [_ h].
      unfold Prow. destruct (Nat.ltb_spec (fst iw) SO); [pose proof (h hv); lia | reflexivity]. }
    rewrite (eB 1%nat), (eB 2%nat), (eS 3%nat), (eS 4%nat), (eS 5%nat) by tauto.
    pose proof (@batch_mixed Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field (Prow pB pS) kindD LtV (frowD SO)
                  [1; 2; 3; 4; 5]%nat cls kp ltac:(repeat constructor; cbn; intuition lia)
                  ltac:(rewrite Hkp; symmetry; eapply claimsD_length; eassumption)) as hb.
    replace (map (gtv P0) cls) with (map (gtv (Prow pB pS)) cls)
      by (apply map_ext_in; intros cl hcl; apply gtv_pads; assumption).
    rewrite <-hb.
    - unfold cbD, LkD. cbn [map LogDer.fsum]. field.
    - intros cl hcl t ht.
      destruct (claimsD_terms ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdG HdT cl t hcl ht)
        as [(es & _) | [(es & _) | [(es & _) | [(es & _) | (es & _)]]]]; rewrite es; cbn; tauto.
    - intros cl hcl t ht hk.
      destruct (claimsD_terms ftg n1 ell lo1 SO kd base aF ppF usF dG dT ptD th2 rz rt HptD Hth2 Hrz Hrt HdG HdT cl t hcl ht)
        as [(es & _) | [(es & _) | [(es & er) | [(es & er) | (es & er)]]]]; rewrite es in hk |- *;
        try discriminate; rewrite er; reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the shifts at the opened columns, from the opened entries *)

  Hypothesis HnB : forall i j, (i < nB)%nat -> (j < nB)%nat -> @pw Zq qone qmul omB i = @pw Zq qone qmul omB j -> i = j.
  Hypothesis HnS : forall i j, (i < nS)%nat -> (j < nS)%nat -> @pw Zq qone qmul omS i = @pw Zq qone qmul omS j -> i = j.
  Hypothesis HomB0 : omB <> qzero.
  Hypothesis HomS0 : omS <> qzero.
  Hypothesis HJBnd : NoDup JB.
  Hypothesis HJSnd : NoDup JS.
  Hypothesis HJBlt : forall j, In j JB -> (j < nB)%nat.
  Hypothesis HJSlt : forall j, In j JS -> (j < nS)%nat.
  Hypothesis HJBlen : length JB = nqB.
  Hypothesis HJSlen : length JS = nqS.

  Local Notation encB := (@ZkOpenTranscript.encJ Fq2 fzero fone fadd fmul (emb omB) JB).
  Local Notation encS := (@ZkOpenTranscript.encJ Fq2 fzero fone fadd fmul (emb omS) JS).
  Local Notation openedK := (@opened Zq qzero qone qadd qmul).

  Definition shJB (ys : list (list Zq)) : list (list F) :=
    [map (fmul cc) (msumJ JB (fun i => map emb (nth i ys [])) (cbD 1));
     map (fmul cc) (msumJ JB (fun i => map emb (nth i ys [])) (cbD 2))].
  Definition shJS (ys : list (list Zq)) : list (list F) :=
    [map (fmul cc) (msumJ JS (fun i => map emb (nth (i - SO) ys [])) (cbD 3));
     map (fmul cc) (msumJ JS (fun i => map emb (nth (i - SO) ys [])) (cbD 4));
     map (fmul cc) (msumJ JS (fun i => map emb (nth (i - SO) ys [])) (cbD 5))].

  Lemma len_datasB : length datasB = (kd * rw)%nat.
  Proof. unfold datasB. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma len_datasS : length datasS = 3%nat.
  Proof. reflexivity. Qed.

  Theorem HshB_dec : forall pB, length pB = length datasB ->
    map encB (tfunB pB) = shJB (zipw (fun d p => openedK omB d p JB) datasB pB).
  Proof.
    intros pB hl. unfold tfunB, shJB. cbn [map]. rewrite !enc_pscale, !enc_msum.
    assert (e : forall v, (v = 1 \/ v = 2)%nat -> msumJ JB (fun i => encB (rowB pB i)) (cbD v)
                  = msumJ JB (fun i => map emb (nth i (zipw (fun d p => openedK omB d p JB) datasB pB) [])) (cbD v)).
    { intros v hv. apply msumJ_ext. intros iw hiw. destruct (cbD_rows v iw hiw) as [h _].
      unfold rowB. rewrite enc_emb. f_equal. symmetry.
      refine (nth_zipw (fun d p => openedK omB d p JB) datasB pB _ [] [] [] _ _);
        [rewrite len_datasB; apply h; exact hv | symmetry; exact hl]. }
    rewrite (e 1%nat), (e 2%nat) by tauto. reflexivity.
  Qed.

  Theorem HshS_dec : forall pS, length pS = length datasS ->
    map encS (tfunS pS) = shJS (zipw (fun d p => openedK omS d p JS) datasS pS).
  Proof.
    intros pS hl. unfold tfunS, shJS. cbn [map]. rewrite !enc_pscale, !enc_msum.
    assert (e : forall v, (v = 3 \/ v = 4 \/ v = 5)%nat -> msumJ JS (fun i => encS (rowS pS i)) (cbD v)
                  = msumJ JS (fun i => map emb (nth (i - SO) (zipw (fun d p => openedK omS d p JS) datasS pS) [])) (cbD v)).
    { intros v hv. apply msumJ_ext. intros iw hiw. destruct (cbD_rows v iw hiw) as [_ h].
      pose proof (h hv) as hr. unfold rowS. rewrite enc_emb. f_equal. symmetry.
      refine (nth_zipw (fun d p => openedK omS d p JS) datasS pS _ [] [] [] _ _);
        [rewrite len_datasS; lia | symmetry; exact hl]. }
    rewrite (e 3%nat), (e 4%nat), (e 5%nat) by tauto. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the proximity vectors *)

  Definition cbPB : list (nat * F) := combine (seq 0 (kd * rw)) (firstn (kd * rw) gB).
  Definition cbPS : list (nat * F) := combine (map (fun j => SO + j)%nat (seq 0 3)) (firstn 3 gS).

  Definition tpB (pB : list (list Zq)) : list F := msumF (rowB pB) cbPB.
  Definition tpS (pS : list (list Zq)) : list F := msumF (rowS pS) cbPS.
  Definition shpB (ys : list (list Zq)) : list F := msumJ JB (fun i => map emb (nth i ys [])) cbPB.
  Definition shpS (ys : list (list Zq)) : list F := msumJ JS (fun i => map emb (nth (i - SO) ys [])) cbPS.

  Lemma cbPB_rows : forall iw, In iw cbPB -> (fst iw < kd * rw)%nat.
  Proof. intros [i w] h. apply in_combine_l in h. apply in_seq in h. cbn. lia. Qed.
  Lemma cbPS_rows : forall iw, In iw cbPS -> (SO <= fst iw < SO + 3)%nat.
  Proof.
    intros [i w] h. apply in_combine_l in h. apply in_map_iff in h. destruct h as (j & <- & hj).
    apply in_seq in hj. cbn. lia.
  Qed.

  Theorem HspB_dec : forall pB, length pB = length datasB ->
    encB (tpB pB) = shpB (zipw (fun d p => openedK omB d p JB) datasB pB).
  Proof.
    intros pB hl. unfold tpB, shpB. rewrite enc_msum. apply msumJ_ext. intros iw hiw.
    pose proof (cbPB_rows iw hiw) as h. unfold rowB. rewrite enc_emb. f_equal. symmetry.
    refine (nth_zipw (fun d p => openedK omB d p JB) datasB pB _ [] [] [] _ _);
      [rewrite len_datasB; exact h | symmetry; exact hl].
  Qed.

  Theorem HspS_dec : forall pS, length pS = length datasS ->
    encS (tpS pS) = shpS (zipw (fun d p => openedK omS d p JS) datasS pS).
  Proof.
    intros pS hl. unfold tpS, shpS. rewrite enc_msum. apply msumJ_ext. intros iw hiw.
    pose proof (cbPS_rows iw hiw) as h. unfold rowS. rewrite enc_emb. f_equal. symmetry.
    refine (nth_zipw (fun d p => openedK omS d p JS) datasS pS _ [] [] [] _ _);
      [rewrite len_datasS; lia | symmetry; exact hl].
  Qed.

  Definition gBi (i : nat) : F := nth (kd * rw + i) gB fzero.
  Definition gSi (i : nat) : F := nth (3 + i) gS fzero.

  Definition GB (ms : list (list F)) : list F := Gm gBi (nth 0 ms []) (nth 1 ms []).
  Definition GS (ms : list (list F)) : list F := G3 gSi (nth 0 ms []) (nth 1 ms []) (nth 2 ms []).
  Definition GhB (es : list (list F)) : list F :=
    Ghm gBi (nth 0 es (map (fun _ => fzero) JB)) (nth 1 es (map (fun _ => fzero) JB)).
  Definition GhS (es : list (list F)) : list F :=
    G3h gSi (nth 0 es (map (fun _ => fzero) JS)) (nth 1 es (map (fun _ => fzero) JS)) (nth 2 es (map (fun _ => fzero) JS)).

  Theorem HGB_dec : forall ms, encB (GB ms) = GhB (map encB ms).
  Proof.
    intro ms. unfold GB, GhB. rewrite enc_Gm. f_equal; symmetry; exact (map_nth (fun m => encB m) ms [] _).
  Qed.

  Theorem HGS_dec : forall ms, encS (GS ms) = GhS (map encS ms).
  Proof.
    intro ms. unfold GS, GhS. rewrite enc_G3. f_equal; symmetry; exact (map_nth (fun m => encS m) ms [] _).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* lengths *)


  Local Notation shapedPB := (@shapedP Zq datasB JB).
  Local Notation shapedPS := (@shapedP Zq datasS JS).

  Lemma rowB_len : forall p i, shapedPB p -> (i < kd * rw)%nat -> (length (rowB p i) <= kB)%nat.
  Proof.
    intros p i hp hi. unfold rowB. rewrite length_map, length_app.
    unfold datasB. rewrite (nth_map_seq_any2 dB (kd * rw) i [] hi), HdB by exact hi.
    rewrite (pad_len2 datasB p JB i hp) by (rewrite len_datasB; exact hi). rewrite HJBlen. lia.
  Qed.

  Lemma rowS_len : forall p i, shapedPS p -> (SO <= i < SO + 3)%nat -> (length (rowS p i) <= kS)%nat.
  Proof.
    intros p i hp hi. unfold rowS. rewrite length_map, length_app.
    unfold datasS. rewrite (nth_map_seq_any2 dS 3 (i - SO) [] ltac:(lia)), HdS by lia.
    rewrite (pad_len2 datasS p JS (i - SO) hp) by (rewrite len_datasS; lia). rewrite HJSlen. lia.
  Qed.

  Lemma HtkB_dec : forall p, shapedPB p -> Forall (fun t => (length t <= kB)%nat) (tfunB p).
  Proof.
    intros p hp. unfold tfunB.
    repeat constructor; rewrite (@length_pscale Fq2 fmul); apply msum_length; intros iw hiw;
      apply rowB_len; [exact hp | | exact hp |]; apply (proj1 (cbD_rows _ iw hiw)); tauto.
  Qed.

  Lemma HtkS_dec : forall p, shapedPS p -> Forall (fun t => (length t <= kS)%nat) (tfunS p).
  Proof.
    intros p hp. unfold tfunS.
    repeat constructor; rewrite (@length_pscale Fq2 fmul); apply msum_length; intros iw hiw;
      apply rowS_len; try exact hp; apply (proj2 (cbD_rows _ iw hiw)); tauto.
  Qed.

  Lemma HtpB_dec : forall p, shapedPB p -> (length (tpB p) <= kB)%nat.
  Proof. intros p hp. apply msum_length. intros iw hiw. apply rowB_len; [exact hp | exact (cbPB_rows iw hiw)]. Qed.

  Lemma HtpS_dec : forall p, shapedPS p -> (length (tpS p) <= kS)%nat.
  Proof. intros p hp. apply msum_length. intros iw hiw. apply rowS_len; [exact hp | exact (cbPS_rows iw hiw)]. Qed.

  Lemma HGlB_dec : forall ms, @shapedM Fq2 kB 2 ms -> (length (GB ms) <= kB)%nat.
  Proof. intros ms h. apply Gm_len2; apply (shapedM_nth2 kB 2 ms); [exact h | lia | exact h | lia]. Qed.
  Lemma HGlS_dec : forall ms, @shapedM Fq2 kS 3 ms -> (length (GS ms) <= kS)%nat.
  Proof.
    intros ms h. apply G3_len; apply (shapedM_nth2 kS 3 ms); [exact h | lia | exact h | lia | exact h | lia].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the instance *)

  Definition honDO := @honO3 Zq qzero qone qadd qmul Fq2 fzero fone fadd fmul emb omB omS JB JS
                        datasB datasS tfunB tfunS tpB tpS GB GS LsB LsS.
  Definition oviewDO := @oview3 Zq qzero qone qadd qmul Fq2 fadd omB omS JB JS datasB datasS tfunB tfunS tpB tpS GB GS.
  Definition coinsDO := @O3L Zq Fq2 lq lf2 JB JS datasB datasS kB 2 kB kS 3 kS.

  Theorem dec_open_parts : forall cv, cv = cvD ->
    NoDup coinsDO
    /\ (forall x, In x coinsDO -> In (oviewDO x) coinsDO)
    /\ (forall x x', In x coinsDO -> In x' coinsDO -> oviewDO x = oviewDO x' -> x = x')
    /\ (forall v, In v coinsDO -> exists x, In x coinsDO /\ oviewDO x = v)
    /\ (forall x, In x coinsDO ->
          honDO x = @simO3 Zq Fq2 fzero fone fadd fmul fsub emb omB omS JB JS LsB LsS cv
                       shJB shJS shpB shpS GhB GhS (oviewDO x)).
  Proof.
    intros cv ->. unfold honDO, coinsDO, oviewDO.
    refine (@open3_parts Zq qzero qone qadd qmul qsub qdiv qopp qinv Zq_dec Zq_field
              Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field
              emb lq lq_NoDup lq_all lf2 lf2_NoDup lf2_all omB omS nB nS HnB HnS HomB0 HomS0
              JB JS HJBnd HJSnd HJBlt HJSlt datasB datasS kB 2 kB kS 3 kS
              tfunB tfunS tpB tpS GB GS
              (fun _ => eq_refl) (fun _ => eq_refl) HtkB_dec HtkS_dec HtpB_dec HtpS_dec HGlB_dec HGlS_dec
              LsB LsS cvD shJB shJS shpB shpS GhB GhS _ _ _ _ _ (fun ms _ => HGB_dec ms) (fun ms _ => HGS_dec ms)).
    - intros pB pS [hB _] [hS _]. apply Hmu_dec; assumption.
    - intros pB [h _]. exact (HshB_dec pB h).
    - intros pS [h _]. exact (HshS_dec pS h).
    - intros pB [h _]. exact (HspB_dec pB h).
    - intros pS [h _]. exact (HspS_dec pS h).
  Qed.

  (* Theorem 7.1, zero knowledge of the opening, for any committed data *)
  Theorem dec_open_zk : Permutation (map honDO coinsDO)
    (map (@simO3 Zq Fq2 fzero fone fadd fmul fsub emb omB omS JB JS LsB LsS cvD shJB shJS shpB shpS GhB GhS) coinsDO).
  Proof.
    destruct (dec_open_parts cvD eq_refl) as (n & i & j & sj & e).
    exact (zk_perm oviewDO honDO _ coinsDO coinsDO n n i j sj e).
  Qed.

End DecOpen.
