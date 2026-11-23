(* Knowledge soundness of the decryption proof (paper, Theorem 7.1), for
   the protocol of dec_derive with the opening of pcs_open_verify, as an
   interactive oracle proof against an adaptive prover.

   Committed words. X i is the committed word of row i. All rows are
   committed before the first challenge. Rows of the small matrix are
   numbered from SO.

   Extractor. Every row is decoded by the decoder of its matrix
   (RsDecode.v). The digit tables, the key share s and its noise e, and
   the masks are read off the decoded rows (DecLayout.v).

   Theorem dec_theorem_7_1. If the extracted (digits, s, e) is not a
   witness (digits roots of phiR, s and e ternary, (D) and (K) coefficient
   by coefficient), the challenge tuples for which the verifier accepts
   number at most

       dec_bound * |O| + open_bound * |Omega_dec|

   where Omega_dec are the challenge tuples of the sumcheck layer and O
   those of the opening (kd + 6 claims).

   Assumed: a proximity lemma for each of the two row codes (ProxB,
   ProxS). Everything else is a hypothesis on the shape of the instance or
   of the messages, which the verifier enforces. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Bgv Proximity ReedSolomon Opening MatQueries OpenSound RsDecode OpenSoundDec SlotKinds OpenClaims Sumcheck SumcheckMask SumcheckSound MaskedExt CubeIndex ZkSumcheck LayoutLemmas RowLayout ZeroTest DecSound DecLayout.
Import ListNotations.

Section DecFinal.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Notation pw := (@pw F one mul).
  Local Notation pi := (@pi F zero add mul).
  Local Notation mle := (@mle F zero one add mul sub).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  (* the instance *)
  Variables (a b : list F) (pp offB : F).
  Variables n1 ell base kd : nat.
  Hypothesis Hn1 : (1 <= n1)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Variables us ts : nat -> list F.
  Variable phiR : list F.
  Hypothesis HphiR : (length phiR <= S base)%nat.

  (* the layout *)
  Variable tg : F.
  Variables lo1 SO : nat.
  Local Notation rwv := (rwD n1 ell lo1).
  Hypothesis HSO : (kd * rwv + 6 <= SO)%nat.

  Definition dG : list nat := map (degZ m base) (seq 0 m).
  Definition dT : list nat := map (degZ n1 3) (seq 0 n1).

  (* the two row codes and their proximity lemmas *)
  Variables omB omS : F.
  Variables nb kb eb nqb pnb : nat.
  Variables ns ks es nqs pns : nat.
  Hypothesis HkB : (kb <= nb)%nat.
  Hypothesis HkS : (ks <= ns)%nat.
  Hypothesis HnodesB : forall i j, (i < nb)%nat -> (j < nb)%nat -> pw omB i = pw omB j -> i = j.
  Hypothesis HnodesS : forall i j, (i < ns)%nat -> (j < ns)%nat -> pw omS i = pw omS j -> i = j.
  Hypothesis HeB : (2 * eb < nb - kb + 1)%nat.
  Hypothesis HeS : (2 * es < ns - ks + 1)%nat.
  Local Notation codeB := (@rs_code F zero one add mul omB nb kb).
  Local Notation codeS := (@rs_code F zero one add mul omS ns ks).
  Hypothesis ProxB : forall (mw : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close nb eb codeB (pi mw rows g)) ->
    (pnb * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= eb)%nat /\ codeB cm /\ agree_out nb E mw cm /\
      Forall2 (fun r c => codeB c /\ agree_out nb E r c) rows cs.
  Hypothesis ProxS : forall (mw : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close ns es codeS (pi mw rows g)) ->
    (pns * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= es)%nat /\ codeS cm /\ agree_out ns E mw cm /\
      Forall2 (fun r c => codeS c /\ agree_out ns E r c) rows cs.

  (* ------------------------------------------------------------------ *)
  (* committed words and decoded rows *)

  Variable X : nat -> nat -> F.

  Definition rwsB : list nat := seq 0 (kd * rwv + 4).
  Definition rwsS : list nat := map (fun i => (SO + i)%nat) (seq 0 9).

  Definition Pd : nat -> list F := @Pdec F zero one add mul Fdec lf omB omS nb kb eb ns ks es X rwsB.

  (* the extracted witness *)
  Definition dts : list (list F -> F) := @dtsT F zero one Fdec Pd n1 ell lo1 kd.
  Definition stab : list F -> F := @stabT F zero one Fdec Pd SO.
  Definition etab : list F -> F := @etabT F zero one Fdec Pd SO.

  (* the defect tables *)
  Definition Dtab : list F -> F := @DtabT F zero one add mul sub opp Fdec Pd n1 ell lo1 SO kd base pp offB us ts.
  Definition Ktab : list F -> F := @KtabT F zero one add mul sub opp Fdec Pd n1 SO a b pp.

  (* the masks, read off the mask table *)
  Local Notation ThT := (@ThT F).
  Local Notation P2 := (@P2 F).
  Local Notation WD := (@WD F).
  Local Notation wTh := (@wTh F).
  Local Notation wrG := (@wrG F).
  Local Notation wrT := (@wrT F).

  Definition avsG (_ : ThT) : list F := @avG F zero add mul Pd tg SO kd.
  Definition a0G (_ : ThT) : F := @a0GT F zero add mul Pd tg SO kd.
  Definition csG (_ : ThT) : list (list F) := @csGT F zero add mul Pd tg SO kd dG.
  Definition avsT (_ : P2) : list F := @avT F zero add mul Pd tg SO kd.
  Definition a0T (_ : P2) : F := @a0TT F zero add mul Pd tg SO kd dG.
  Definition csT (_ : P2) : list (list F) := @csTT F zero add mul Pd tg SO kd dG dT.

  Lemma nth_map_seqN : forall (f : nat -> nat) (n i : nat), (i < n)%nat -> nth i (map f (seq 0 n)) 0%nat = f i.
  Proof.
    intros f n i hi.
    rewrite (nth_indep _ 0%nat (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth f (seq 0 n) 0%nat i), seq_nth by exact hi. reflexivity.
  Qed.

  Lemma mask_shapeD : forall (Pm : list F) (off : nat) (degs : list nat),
    length (@maskCs F zero add mul tg Pm off degs) = length degs /\
    forall i, (i < length degs)%nat ->
      length (nth i (@maskCs F zero add mul tg Pm off degs) []) = nth i degs 0%nat.
  Proof.
    intros Pm off degs. unfold RowLayout.maskCs. split.
    + apply (@chunks_length F).
    + apply (@shaped_nth F). apply (@chunks_shaped F). rewrite length_map, length_seq. lia.
  Qed.

  Lemma dG_len : length dG = m. Proof. unfold dG. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma dT_len : length dT = n1. Proof. unfold dT. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma dts_len : length dts = kd. Proof. unfold dts, DecLayout.dtsT. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma HavsG_F : forall p, length (avsG p) = length dts.
  Proof. intro p. rewrite dts_len. unfold avsG, DecLayout.avG. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma HcsG_F : forall p, length (csG p) = m.
  Proof. intro p. unfold csG, DecLayout.csGT. rewrite (proj1 (mask_shapeD _ _ _)). apply dG_len. Qed.
  Lemma HdegG_F : forall p i, (i < m)%nat -> (length (nth i (csG p) []) <= degZ m base i)%nat.
  Proof.
    intros p i hi. unfold csG, DecLayout.csGT.
    rewrite (proj2 (mask_shapeD _ _ _)) by (rewrite dG_len; exact hi).
    unfold dG. rewrite nth_map_seqN by exact hi. lia.
  Qed.
  Lemma HavsT_F : forall p, length (avsT p) = 2%nat.
  Proof. reflexivity. Qed.
  Lemma HcsT_F : forall p, length (csT p) = n1.
  Proof. intro p. unfold csT, DecLayout.csTT. rewrite (proj1 (mask_shapeD _ _ _)). apply dT_len. Qed.
  Lemma HdegT_F : forall p i, (i < n1)%nat -> (length (nth i (csT p) []) <= degZ n1 3 i)%nat.
  Proof.
    intros p i hi. unfold csT, DecLayout.csTT.
    rewrite (proj2 (mask_shapeD _ _ _)) by (rewrite dT_len; exact hi).
    unfold dT. rewrite nth_map_seqN by exact hi. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the two compressed claims *)

  Definition VD (th : ThT) : F := @VDv F zero one add mul sub Fdec n1 ell pp offB ts (fst th).
  Definition VK (th : ThT) : F := @VKv F zero one add mul sub n1 b (snd th).
  Definition LD (th : ThT) : F := sub (VD th) (mle m Dtab (fst th)).
  Definition LK (th : ThT) : F := sub (VK th) (mle n1 Ktab (snd th)).

  Lemma HlinD_F : forall th, In th (@OTh F lf n1 ell) -> sub (VD th) (LD th) = mle m Dtab (fst th).
  Proof. intros th _. unfold LD. field. Qed.
  Lemma HlinK_F : forall th, In th (@OTh F lf n1 ell) -> sub (VK th) (LK th) = mle n1 Ktab (snd th).
  Proof. intros th _. unfold LK. field. Qed.

  (* the claims of the opening *)
  Definition clsW (w : WD) : list (list (@gterm F)) :=
    @claimsD F zero one add mul sub opp tg n1 ell lo1 SO kd base a pp us dG dT
             (fst (wTh w)) (snd (wTh w)) (wrG w) (wrT w).
  Definition LtW (w : WD) : nat -> list F := @LtD F zero one add mul sub n1 ell lo1 (fst (wTh w)) (wrG w).

  Definition tvW (w : WD) : list F :=
    @tvD F zero one add mul sub n1 ell dts stab etab avsG a0G csG avsT a0T csT LD LK w.

  (* the layout identity, for the extracted tables *)
  Theorem layout_tvD : forall w : WD,
    length (fst (wTh w)) = m -> length (snd (wTh w)) = n1 -> length (wrG w) = m -> length (wrT w) = n1 ->
    map (@gtval F zero add mul Pd kindD (LtW w)) (clsW w) = tvW w.
  Proof.
    intros w h1 h2 h3 h4. unfold clsW, LtW.
    rewrite (@layout_identityD F zero one add mul sub div opp inv Fdec Hf Pd tg n1 ell lo1 SO kd base a pp us dG dT
               (fst (wTh w)) (snd (wTh w)) (wrG w) (wrT w) h1 h2 h3 h4 dG_len dT_len).
    pose proof (@claimD F zero one add mul sub div opp inv Fdec Hf Pd n1 ell lo1 SO kd base pp offB us ts dG dT
                  (fst (wTh w)) (snd (wTh w)) (wrG w) (wrT w) h1 h2 h3 h4 dG_len dT_len) as eD.
    pose proof (@claimK F zero one add mul sub div opp inv Fdec Hf Pd n1 ell lo1 SO a b pp dG dT
                  (fst (wTh w)) (snd (wTh w)) (wrG w) (wrT w) h1 h2 h3 h4 dG_len dT_len) as eK.
    unfold tvW, DecSound.tvD. f_equal. f_equal.
    + unfold LD, VD. fold Dtab in eD. rewrite <-eD. field.
    + f_equal. unfold LK, VK. fold Ktab in eK. rewrite <-eK. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the rest of the protocol *)

  (* the prover's messages of the sumcheck layer *)
  Variable GGG : ThT -> F.
  Variables stratG zsG : ThT -> list F * list F -> list F -> list F.
  Variable GGT : P2 -> F.
  Variables stratT zsT : P2 -> list F * list F -> list F -> list F.
  Hypothesis HmsgG : forall p c4 pre, (length (stratG p c4 pre) <= S (degZ m base (length pre)))%nat.
  Hypothesis HmsgT : forall p c4 pre, (length (stratT p c4 pre) <= S (degZ n1 3 (length pre)))%nat.

  (* the prover's messages of the opening *)
  Variable muO : WD -> list F -> F.
  Variable ubO : WD -> list F -> @cgT F -> nat -> list F.
  Variables pvBO pvSO : WD -> list F -> @cgT F -> list F.

  Definition valsW (w : WD) : list F :=
    @valsD F zero one add mul sub opp inv Fdec dts stab etab phiR GGG stratG zsG GGT stratT zsT VD VK w.

  Local Notation OmD := (@OmD F lf n1 ell dts stab etab).
  Local Notation LenD := (@LenD F dts zsG zsT).

  (* slot masks and proximity masks: F-rows stored as two rows *)
  Definition mcbD (v : nat) : list (nat * F) :=
    match v with
    | 1 => [((kd * rwv)%nat, one); ((kd * rwv + 1)%nat, tg)]
    | 2 => [((kd * rwv + 2)%nat, one); ((kd * rwv + 3)%nat, tg)]
    | 3 => [((SO + 3)%nat, one); ((SO + 4)%nat, tg)]
    | 4 => [((SO + 5)%nat, one); ((SO + 6)%nat, tg)]
    | _ => [((SO + 7)%nat, one); ((SO + 8)%nat, tg)]
    end.
  Definition xmpB (j : nat) : F := add (X (kd * rwv + 4)%nat j) (mul tg (X (kd * rwv + 5)%nat j)).
  Definition xmpS (j : nat) : F := add (X (SO + 9)%nat j) (mul tg (X (SO + 10)%nat j)).

  (* the opening: challenges and acceptance *)
  Definition OT : Type := (list F * (@cgT F * jT))%type.
  Definition Oo : list OT :=
    list_prod (all_lists lf (kd + 6)) (list_prod (@OCG F lf rwsB rwsS) (OJ nb nqb ns nqs)).

  Definition AccOw (w : WD) (o : OT) : Prop :=
    @AccO F zero one add mul omB omS kb ks X rwsB rwsS xmpB xmpS (valsW w)
          (fun kp => @Lk F add mul kindD (LtW w) kp (clsW w))
          (fun kp => @cbk F one mul kindD (frowD SO) kp (clsW w))
          mcbD [1; 2]%nat [3; 4; 5]%nat (muO w) (ubO w) (pvBO w) (pvSO w) (fst o) (fst (snd o)) (snd (snd o)).

  Definition Bo : nat := @open_bound F lf nb eb nqb pnb ns es nqs pns rwsB rwsS (repeat zero (kd + 6)).

  Lemma open_bound_len : forall v v' : list F, length v = length v' ->
    @open_bound F lf nb eb nqb pnb ns es nqs pns rwsB rwsS v
    = @open_bound F lf nb eb nqb pnb ns es nqs pns rwsB rwsS v'.
  Proof. intros v v' h. unfold OpenSound.open_bound, OpenSound.OK. rewrite h. reflexivity. Qed.

  Lemma OmD_lengths : forall w : WD, In w OmD ->
    length (fst (wTh w)) = m /\ length (snd (wTh w)) = n1 /\ length (wrG w) = m /\ length (wrT w) = n1.
  Proof.
    intros [[[t1 t2] [cG rG]] [cT rT]] hin.
    unfold DecSound.OmD, DecSound.OP2, DecSound.OTh, DecSound.OmG, DecSound.OmT in hin.
    apply in_prod_iff in hin. destruct hin as [h2 hT].
    apply in_prod_iff in h2. destruct h2 as [hth hG].
    apply in_prod_iff in hth. destruct hth as [ht1 ht2].
    apply in_prod_iff in hG. destruct hG as [_ hrG].
    apply in_prod_iff in hT. destruct hT as [_ hrT].
    unfold ZeroTest.RZZ in hrG, hrT.
    apply all_lists_In in ht1. apply all_lists_In in ht2. apply all_lists_In in hrG. apply all_lists_In in hrT.
    cbn. tauto.
  Qed.

  Lemma in_rwsS : forall i, (SO <= i < SO + 9)%nat -> In i rwsS.
  Proof.
    intros i hi. unfold rwsS. apply in_map_iff. exists (i - SO)%nat. split; [lia | apply in_seq; lia].
  Qed.

  Lemma valsW_length : forall w, LenD w -> length (valsW w) = (kd + 6)%nat.
  Proof.
    intros w [h1 h2]. unfold valsW, DecSound.valsD. cbn [app length].
    rewrite !length_app, h1, h2, dts_len. cbn [length]. lia.
  Qed.

  (* the opening is sound for the kd + 6 claimed values *)
  Theorem Hopen_D : forall w, In w OmD -> LenD w -> valsW w <> tvW w -> card_le Oo (AccOw w) Bo.
  Proof.
    intros w hw hlen hne. destruct (OmD_lengths w hw) as (h1 & h2 & h3 & h4).
    assert (hne' : valsW w <> map (@gtval F zero add mul Pd kindD (LtW w)) (clsW w))
      by (rewrite (layout_tvD w h1 h2 h3 h4); exact hne).
    pose proof (valsW_length w hlen) as hvl.
    assert (T : forall cl t, In cl (clsW w) -> In t cl -> @term_ok F n1 ell lo1 SO kd t).
    { intros cl t hcl ht.
      exact (@claimsD_terms F zero one add mul sub opp tg n1 ell lo1 SO kd base a pp us dG dT
               (fst (wTh w)) (snd (wTh w)) (wrG w) (wrT w) h1 h2 h3 h4 dG_len dT_len cl t hcl ht). }
    assert (hvs : NoDup ([1; 2] ++ [3; 4; 5])%nat).
    { cbn. repeat constructor; cbn; intro h; repeat (destruct h as [h | h]; [discriminate |]); exact h. }
    assert (hcl : length (valsW w) = length (clsW w)).
    { rewrite hvl. unfold clsW. symmetry.
      exact (@claimsD_length F zero one add mul sub opp tg n1 ell lo1 SO kd base a pp us dG dT
               (fst (wTh w)) (snd (wTh w)) (wrG w) (wrT w) h1 h2 h3 h4 dG_len dT_len). }
    assert (hslots : forall cl, In cl (clsW w) -> forall t, In t cl -> In (tslot t) ([1; 2] ++ [3; 4; 5])%nat).
    { intros cl hc t ht. destruct (T cl t hc ht) as [[e _] | [[e _] | [[e _] | [[e _] | [e _]]]]]; rewrite e; cbn; tauto. }
    assert (hfunc : forall cl, In cl (clsW w) -> forall t, In t cl -> kindD (tslot t) = true ->
              trow t = frowD SO (tslot t)).
    { intros cl hc t ht hk.
      destruct (T cl t hc ht) as [[e _] | [[e _] | [[e er] | [[e er] | [e er]]]]];
        try (rewrite e in hk; cbn in hk; discriminate); rewrite e; exact er. }
    assert (hmul : forall d j, (d < kd)%nat -> (j < rwv)%nat -> (d * rwv + j < kd * rwv)%nat).
    { intros d j hd hj. pose proof (Nat.mul_le_mono_r (S d) kd rwv ltac:(lia)). lia. }
    assert (htB : forall cl, In cl (clsW w) -> forall t, In t cl -> In (tslot t) [1; 2]%nat -> In (trow t) rwsB).
    { intros cl hc t ht hin.
      destruct (T cl t hc ht) as [[e (d & j & hd & hj & er)] | [[e (d & j & hd & hj & er)] | [[e _] | [[e _] | [e _]]]]];
        try (rewrite e in hin; cbn in hin; destruct hin as [h | [h | []]]; discriminate).
      + rewrite er. unfold rwsB. apply in_seq. pose proof (hmul d j hd hj). lia.
      + rewrite er. unfold rwsB. apply in_seq. pose proof (hmul d j hd hj). lia. }
    assert (htS : forall cl, In cl (clsW w) -> forall t, In t cl -> In (tslot t) [3; 4; 5]%nat -> In (trow t) rwsS).
    { intros cl hc t ht hin.
      destruct (T cl t hc ht) as [[e _] | [[e _] | [[e er] | [[e er] | [e er]]]]];
        try (rewrite e in hin; cbn in hin; destruct hin as [h | [h | [h | []]]]; discriminate);
        rewrite er; apply in_rwsS; unfold DecLayout.rS, DecLayout.rE, DecLayout.rMd; lia. }
    assert (hfB : forall v, In v [1; 2]%nat -> kindD v = true -> In (frowD SO v) rwsB).
    { intros v hv hk. cbn in hv. destruct hv as [<- | [<- | []]]; cbn in hk; discriminate. }
    assert (hfS : forall v, In v [3; 4; 5]%nat -> kindD v = true -> In (frowD SO v) rwsS).
    { intros v hv _. cbn in hv. destruct hv as [<- | [<- | [<- | []]]]; apply in_rwsS;
        cbn; unfold DecLayout.rS, DecLayout.rE, DecLayout.rMd; lia. }
    assert (hmB : forall v, In v [1; 2]%nat -> forall i, In i (map fst (mcbD v)) -> In i rwsB).
    { intros v hv i hi. cbn in hv. destruct hv as [<- | [<- | []]]; cbn in hi;
        destruct hi as [<- | [<- | []]]; unfold rwsB; apply in_seq; lia. }
    assert (hmS : forall v, In v [3; 4; 5]%nat -> forall i, In i (map fst (mcbD v)) -> In i rwsS).
    { intros v hv i hi. cbn in hv. destruct hv as [<- | [<- | [<- | []]]]; cbn in hi;
        destruct hi as [<- | [<- | []]]; apply in_rwsS; lia. }
    assert (hdisj : forall i, In i rwsS -> ~ In i rwsB).
    { intros i hi hb. unfold rwsS in hi. apply in_map_iff in hi. destruct hi as (x & <- & _).
      unfold rwsB in hb. apply in_seq in hb. lia. }
    pose proof (@open_sound_claims F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall omB omS nb kb eb nqb pnb
                  ns ks es nqs pns HkB HkS HnodesB HnodesS HeB HeS ProxB ProxS X rwsB rwsS
                  xmpB xmpS hdisj kindD (LtW w) (frowD SO) mcbD [1; 2]%nat [3; 4; 5]%nat
                  (clsW w) (valsW w) hvs hcl hslots hfunc htB htS hfB hfS hmB hmS
                  (muO w) (ubO w) (pvBO w) (pvSO w) hne') as h.
    unfold OpenSound.OK in h. rewrite hvl in h.
    rewrite (open_bound_len (valsW w) (repeat zero (kd + 6))) in h by (rewrite hvl, repeat_length; reflexivity).
    exact h.
  Qed.

  (* Theorem 7.1 for the protocol of dec_derive. *)
  Theorem dec_theorem_7_1 :
    ~ @is_dec_witness F zero one add mul sub opp a b pp offB n1 ell base us ts dts stab etab phiR ->
    card_le (list_prod OmD Oo)
            (@RealAccD F zero one add mul Fdec dts stab etab GGG stratG zsG GGT stratT zsT OT AccOw)
            (@dec_bound F lf n1 ell base dts stab etab * length Oo + Bo * length OmD).
  Proof.
    intro hnw.
    assert (hOo : NoDup Oo).
    { unfold Oo, OpenSound.OCG, OpenSound.OG, OpenSound.OJ, OpenSound.QB, OpenSound.QS.
      repeat apply NoDup_list_prod; try (apply all_lists_NoDup; exact Hnd); try exact Hnd; apply qspace_NoDup. }
    assert (decO : forall x y : OT, {x = y} + {x <> y}).
    { unfold OT, OpenSound.cgT, OpenSound.jT. repeat decide equality. }
    exact (@dec_full F zero one add mul sub div opp inv Fdec Hf lf Hnd a b pp offB n1 ell base Hn1 us ts
             dts stab etab phiR HphiR Dtab Ktab
             (@HD_T F zero one add mul sub div opp inv Fdec Hf Pd n1 ell lo1 SO kd base pp offB us ts)
             (@HK_T F zero one add mul sub div opp inv Fdec Hf Pd n1 SO a b pp)
             avsG a0G GGG csG stratG zsG avsT a0T GGT csT stratT zsT
             HavsG_F HcsG_F HdegG_F HmsgG HavsT_F HcsT_F HdegT_F HmsgT
             VD VK LD LK HlinD_F HlinK_F OT Oo hOo decO AccOw Bo Hopen_D hnw).
  Qed.

End DecFinal.
