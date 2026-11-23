(* Knowledge soundness of the shuffle proof (paper, Theorem 5.2), for the
   protocol of mix_derive with the opening of pcs_open_verify, as an
   interactive oracle proof against an adaptive prover.

   Committed words. Xfix i is the committed word of row i for the rows of
   the first round (the big matrix, and sigma and the masks of the small
   matrix); Xlate c1 i is the word of a row of the second batch of the
   small matrix (u, uhat, the mask table), which the prover chooses after
   the first challenge c1. Rows of the small matrix are numbered from SO.

   Extractor. Every row is decoded by the decoder of its matrix
   (RsDecode.v). The tables W1, W2, W3 and sigma are read off the decoded
   rows of the first round (RowLayout.v, MixLayout.v); u, uhat and the mask
   table off the decoded rows after c1.

   Theorem mix_theorem_5_2. If the extracted (sigma, W) is not a witness
   of the shuffle relation with ternary re-randomisers, the challenge
   tuples for which the verifier accepts number at most

       mix_bound * |O| + open_bound * |Omega_mix|

   where Omega_mix are the challenge tuples of the sumcheck layer and O
   those of the opening. As fractions: (2 tau + 4 ell + 2 log N + 5 m + 7)/|F|
   for the sumcheck layer (mix_bound_fraction, mix_K_value), plus the five
   opening terms of open_bound.

   Assumed: a proximity lemma for each of the two row codes (ProxB,
   ProxS); for Delta = 3 it is rs_prox_affine, which rests on the line
   lemma. Everything else is a hypothesis on the shape of the instance or
   of the messages, which the verifier enforces. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Bgv Proximity ReedSolomon Opening MatQueries OpenSound RsDecode OpenSoundDec SlotKinds OpenClaims Sumcheck SumcheckMask SumcheckSound MaskedExt CubeIndex MixMultiset MixSummands MixIdentities MixSoundA MixSoundB MixSoundC MixBridge MixSound ZkSumcheck LayoutLemmas RowLayout MixLayout.
Import ListNotations.

Section MixFinal.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Notation nF := (@nF F zero one add).
  Local Notation pw := (@pw F one mul).
  Local Notation pi := (@pi F zero add mul).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation pt := (@pt F zero one).
  Local Notation ctx := (@ctx F).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  (* the instance *)
  Variables (a b : list F) (pp : F).
  Variables n1 ell : nat.
  Hypothesis Hell : (1 <= ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Hypothesis Hchar : forall k, (0 < k <= tau)%nat -> nF k <> zero.
  Hypothesis HN : nF N <> zero.
  Variables cin cout : nat -> ctx.
  Hypothesis Hci : forall i, (i < tau)%nat -> length (fst (cin i)) = N /\ length (snd (cin i)) = N.
  Hypothesis Hco : forall j, (j < tau)%nat -> length (fst (cout j)) = N /\ length (snd (cout j)) = N.

  (* the layout *)
  Variable tg : F.
  Variables lo1 lo2 SO : nat.
  Local Notation rwv := (MixLayout.rw n1 ell lo1).
  Local Notation rsv := (MixLayout.rs ell lo2).
  Hypothesis HSO : (3 * rwv + 6 <= SO)%nat.

  Definition invN : F := inv (nF N).
  Definition dA : list nat := map (degA ell) (seq 0 ell).
  Definition dB : list nat := map degB (seq 0 n1).
  Definition dC : list nat := map (degC m) (seq 0 m).

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

  Variable Xfix : nat -> nat -> F.
  Variable Xlate : list F -> nat -> nat -> F.

  Definition lateb (i : nat) : bool := Nat.leb (SO + rsv + 6) i.
  Definition Xc (c1 : list F) (i : nat) : nat -> F := if lateb i then Xlate c1 i else Xfix i.

  Definition rwsB : list nat := seq 0 (3 * rwv + 4).
  Definition rwsS : list nat := map (fun i => (SO + i)%nat) (seq 0 (rsv + 4) ++ seq (rsv + 6) (4 * rsv + 1)).

  Definition Pd (c1 : list F) : nat -> list F :=
    @Pdec F zero one add mul Fdec lf omB omS nb kb eb ns ks es (Xc c1) rwsB.

  Lemma Pd_fixed : forall c1 c1' i, lateb i = false -> Pd c1 i = Pd c1' i.
  Proof.
    intros c1 c1' i h. unfold Pd, OpenSoundDec.Pdec, Xc. rewrite h. reflexivity.
  Qed.

  (* the tables of the first round do not depend on the first challenge *)
  Lemma tab_fixed : forall c1 c1' start M lo bq,
    length bq = M -> (start + 2 ^ hiE M lo <= SO + rsv + 6)%nat ->
    @rdtab F zero one Fdec (Pd c1) start M lo bq = @rdtab F zero one Fdec (Pd c1') start M lo bq.
  Proof.
    intros c1 c1' start M lo bq hb hs.
    rewrite (@rdtab_rows F zero one Fdec (Pd c1) (Pd c1') start M lo bq hb); [reflexivity |].
    intros i hi. apply Pd_fixed. unfold lateb. apply Nat.leb_gt. lia.
  Qed.

  Definition c0 : list F := [].

  (* the extracted tables *)
  Definition W1 : list F -> F := @W1T F zero one Fdec (Pd c0) n1 ell lo1.
  Definition W2 : list F -> F := @W2T F zero one Fdec (Pd c0) n1 ell lo1.
  Definition W3 : list F -> F := @W3T F zero one Fdec (Pd c0) n1 ell lo1.
  Definition sg : list F -> F := @sgT F zero one Fdec (Pd c0) ell lo2 SO.

  Lemma W_fixed : forall c1 bq, In bq (cube m) ->
    @W1T F zero one Fdec (Pd c1) n1 ell lo1 bq = W1 bq /\
    @W2T F zero one Fdec (Pd c1) n1 ell lo1 bq = W2 bq /\
    @W3T F zero one Fdec (Pd c1) n1 ell lo1 bq = W3 bq.
  Proof.
    intros c1 bq hb. pose proof (@cube_length F zero one m bq hb) as hl.
    unfold W1, W2, W3, MixLayout.W1T, MixLayout.W2T, MixLayout.W3T, MixLayout.rW.
    repeat split; apply tab_fixed; try exact hl; fold rwv; lia.
  Qed.

  Lemma sg_fixed : forall c1 bq, In bq (cube ell) ->
    @sgT F zero one Fdec (Pd c1) ell lo2 SO bq = sg bq.
  Proof.
    intros c1 bq hb. pose proof (@cube_length F zero one ell bq hb) as hl.
    unfold sg, MixLayout.sgT, MixLayout.rSg. apply tab_fixed; [exact hl |]. fold rsv. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* what the prover committed after the first challenge *)

  Definition uF (c1 : list F) : list F -> F := @uT F zero one add mul Fdec (Pd c1) tg ell lo2 SO.
  Definition uhF (c1 : list F) : list F -> F := @uhT F zero one add mul Fdec (Pd c1) tg ell lo2 SO.
  Definition auF (c1 : list F) : F := @auT F zero add mul (Pd c1) tg ell lo2 SO.
  Definition auhF (c1 : list F) : F := @auhT F zero add mul (Pd c1) tg ell lo2 SO.
  Definition asgF (c1 : list F) : F := @asgT F zero add mul (Pd c1) tg ell lo2 SO.
  Definition ahF (c1 : list F) : F := @ahT F zero add mul (Pd c1) tg ell lo2 SO.
  Definition aw1F (c1 : list F) : F := @aw1T F zero add mul (Pd c1) tg ell lo2 SO.
  Definition aw2F (c1 : list F) : F := @aw2T F zero add mul (Pd c1) tg ell lo2 SO.
  Definition aw3F (c1 : list F) : F := @aw3T F zero add mul (Pd c1) tg ell lo2 SO.
  Definition a0AF (c1 : list F) : F := @a0AT F zero add mul (Pd c1) tg ell lo2 SO.
  Definition csAF (c1 : list F) : list (list F) := @csAT F zero add mul (Pd c1) tg ell lo2 SO dA.
  Definition a0BF (c1 : list F) : F := @a0BT F zero add mul (Pd c1) tg ell lo2 SO dA.
  Definition csBF (c1 : list F) : list (list F) := @csBT F zero add mul (Pd c1) tg ell lo2 SO dA dB.
  Definition a0CF (c1 : list F) : F := @a0CT F zero add mul (Pd c1) tg ell lo2 SO dA dB.
  Definition csCF (c1 : list F) : list (list F) := @csCT F zero add mul (Pd c1) tg ell lo2 SO dA dB dC.

  Lemma nth_map_seq : forall (f : nat -> nat) (n i : nat), (i < n)%nat -> nth i (map f (seq 0 n)) 0%nat = f i.
  Proof.
    intros f n i hi.
    rewrite (nth_indep _ 0%nat (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth f (seq 0 n) 0%nat i), seq_nth by exact hi. reflexivity.
  Qed.

  Lemma mask_shape : forall (Pm : list F) (off : nat) (degs : list nat),
    length (@maskCs F zero add mul tg Pm off degs) = length degs /\
    forall i, (i < length degs)%nat ->
      length (nth i (@maskCs F zero add mul tg Pm off degs) []) = nth i degs 0%nat.
  Proof.
    intros Pm off degs. unfold RowLayout.maskCs. split.
    + apply (@chunks_length F).
    + apply (@shaped_nth F). apply (@chunks_shaped F). rewrite length_map, length_seq. lia.
  Qed.

  Lemma dA_len : length dA = ell. Proof. unfold dA. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma dB_len : length dB = n1. Proof. unfold dB. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma dC_len : length dC = m. Proof. unfold dC. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma HcsA_F : forall c1, length (csAF c1) = ell.
  Proof. intro c1. unfold csAF, MixLayout.csAT. rewrite (proj1 (mask_shape _ _ _)). apply dA_len. Qed.
  Lemma HdegA_F : forall c1 i, (i < ell)%nat -> (length (nth i (csAF c1) []) <= degA ell i)%nat.
  Proof.
    intros c1 i hi. unfold csAF, MixLayout.csAT.
    rewrite (proj2 (mask_shape _ _ _)) by (rewrite dA_len; exact hi).
    unfold dA. rewrite nth_map_seq by exact hi. lia.
  Qed.
  Lemma HcsB_F : forall c1, length (csBF c1) = n1.
  Proof. intro c1. unfold csBF, MixLayout.csBT. rewrite (proj1 (mask_shape _ _ _)). apply dB_len. Qed.
  Lemma HdegB_F : forall c1 i, (i < n1)%nat -> (length (nth i (csBF c1) []) <= 2)%nat.
  Proof.
    intros c1 i hi. unfold csBF, MixLayout.csBT.
    rewrite (proj2 (mask_shape _ _ _)) by (rewrite dB_len; exact hi).
    unfold dB. rewrite nth_map_seq by exact hi. unfold degB. lia.
  Qed.
  Lemma HcsC_F : forall c1, length (csCF c1) = m.
  Proof. intro c1. unfold csCF, MixLayout.csCT. rewrite (proj1 (mask_shape _ _ _)). apply dC_len. Qed.
  Lemma HdegC_F : forall c1 i, (i < m)%nat -> (length (nth i (csCF c1) []) <= degC m i)%nat.
  Proof.
    intros c1 i hi. unfold csCF, MixLayout.csCT.
    rewrite (proj2 (mask_shape _ _ _)) by (rewrite dC_len; exact hi).
    unfold dC. rewrite nth_map_seq by exact hi. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the verifier's tables *)

  Variables rp1T rp2T rp3T zpT zhT : list F -> list F -> F.
  Variables alT beT : list F -> F.

  Local Notation Wm := (@Wm F).
  Local Notation w1 := (@w1 F).
  Local Notation wA := (@wA F).
  Local Notation wB := (@wB F).
  Local Notation wY := (@wY F).
  Local Notation wZ := (@wZ F).

  Definition clsW (w : Wm) : list (list (@gterm F)) :=
    @claims9 F zero one add mul sub tg invN n1 ell lo1 lo2 SO dA dB dC (wA w) (wY w) (wZ w) (wB w)
             (rp1T (w1 w)) (rp2T (w1 w)) (rp3T (w1 w)).

  Definition LtW (w : Wm) : nat -> list F := @LtM F zero one add mul sub n1 ell lo1 lo2 (wA w) (wY w) (wZ w).

  Definition tvW (w : Wm) : list F :=
    @tvI F zero one add mul sub inv n1 ell W1 W2 W3 sg rp1T rp2T rp3T uF uhF auF auhF asgF ahF aw1F aw2F aw3F
         a0AF a0BF a0CF csAF csBF csCF w.

  Lemma mstar_ext : forall k (T T' : list F -> F) (av : F) (x : list F),
    (forall bq, In bq (cube k) -> T bq = T' bq) -> mstar k T av x = mstar k T' av x.
  Proof.
    intros k T T' av x h. unfold MaskedExt.mstar. rewrite (@mle_ext F zero one add mul sub k T T' x h). reflexivity.
  Qed.

  Lemma cons_eq : forall (x x' : F) (l l' : list F), x = x' -> l = l' -> x :: l = x' :: l'.
  Proof. intros; subst; reflexivity. Qed.

  (* the layout identity, for the extracted tables *)
  Theorem layout_tv : forall w : Wm,
    length (wA w) = ell -> length (wY w) = n1 -> length (wZ w) = m ->
    map (@gtval F zero add mul (Pd (w1 w)) kindM (LtW w)) (clsW w) = tvW w.
  Proof.
    intros w hA hY hZ. unfold clsW, LtW.
    rewrite (@layout_identity F zero one add mul sub div opp inv Fdec Hf (Pd (w1 w)) tg invN n1 ell lo1 lo2 SO
               dA dB dC (wA w) (wY w) (wZ w) (wB w) (rp1T (w1 w)) (rp2T (w1 w)) (rp3T (w1 w))
               hA hY hZ dA_len dB_len dC_len).
    unfold tvW, MixSound.tvI.
    apply cons_eq; [reflexivity |]. apply cons_eq; [reflexivity |].
    apply cons_eq; [apply mstar_ext; intros bq hb; apply sg_fixed; exact hb |].
    apply cons_eq.
    { unfold MixSummands.gB.
      rewrite (@mle_ext F zero one add mul sub m _ W1 _ (fun bq hb => proj1 (W_fixed (w1 w) bq hb))).
      rewrite (@mle_ext F zero one add mul sub m _ W2 _ (fun bq hb => proj1 (proj2 (W_fixed (w1 w) bq hb)))).
      rewrite (@mle_ext F zero one add mul sub m _ W3 _ (fun bq hb => proj2 (proj2 (W_fixed (w1 w) bq hb)))).
      reflexivity. }
    apply cons_eq; [apply mstar_ext; intros bq hb; exact (proj1 (W_fixed (w1 w) bq hb)) |].
    apply cons_eq; [apply mstar_ext; intros bq hb; exact (proj1 (proj2 (W_fixed (w1 w) bq hb))) |].
    apply cons_eq; [apply mstar_ext; intros bq hb; exact (proj2 (proj2 (W_fixed (w1 w) bq hb))) |].
    reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the rest of the protocol *)

  Hypothesis Hver : forall c1, In c1 (@MixSoundA.C1 F lf N) ->
    exists ru rv, length ru = N /\ length rv = N /\
      c1 = @point F ru rv (alT c1) (beT c1) /\
      (forall y, (y < N)%nat -> rp1T c1 (pt n1 y) = nth y (@rho_r F add mul opp a b ru rv) zero) /\
      (forall y, (y < N)%nat -> rp2T c1 (pt n1 y) = nth y (@rho_e1 F mul pp ru) zero) /\
      (forall y, (y < N)%nat -> rp3T c1 (pt n1 y) = nth y (@rho_e2 F mul pp rv) zero) /\
      (forall i, (i < tau)%nat -> zpT c1 (pt ell i) = @proj F zero add mul ru rv (cin i)) /\
      (forall j, (j < tau)%nat -> zhT c1 (pt ell j) = @proj F zero add mul ru rv (cout j)).

  (* the prover's messages of the sumcheck layer *)
  Variables GA GB GC : list F -> F.
  Variable stratA : list F -> list F * list F -> list F -> list F.
  Variables eU eUh eS eH : list F -> list F * list F -> list F -> F.
  Variable stratB : @P3 F -> F -> list F -> list F.
  Variable stratC : @P5 F -> list F * list F -> list F -> list F.
  Variables wz1 wz2 wz3 : @P5 F -> list F * list F -> list F -> F.
  Hypothesis HmsgA : forall c1 c2 pre, (length (stratA c1 c2 pre) <= S (degA ell (length pre)))%nat.
  Hypothesis HmsgB : forall p rB pre, (length (stratB p rB pre) <= S (degB (length pre)))%nat.
  Hypothesis HmsgC : forall p c4 pre, (length (stratC p c4 pre) <= S (degC m (length pre)))%nat.

  (* the prover's messages of the opening *)
  Variable muO : Wm -> list F -> F.
  Variable ubO : Wm -> list F -> @cgT F -> nat -> list F.
  Variables pvBO pvSO : Wm -> list F -> @cgT F -> list F.

  Definition valsW (w : Wm) : list F :=
    @vals9 F zero one add mul sub inv Fdec ell zpT zhT alT beT GA GB GC stratA eU eUh eS eH stratB stratC
           wz1 wz2 wz3 w.

  (* slot masks and proximity masks: F-rows stored as two rows *)
  Definition mcbM (v : nat) : list (nat * F) :=
    match v with
    | 1 => [((3 * rwv)%nat, one); ((3 * rwv + 1)%nat, tg)]
    | 2 => [((3 * rwv + 2)%nat, one); ((3 * rwv + 3)%nat, tg)]
    | 3 => [((SO + rsv)%nat, one); ((SO + rsv + 1)%nat, tg)]
    | _ => [((SO + rsv + 2)%nat, one); ((SO + rsv + 3)%nat, tg)]
    end.
  Definition xmpB (c1 : list F) (j : nat) : F :=
    add (Xc c1 (3 * rwv + 4)%nat j) (mul tg (Xc c1 (3 * rwv + 5)%nat j)).
  Definition xmpS (c1 : list F) (j : nat) : F :=
    add (Xc c1 (SO + rsv + 4)%nat j) (mul tg (Xc c1 (SO + rsv + 5)%nat j)).

  (* the opening: challenges and acceptance *)
  Definition OT : Type := (list F * (@cgT F * jT))%type.
  Definition Oo : list OT :=
    list_prod (all_lists lf 9) (list_prod (@OCG F lf rwsB rwsS) (OJ nb nqb ns nqs)).

  Definition AccOw (w : Wm) (o : OT) : Prop :=
    @AccO F zero one add mul omB omS kb ks (Xc (w1 w)) rwsB rwsS (xmpB (w1 w)) (xmpS (w1 w)) (valsW w)
          (fun kp => @Lk F add mul kindM (LtW w) kp (clsW w))
          (fun kp => @cbk F one mul kindM (frowM ell lo2 SO) kp (clsW w))
          mcbM [1; 2]%nat [3; 4]%nat (muO w) (ubO w) (pvBO w) (pvSO w) (fst o) (fst (snd o)) (snd (snd o)).

  Definition Bo : nat := @open_bound F lf nb eb nqb pnb ns es nqs pns rwsB rwsS (repeat zero 9).

  Lemma Om_lengths : forall w : Wm, In w (@Om F lf n1 ell) ->
    length (wA w) = ell /\ length (wY w) = n1 /\ length (wZ w) = m.
  Proof.
    intros [[[c1 [c2 rA]] [rB ry]] [c4 rz]] hin.
    unfold MixSound.Om, MixSound.OP5, MixSound.OP3 in hin.
    apply in_prod_iff in hin. destruct hin as [h5 hcz].
    apply in_prod_iff in h5. destruct h5 as [h3 hby].
    apply in_prod_iff in h3. destruct h3 as [_ h3]. apply in_prod_iff in h3. destruct h3 as [_ hA].
    apply in_prod_iff in hby. destruct hby as [_ hY].
    apply in_prod_iff in hcz. destruct hcz as [_ hZ].
    unfold MixSoundA.RA in hA. unfold MixSoundC.RZ in hZ.
    apply all_lists_In in hA. apply all_lists_In in hY. apply all_lists_In in hZ.
    cbn. tauto.
  Qed.

  Lemma in_rwsS : forall x, (x < rsv + 4 \/ rsv + 6 <= x < rsv + 6 + (4 * rsv + 1))%nat -> In (SO + x)%nat rwsS.
  Proof.
    intros x hx. unfold rwsS. apply (in_map (fun i => (SO + i)%nat)). apply in_or_app.
    destruct hx as [hx | hx]; [left | right]; apply in_seq; lia.
  Qed.

  (* the opening is sound for the nine claimed values *)
  Theorem Hopen_F : forall w, In w (@Om F lf n1 ell) -> valsW w <> tvW w -> card_le Oo (AccOw w) Bo.
  Proof.
    intros w hw hne. destruct (Om_lengths w hw) as (hA & hY & hZ).
    assert (hne' : valsW w <> map (@gtval F zero add mul (Pd (w1 w)) kindM (LtW w)) (clsW w))
      by (rewrite (layout_tv w hA hY hZ); exact hne).
    assert (T : forall cl t, In cl (clsW w) -> In t cl ->
              (tslot t = 1%nat /\ exists k j, (k < 3)%nat /\ (j < rwv)%nat /\ trow t = (k * rwv + j)%nat)
              \/ (tslot t = 2%nat /\ exists k j, (k < 3)%nat /\ (j < rwv)%nat /\ trow t = (k * rwv + j)%nat)
              \/ (tslot t = 3%nat /\ exists j, (j < rsv)%nat /\
                    (trow t = (SO + j)%nat \/ exists a0, (a0 < 4)%nat /\ trow t = (SO + (rsv + 6) + a0 * rsv + j)%nat))
              \/ (tslot t = 4%nat /\ trow t = MixLayout.rM ell lo2 SO)).
    { intros cl t hcl ht. exact (@claims9_terms F zero one add mul sub tg invN n1 ell lo1 lo2 SO dA dB dC
                                   (wA w) (wY w) (wZ w) (wB w) (rp1T (w1 w)) (rp2T (w1 w)) (rp3T (w1 w))
                                   hA hY hZ dA_len dB_len dC_len cl t hcl ht). }
    assert (hrM : In (MixLayout.rM ell lo2 SO) rwsS).
    { unfold MixLayout.rM. replace (SO + (rsv + 6) + 4 * rsv)%nat with (SO + (rsv + 6 + 4 * rsv))%nat by lia.
      apply in_rwsS. lia. }
    assert (hvs : NoDup ([1; 2] ++ [3; 4])%nat).
    { cbn. repeat constructor; cbn; intro h; repeat (destruct h as [h | h]; [discriminate |]); exact h. }
    assert (hslots : forall cl, In cl (clsW w) -> forall t, In t cl -> In (tslot t) ([1; 2] ++ [3; 4])%nat).
    { intros cl hcl t ht. destruct (T cl t hcl ht) as [[e _] | [[e _] | [[e _] | [e _]]]]; rewrite e; cbn; tauto. }
    assert (hfunc : forall cl, In cl (clsW w) -> forall t, In t cl -> kindM (tslot t) = true ->
              trow t = frowM ell lo2 SO (tslot t)).
    { intros cl hcl t ht hk. destruct (T cl t hcl ht) as [[e _] | [[e _] | [[e _] | [e er]]]];
        try (rewrite e in hk; cbn in hk; discriminate). unfold MixLayout.frowM. exact er. }
    assert (htB : forall cl, In cl (clsW w) -> forall t, In t cl -> In (tslot t) [1; 2]%nat -> In (trow t) rwsB).
    { intros cl hcl t ht hin.
      destruct (T cl t hcl ht) as [[e (k & j & hk & hj & er)] | [[e (k & j & hk & hj & er)] | [[e _] | [e _]]]].
      + rewrite er. unfold rwsB. apply in_seq. nia.
      + rewrite er. unfold rwsB. apply in_seq. nia.
      + rewrite e in hin. cbn in hin. destruct hin as [h | [h | []]]; discriminate.
      + rewrite e in hin. cbn in hin. destruct hin as [h | [h | []]]; discriminate. }
    assert (htS : forall cl, In cl (clsW w) -> forall t, In t cl -> In (tslot t) [3; 4]%nat -> In (trow t) rwsS).
    { intros cl hcl t ht hin.
      destruct (T cl t hcl ht) as [[e _] | [[e _] | [[e (j & hj & er)] | [e er]]]].
      + rewrite e in hin. cbn in hin. destruct hin as [h | [h | []]]; discriminate.
      + rewrite e in hin. cbn in hin. destruct hin as [h | [h | []]]; discriminate.
      + destruct er as [er | (a0 & ha0 & er)]; rewrite er.
        - apply in_rwsS. lia.
        - replace (SO + (rsv + 6) + a0 * rsv + j)%nat with (SO + (rsv + 6 + a0 * rsv + j))%nat by lia.
          apply in_rwsS. right. nia.
      + rewrite er. exact hrM. }
    assert (hfB : forall v, In v [1; 2]%nat -> kindM v = true -> In (frowM ell lo2 SO v) rwsB).
    { intros v hv hk. cbn in hv. destruct hv as [<- | [<- | []]]; cbn in hk; discriminate. }
    assert (hfS : forall v, In v [3; 4]%nat -> kindM v = true -> In (frowM ell lo2 SO v) rwsS).
    { intros v _ _. unfold MixLayout.frowM. exact hrM. }
    assert (hmB : forall v, In v [1; 2]%nat -> forall i, In i (map fst (mcbM v)) -> In i rwsB).
    { intros v hv i hi. cbn in hv. destruct hv as [<- | [<- | []]]; cbn in hi;
        destruct hi as [<- | [<- | []]]; unfold rwsB; apply in_seq; lia. }
    assert (hmS : forall v, In v [3; 4]%nat -> forall i, In i (map fst (mcbM v)) -> In i rwsS).
    { intros v hv i hi. cbn in hv. destruct hv as [<- | [<- | []]]; cbn in hi; destruct hi as [<- | [<- | []]].
      + apply in_rwsS. lia.
      + replace (SO + rsv + 1)%nat with (SO + (rsv + 1))%nat by lia. apply in_rwsS. lia.
      + replace (SO + rsv + 2)%nat with (SO + (rsv + 2))%nat by lia. apply in_rwsS. lia.
      + replace (SO + rsv + 3)%nat with (SO + (rsv + 3))%nat by lia. apply in_rwsS. lia. }
    assert (hdisj : forall i, In i rwsS -> ~ In i rwsB).
    { intros i hi hb. unfold rwsS in hi. apply in_map_iff in hi. destruct hi as (x & <- & _).
      unfold rwsB in hb. apply in_seq in hb. lia. }
    exact (@open_sound_claims F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall omB omS nb kb eb nqb pnb
             ns ks es nqs pns HkB HkS HnodesB HnodesS HeB HeS ProxB ProxS (Xc (w1 w)) rwsB rwsS
             (xmpB (w1 w)) (xmpS (w1 w)) hdisj kindM (LtW w) (frowM ell lo2 SO) mcbM [1; 2]%nat [3; 4]%nat
             (clsW w) (valsW w) hvs eq_refl hslots hfunc htB htS hfB hfS hmB hmS
             (muO w) (ubO w) (pvBO w) (pvSO w) hne').
  Qed.

  Lemma rr_len : forall (T1 T2 T3 : list F -> F) i, (i < tau)%nat ->
    length (fst (@rrW F zero one add mul opp a b pp n1 ell cin T1 T2 T3 i)) = N /\
    length (snd (@rrW F zero one add mul opp a b pp n1 ell cin T1 T2 T3 i)) = N.
  Proof.
    intros T1 T2 T3 i hi. destruct (Hci i hi) as [h1 h2].
    assert (hn : forall aa rr0 : list F, length rr0 = N -> (length (@nmul F zero add mul opp aa rr0) <= N)%nat).
    { intros aa rr0 hl. destruct aa as [| a0 aa']; [cbn; lia |].
      rewrite (@nmul_length F zero add mul opp (a0 :: aa') rr0 ltac:(discriminate)). lia. }
    unfold MixBridge.rrW, Bgv.cadd, Bgv.enc0. cbn [fst snd].
    rewrite !(@length_padd F add), !(@length_pscale F mul).
    assert (hw1 : length (@wr F zero one n1 ell T1 i) = N) by (unfold MixBridge.wr; rewrite length_map, length_seq; reflexivity).
    assert (hw2 : length (@we1 F zero one n1 ell T2 i) = N) by (unfold MixBridge.we1; rewrite length_map, length_seq; reflexivity).
    assert (hw3 : length (@we2 F zero one n1 ell T3 i) = N) by (unfold MixBridge.we2; rewrite length_map, length_seq; reflexivity).
    pose proof (hn a _ hw1). pose proof (hn b _ hw1). rewrite hw2, hw3, h1, h2. lia.
  Qed.

  (* Theorem 5.2 for the protocol of mix_derive. *)
  Theorem mix_theorem_5_2 :
    ~ @is_witness F zero one add mul opp a b pp n1 ell cin cout W1 W2 W3 sg ->
    card_le (list_prod (@Om F lf n1 ell) Oo)
            (@RealAcc F zero one add mul sub Fdec ell zpT alT beT GA GB GC stratA eH stratB stratC OT AccOw)
            (@mix_bound F lf n1 ell * length Oo + Bo * length (@Om F lf n1 ell)).
  Proof.
    intro hnw.
    assert (hOo : NoDup Oo).
    { unfold Oo, OpenSound.OCG, OpenSound.OG, OpenSound.OJ, OpenSound.QB, OpenSound.QS.
      repeat apply NoDup_list_prod; try (apply all_lists_NoDup; exact Hnd); try exact Hnd; apply qspace_NoDup. }
    assert (decO : forall x y : OT, {x = y} + {x <> y}).
    { unfold OT, OpenSound.cgT, OpenSound.jT. repeat decide equality. }
    exact (@mix_full F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall a b pp n1 ell Hell Hchar HN cin cout
             W1 W2 W3 sg (rr_len W1 W2 W3) Hco rp1T rp2T rp3T zpT zhT alT beT Hver
             uF uhF auF auhF asgF ahF aw1F aw2F aw3F a0AF a0BF a0CF GA GB GC csAF csBF csCF
             stratA eU eUh eS eH stratB stratC wz1 wz2 wz3
             HcsA_F HdegA_F HmsgA HcsB_F HdegB_F HmsgB HcsC_F HdegC_F HmsgC
             OT Oo hOo decO AccOw Bo Hopen_F hnw).
  Qed.

End MixFinal.
