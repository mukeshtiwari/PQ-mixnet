(* The opening theorem for a list of claims, as the verifier compiles them
   (fp_core.py: pcs_open_verify with _slots_compile).

   open_sound_claims combines open_sound_dec (soundness of the opening for
   the decoded rows) with batch_mixed (the batching identity for tensor and
   func slots): if the claimed values vals are not the values gtval of the
   claims on the decoded rows, the verifier accepts for at most open_bound
   challenges.

   The side conditions are stated on the claims themselves: every term
   lies in a known slot; a term of a func slot is on the row of that slot;
   the rows of a slot of the big (small) matrix, and its mask rows, are
   rows of the big (small) matrix. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Proximity ReedSolomon Opening MatQueries OpenSound RsDecode OpenSoundDec SlotKinds.
Import ListNotations.

Section OpenClaims.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Local Notation pw := (@pw F one mul).
  Local Notation pi := (@pi F zero add mul).
  Local Notation gterm := (@gterm F).
  Local Notation gsel := (@gsel F mul).
  Local Notation gbatch := (@gbatch F mul).
  Local Notation cbk := (@cbk F one mul).
  Local Notation Lk := (@Lk F add mul).
  Local Notation gtval := (@gtval F zero add mul).

  (* the rows that a compiled slot uses *)
  Lemma gsel_rows : forall k0 (cl : list gterm) v i, In i (map fst (gsel k0 cl v)) ->
    exists t, In t cl /\ tslot t = v /\ trow t = i.
  Proof.
    intros k0; induction cl as [| t cl ih]; intros v i h; [contradiction |].
    cbn [SlotKinds.gsel] in h. destruct (Nat.eqb (tslot t) v) eqn:e.
    + cbn in h. destruct h as [<- | h].
      - exists t; split; [left; reflexivity | split; [apply Nat.eqb_eq; exact e | reflexivity]].
      - destruct (ih v i h) as (t' & ht & hr). exists t'; split; [right; exact ht | exact hr].
    + destruct (ih v i h) as (t' & ht & hr). exists t'; split; [right; exact ht | exact hr].
  Qed.

  Lemma gbatch_rows : forall (cls : list (list gterm)) kp v i, In i (map fst (gbatch kp cls v)) ->
    exists cl t, In cl cls /\ In t cl /\ tslot t = v /\ trow t = i.
  Proof.
    induction cls as [| cl cls ih]; intros kp v i h; destruct kp as [| k0 kp]; cbn [SlotKinds.gbatch] in h;
      try contradiction.
    rewrite map_app in h. apply in_app_or in h. destruct h as [h | h].
    + destruct (gsel_rows k0 cl v i h) as (t & ht & hr). exists cl, t; split; [left; reflexivity | tauto].
    + destruct (ih kp v i h) as (cl' & t & hcl & ht). exists cl', t; split; [right; exact hcl | exact ht].
  Qed.

  Lemma cbk_rows : forall (kind : nat -> bool) (frow : nat -> nat) (cls : list (list gterm)) kp v i,
    In i (map fst (cbk kind frow kp cls v)) ->
    (kind v = true /\ i = frow v) \/ (exists cl t, In cl cls /\ In t cl /\ tslot t = v /\ trow t = i).
  Proof.
    intros kind frow cls kp v i h. unfold SlotKinds.cbk in h. destruct (kind v) eqn:ek.
    + left. cbn in h. destruct h as [<- | []]. split; reflexivity.
    + right. apply (gbatch_rows cls kp v i h).
  Qed.

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

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

  Hypothesis ProxB : forall (m : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close nb eb codeB (pi m rows g)) ->
    (pnb * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= eb)%nat /\ codeB cm /\ agree_out nb E m cm /\
      Forall2 (fun r c => codeB c /\ agree_out nb E r c) rows cs.
  Hypothesis ProxS : forall (m : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close ns es codeS (pi m rows g)) ->
    (pns * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= es)%nat /\ codeS cm /\ agree_out ns E m cm /\
      Forall2 (fun r c => codeS c /\ agree_out ns E r c) rows cs.

  Variable X : nat -> nat -> F.
  Variables rwsB rwsS : list nat.
  Variables xmpB xmpS : nat -> F.
  Hypothesis Hdisj : forall i, In i rwsS -> ~ In i rwsB.

  Local Notation Pd := (@Pdec F zero one add mul Fdec lf omB omS nb kb eb ns ks es X rwsB).

  (* the claims *)
  Variable kind : nat -> bool.
  Variable Lt : nat -> list F.
  Variable frow : nat -> nat.
  Variable mcb : nat -> list (nat * F).
  Variables svB svS : list nat.
  Variable cls : list (list gterm).
  Variable vals : list F.

  Hypothesis Hvs : NoDup (svB ++ svS).
  Hypothesis Hlen : length vals = length cls.
  Hypothesis Hslots : forall cl, In cl cls -> forall t, In t cl -> In (tslot t) (svB ++ svS).
  Hypothesis Hfunc : forall cl, In cl cls -> forall t, In t cl -> kind (tslot t) = true -> trow t = frow (tslot t).
  Hypothesis HtB : forall cl, In cl cls -> forall t, In t cl -> In (tslot t) svB -> In (trow t) rwsB.
  Hypothesis HtS : forall cl, In cl cls -> forall t, In t cl -> In (tslot t) svS -> In (trow t) rwsS.
  Hypothesis HfB : forall v, In v svB -> kind v = true -> In (frow v) rwsB.
  Hypothesis HfS : forall v, In v svS -> kind v = true -> In (frow v) rwsS.
  Hypothesis HmB : forall v, In v svB -> forall i, In i (map fst (mcb v)) -> In i rwsB.
  Hypothesis HmS : forall v, In v svS -> forall i, In i (map fst (mcb v)) -> In i rwsS.

  Variable mu : list F -> F.
  Variable ub : list F -> @cgT F -> nat -> list F.
  Variables pvB pvS : list F -> @cgT F -> list F.

  Theorem open_sound_claims :
    vals <> map (gtval Pd kind Lt) cls ->
    card_le (list_prod (@OK F lf vals) (list_prod (@OCG F lf rwsB rwsS) (OJ nb nqb ns nqs)))
            (fun w => @AccO F zero one add mul omB omS kb ks X rwsB rwsS xmpB xmpS vals
                        (fun kp => Lk kind Lt kp cls) (fun kp => cbk kind frow kp cls) mcb svB svS
                        mu ub pvB pvS (fst w) (fst (snd w)) (snd (snd w)))
            (@open_bound F lf nb eb nqb pnb ns es nqs pns rwsB rwsS vals).
  Proof.
    apply (@open_sound_dec F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall omB omS nb kb eb nqb pnb ns ks es nqs pns
             HkB HkS HnodesB HnodesS HeB HeS ProxB ProxS X rwsB rwsS xmpB xmpS Hdisj vals
             (map (gtval Pd kind Lt) cls)).
    + rewrite length_map. exact Hlen.
    + intros kp hkp. apply all_lists_In in hkp. destruct hkp as [hl _].
      apply (@batch_mixed F zero one add mul sub div opp inv Hf Pd kind Lt frow (svB ++ svS) cls kp Hvs);
        [lia | exact Hslots | exact Hfunc].
    + intros kp v hv i hi. apply in_app_or in hi. destruct hi as [hi | hi]; [exact (HmB v hv i hi) |].
      destruct (cbk_rows kind frow cls kp v i hi) as [[hk ->] | (cl & t & hcl & ht & <- & <-)].
      - exact (HfB v hv hk).
      - exact (HtB cl hcl t ht hv).
    + intros kp v hv i hi. apply in_app_or in hi. destruct hi as [hi | hi]; [exact (HmS v hv i hi) |].
      destruct (cbk_rows kind frow cls kp v i hi) as [[hk ->] | (cl & t & hcl & ht & <- & <-)].
      - exact (HfS v hv hk).
      - exact (HtS cl hcl t ht hv).
  Qed.

End OpenClaims.
