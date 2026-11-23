(* The opening theorem with its decoding hypotheses discharged.

   open_sound_dec is open_sound for the decoded rows
       Pdec i = dec (X i)        (the decoder of the matrix that row i is in)
   and the closeness tests clM of RsDecode.v. What remains assumed is, for
   each of the two codes, a proximity lemma Prox with numerator pn:

       if more than pn |F|^(R-1) of the combinations m + sum g_i row_i are
       within e of the code, then m and the rows agree with codewords
       outside one set of at most e columns.

   For Delta = 3 this is rs_prox_affine (pn = e + 2), which in turn assumes
   the line lemma; for Delta = 2 it is the statement of BCIKS20, Theorem 1.6
   (pn = n). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Proximity ReedSolomon Opening MatQueries OpenSound RsDecode.
Import ListNotations.

Section OpenSoundDec.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Local Notation pw := (@pw F one mul).
  Local Notation pi := (@pi F zero add mul).

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
  Local Notation decB := (@dec F zero one add mul Fdec lf omB nb kb eb).
  Local Notation decS := (@dec F zero one add mul Fdec lf omS ns ks es).

  (* the proximity lemma for each code *)
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
  Variables rwsB rwsS : list nat.        (* the rows of each matrix *)
  Variables xmpB xmpS : nat -> F.        (* the words of the proximity masks *)
  Hypothesis Hdisj : forall i, In i rwsS -> ~ In i rwsB.

  (* the decoded message of row i *)
  Definition Pdec (i : nat) : list F :=
    if in_dec Nat.eq_dec i rwsB then decB (X i) else decS (X i).

  Variables vals tv : list F.
  Hypothesis Hvals : length vals = length tv.
  Variable Lk : list F -> nat -> list F.
  Variable cbk : list F -> nat -> list (nat * F).
  Variable mcb : nat -> list (nat * F).
  Variables svB svS : list nat.
  Hypothesis Hbatch : forall kp, In kp (all_lists lf (length vals)) ->
    @fsum F zero add (map (fun v => @vsum F zero add mul Pdec (cbk kp v) (Lk kp v)) (svB ++ svS))
    = @dot F zero add mul kp tv.
  Hypothesis HrowB : forall kp v, In v svB -> forall i, In i (map fst (mcb v) ++ map fst (cbk kp v)) -> In i rwsB.
  Hypothesis HrowS : forall kp v, In v svS -> forall i, In i (map fst (mcb v) ++ map fst (cbk kp v)) -> In i rwsS.

  Variable mu : list F -> F.
  Variable ub : list F -> @cgT F -> nat -> list F.
  Variables pvB pvS : list F -> @cgT F -> list F.

  Theorem open_sound_dec :
    vals <> tv ->
    card_le (list_prod (@OK F lf vals) (list_prod (@OCG F lf rwsB rwsS) (OJ nb nqb ns nqs)))
            (fun w => @AccO F zero one add mul omB omS kb ks X rwsB rwsS xmpB xmpS vals Lk cbk mcb svB svS
                        mu ub pvB pvS (fst w) (fst (snd w)) (snd (snd w)))
            (@open_bound F lf nb eb nqb pnb ns es nqs pns rwsB rwsS vals).
  Proof.
    assert (hq0 : (0 < length lf)%nat).
    { destruct lf as [| x l]; [exact (False_ind _ (Hall zero)) | cbn; lia]. }
    apply (@open_sound F zero one add mul sub div opp inv Fdec Hf lf Hnd hq0 omB omS nb kb eb nqb pnb ns ks es nqs pns
             HkB HkS HnodesB HnodesS HeB HeS X Pdec rwsB rwsS rwsB rwsS xmpB xmpS
             (@clM F zero one add mul Fdec lf omB nb kb eb X xmpB rwsB)
             (@clM F zero one add mul Fdec lf omS ns ks es X xmpS rwsS)).
    + exact (@far_M F zero one add mul sub div opp inv Fdec Hf lf Hall omB nb kb eb HkB HeB X xmpB rwsB).
    + exact (@far_M F zero one add mul sub div opp inv Fdec Hf lf Hall omS ns ks es HkS HeS X xmpS rwsS).
    + intro hm.
      destruct (@dec_many F zero one add mul sub div opp inv Fdec Hf lf Hall omB nb kb eb HkB HnodesB HeB pnb ProxB
                  X xmpB rwsB hm) as (E & hE & hrows).
      exists E. split; [exact hE |]. intros i hi. unfold Pdec.
      destruct (in_dec Nat.eq_dec i rwsB) as [_ | hn]; [exact (hrows i hi) | contradiction].
    + intro hm.
      destruct (@dec_many F zero one add mul sub div opp inv Fdec Hf lf Hall omS ns ks es HkS HnodesS HeS pns ProxS
                  X xmpS rwsS hm) as (E & hE & hrows).
      exists E. split; [exact hE |]. intros i hi. unfold Pdec.
      destruct (in_dec Nat.eq_dec i rwsB) as [hb | _]; [exfalso; exact (Hdisj i hi hb) | exact (hrows i hi)].
    + exact Hvals.
    + exact Hbatch.
    + exact HrowB.
    + exact HrowS.
  Qed.

End OpenSoundDec.
