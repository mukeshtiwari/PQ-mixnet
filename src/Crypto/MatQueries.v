(* Column queries on one committed Reed-Solomon matrix (paper, Section 4.2,
   steps 6 and 7, and the last two lines of the error budget).

   X i is the committed word of row i and P i its decoded message. The
   verifier holds, for this matrix,
     - the proximity vector pv, to be compared with the combination
       pi xmp (rows) gam of the committed rows, where xmp is the word of
       the proximity mask (in the implementation a combination of two
       rows);
     - for every slot v of the matrix, a vector ubv v, to be compared with
       the committed combination xw X (mcbv v) (cbv v) c, mcbv v being the
       mask of the slot as rows and weights.

   macc J says that all these comparisons hold at every column of J.

   - mat_consistent: if the boolean test consb holds (the encodings of
     every slot vector and of its decoded combination agree on all
     columns), every slot vector is the decoded combination;
   - mat_bad_queries: if the committed combination for the proximity test
     is not within e of the code, or the matrix decodes with at most e bad
     columns and consb fails, then macc J holds for at most
     fall (n - e - 1) nq of the fall n nq tuples J of nq distinct columns.
     That fraction is at most (1 - (e + 1)/n)^nq <= (1 - e/n)^nq. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Proximity ReedSolomon Opening.
Import ListNotations.

Section MatQueries.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Local Notation pw := (@pw F one mul).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation pi := (@pi F zero add mul).
  Local Notation xw := (@xw F zero add mul).
  Local Notation dm := (@dm F add mul).

  Variable omega : F.
  Variables n k e nq : nat.
  Hypothesis Hk : (k <= n)%nat.
  Hypothesis Hnodes : forall i j, (i < n)%nat -> (j < n)%nat -> pw omega i = pw omega j -> i = j.
  Hypothesis He : (2 * e < n - k + 1)%nat.

  Local Notation rs_enc := (@rs_enc F zero one add mul omega).
  Local Notation rs_code := (@rs_code F zero one add mul omega n k).

  Variable X : nat -> nat -> F.
  Variable P : nat -> list F.

  (* the proximity test *)
  Variable xmp : nat -> F.
  Variable rws : list nat.
  Variable gam : list F.
  Variable pv : list F.

  (* the slots of this matrix *)
  Variable svM : list nat.
  Variable ubv : nat -> list F.
  Variables mcbv cbv : nat -> list (nat * F).
  Variable c : F.

  Definition macc (J : list nat) : Prop :=
    (length pv <= k)%nat /\
    (forall j, In j J -> rs_enc pv j = pi xmp (map X rws) gam j) /\
    (forall v, In v svM ->
       (length (ubv v) <= k)%nat /\
       forall j, In j J -> rs_enc (ubv v) j = xw X (mcbv v) (cbv v) c j).

  Definition slot_ok (v : nat) : bool :=
    forallb (fun j => feqb (rs_enc (ubv v) j) (rs_enc (dm P (mcbv v) (cbv v) c) j)) (seq 0 n).

  Definition consb : bool := forallb slot_ok svM.

  Lemma mat_consistent :
    consb = true ->
    (forall v, In v svM -> (length (ubv v) <= k)%nat) ->
    (forall v, In v svM -> forall i, In i (map fst (mcbv v) ++ map fst (cbv v)) -> (length (P i) <= k)%nat) ->
    forall v, In v svM -> forall t, nth t (ubv v) zero = nth t (dm P (mcbv v) (cbv v) c) zero.
  Proof.
    intros hc hub hP v hv.
    unfold consb in hc. rewrite forallb_forall in hc. specialize (hc v hv).
    unfold slot_ok in hc. rewrite forallb_forall in hc.
    apply (@rs_enc_inj_nth F zero one add mul sub div opp inv Fdec Hf omega n k Hk Hnodes).
    + apply hub; exact hv.
    + apply (@length_dm F add mul n k Hk). apply hP; exact hv.
    + intros j hj. apply feqb_true. apply hc. apply in_seq. lia.
  Qed.

  Theorem mat_bad_queries :
    (~ close n e rs_code (pi xmp (map X rws) gam))
    \/ (exists E, (length E <= e)%nat /\
          (forall v, In v svM -> forall i, In i (map fst (mcbv v) ++ map fst (cbv v)) ->
             (length (P i) <= k)%nat /\ agree_out n E (X i) (rs_enc (P i))) /\
          consb = false) ->
    card_le (qspace n nq) macc (fall (n - e - 1) nq).
  Proof.
    intros [hfar | (E & hE & hrows & hc)].
    + (* the matrix is far: the proximity vector cannot match *)
      destruct (le_dec (length pv) k) as [hl | hl].
      2:{ apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
          intros J _ (h & _). lia. }
      pose proof (@far_few_pass F Fdec n rs_code e (pi xmp (map X rws) gam) (rs_enc pv) hfar
                    (@rs_code_enc F zero one add mul omega n k pv hl)) as hfew.
      pose proof (query_card _ n e nq hfew) as hq.
      eapply card_le_mono; [ | apply le_n | exact hq].
      intros J _ (_ & hp & _) j hj. apply feqb_true. exact (hp j hj).
    + (* the matrix decodes and some slot vector is not the decoded combination *)
      unfold consb in hc. apply forallb_false_ex in hc. destruct hc as (v & hv & hsv).
      unfold slot_ok in hsv. apply forallb_false_ex in hsv. destruct hsv as (j0 & hj0 & hne).
      apply in_seq in hj0.
      destruct (le_dec (length (ubv v)) k) as [hl | hl].
      2:{ apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
          intros J _ (_ & _ & h). destruct (h v hv) as [h1 _]. lia. }
      assert (hPl : forall i, In i (map fst (mcbv v) ++ map fst (cbv v)) -> (length (P i) <= k)%nat)
        by (intros i hi; exact (proj1 (hrows v hv i hi))).
      assert (hag : forall i, In i (map fst (mcbv v) ++ map fst (cbv v)) -> agree_out n E (X i) (rs_enc (P i)))
        by (intros i hi; exact (proj2 (hrows v hv i hi))).
      pose proof (@consistency F Fdec n (n - k + 1) rs_code
                    (@rs_dist F zero one add mul sub div opp inv Fdec Hf omega n k Hk Hnodes)
                    (xw X (mcbv v) (cbv v) c) (rs_enc (ubv v)) (rs_enc (dm P (mcbv v) (cbv v) c)) E
                    (@rs_code_enc F zero one add mul omega n k _ hl)
                    (@rs_code_enc F zero one add mul omega n k _ (@length_dm F add mul n k Hk P _ _ c hPl))
                    (@comb_agree F zero one add mul sub div opp inv Hf omega n X P E _ _ c hag)) as hcons.
      assert (hex : exists j, (j < n)%nat /\ rs_enc (ubv v) j <> rs_enc (dm P (mcbv v) (cbv v) c) j).
      { exists j0; split; [lia |]. intro e0. apply feqb_true in e0. rewrite e0 in hne. discriminate. }
      specialize (hcons hex).
      assert (hfew : (length (filter (fun j => feqb (rs_enc (ubv v) j) (xw X (mcbv v) (cbv v) c j)) (seq 0 n)) + e < n)%nat)
        by lia.
      pose proof (query_card _ n e nq hfew) as hq.
      eapply card_le_mono; [ | apply le_n | exact hq].
      intros J _ (_ & _ & h) j hj. apply feqb_true. exact (proj2 (h v hv) j hj).
  Qed.

End MatQueries.
