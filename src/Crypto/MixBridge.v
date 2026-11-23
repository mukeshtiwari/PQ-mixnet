(* From the tables of the protocol to the ballots (the two hypotheses Hh
   and Hhh of MixSoundA.v, for the concrete tables).

   The committed witness is three tables W1, W2, W3 on the cube of
   n1 + ell variables, coefficient index first. Ballot i has re-randomiser

       wr i = (W1 (pt y ++ pt i))_y,  we1 i, we2 i      (y < N = 2^n1)

   and re-randomised input rr i = c_i + Enc_0(wr i, we1 i, we2 i).

   For a challenge c1 = alpha :: rho_u ++ rho_v ++ [beta], the verifier's
   tables are any functions with the right values on the cube:
     rp_k (pt y) = entry y of the k-th block of rho' = rho * M_pk,
     zp (pt i)   = proj rho c_i,      zh (pt j) = proj rho chat_j.

   - bridge_h:  htab (pt i) = dot (form (rr i) i) c1. The table h of the
     protocol takes at ballot i the value of the tagged re-randomised
     input, through proj_rerand (paper eq. 1).
   - bridge_hh: hhtab (pt j) = dot (form (chat_j) sigma_j) c1.
   - point_parse: every list of length 2N + 2 is such a challenge. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex MixMultiset MixSummands MixIdentities.
Import ListNotations.

Section MixBridge.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation nF := (@nF F zero one add).
  Local Notation cube := (@cube F zero one).
  Local Notation pt := (@pt F zero one).
  Local Notation idr := (@idr F zero one add mul).
  Local Notation proj := (@proj F zero add mul).
  Local Notation cadd := (@cadd F add).
  Local Notation enc0 := (@enc0 F zero add mul opp).
  Local Notation wdot := (@wdot F zero add mul opp).
  Local Notation rho_r := (@rho_r F add mul opp).
  Local Notation rho_e1 := (@rho_e1 F mul).
  Local Notation rho_e2 := (@rho_e2 F mul).
  Local Notation form := (@form F one opp).
  Local Notation point := (@point F).
  Local Notation htab := (@htab F zero one add mul sub).
  Local Notation hhtab := (@hhtab F add mul sub).
  Local Notation ctx := (@ctx F).

  Lemma dot_seq : forall (f : nat -> F) (n s : nat) (l : list F),
    dot l (map f (seq s n)) = fsum (map (fun y => nth (y - s) l zero * f y) (seq s n)).
  Proof.
    intro f; induction n as [| n ih]; intros s l.
    + cbn. apply dot_nil_r.
    + destruct l as [| x l].
      - change (dot [] (map f (seq s (S n)))) with zero.
        symmetry. apply (@fsum_map_zero_ext F zero one add mul sub div opp inv Hf).
        intros y _. destruct (y - s)%nat; cbn; field.
      - cbn [seq map LogDer.dot LogDer.fsum]. rewrite Nat.sub_diag. cbn [nth]. f_equal.
        rewrite (ih (S s) l). apply (@fsum_map_ext F zero add). intros y hy. apply in_seq in hy.
        replace (y - s)%nat with (S (y - S s)) by lia. reflexivity.
  Qed.

  Lemma dot_seq0 : forall (f : nat -> F) (n : nat) (l : list F),
    dot l (map f (seq 0 n)) = fsum (map (fun y => nth y l zero * f y) (seq 0 n)).
  Proof.
    intros f n l. rewrite dot_seq. apply (@fsum_map_ext F zero add). intros y _.
    rewrite Nat.sub_0_r. reflexivity.
  Qed.

  Lemma point_parse : forall (N : nat) (c1 : list F), length c1 = S (N + N + 1) ->
    exists ru rv alpha beta, length ru = N /\ length rv = N /\ c1 = point ru rv alpha beta.
  Proof.
    intros N c1 hl. destruct c1 as [| alpha t]; [discriminate |]. cbn in hl.
    assert (hz : length (skipn N (skipn N t)) = 1%nat) by (rewrite !length_skipn; lia).
    destruct (skipn N (skipn N t)) as [| z0 [| z1 z']] eqn:ez; cbn in hz; try lia.
    exists (firstn N t), (firstn N (skipn N t)), alpha, z0.
    split; [rewrite length_firstn; lia | split; [rewrite length_firstn, length_skipn; lia |]].
    unfold MixMultiset.point. f_equal.
    rewrite <-ez, firstn_skipn, firstn_skipn. reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)

  Variables (a b : list F) (pp : F).        (* public key and plaintext modulus *)
  Variables n1 ell : nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Variables cin cout : nat -> ctx.
  Variables W1 W2 W3 sg : list F -> F.

  Definition wr (i : nat) : list F := map (fun y => W1 (pt n1 y ++ pt ell i)) (seq 0 N).
  Definition we1 (i : nat) : list F := map (fun y => W2 (pt n1 y ++ pt ell i)) (seq 0 N).
  Definition we2 (i : nat) : list F := map (fun y => W3 (pt n1 y ++ pt ell i)) (seq 0 N).

  (* re-randomised input i *)
  Definition rrW (i : nat) : ctx := cadd (cin i) (enc0 a b pp (wr i, we1 i, we2 i)).

  Hypothesis Hrr : forall i, (i < tau)%nat -> length (fst (rrW i)) = N /\ length (snd (rrW i)) = N.
  Hypothesis Hco : forall j, (j < tau)%nat -> length (fst (cout j)) = N /\ length (snd (cout j)) = N.

  Variables (ru rv : list F) (alpha beta : F).
  Hypothesis Hru : length ru = N.
  Hypothesis Hrv : length rv = N.

  Variables rp1 rp2 rp3 zp zh : list F -> F.
  Hypothesis Hrp1 : forall y, (y < N)%nat -> rp1 (pt n1 y) = nth y (rho_r a b ru rv) zero.
  Hypothesis Hrp2 : forall y, (y < N)%nat -> rp2 (pt n1 y) = nth y (rho_e1 pp ru) zero.
  Hypothesis Hrp3 : forall y, (y < N)%nat -> rp3 (pt n1 y) = nth y (rho_e2 pp rv) zero.
  Hypothesis Hzp : forall i, (i < tau)%nat -> zp (pt ell i) = proj ru rv (cin i).
  Hypothesis Hzh : forall j, (j < tau)%nat -> zh (pt ell j) = proj ru rv (cout j).

  Lemma lintab_pt : forall i,
    @lintab F zero one add mul n1 rp1 rp2 rp3 W1 W2 W3 (pt ell i) = wdot a b pp ru rv (wr i, we1 i, we2 i).
  Proof.
    intro i. unfold MixIdentities.lintab, Bgv.wdot, wr, we1, we2.
    rewrite (@cube_sum_seq F zero one add mul sub div opp inv Hf n1).
    rewrite !dot_seq0.
    rewrite <-!(@fsum_map_add F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros y hy. apply in_seq in hy.
    rewrite (Hrp1 y ltac:(lia)), (Hrp2 y ltac:(lia)), (Hrp3 y ltac:(lia)). reflexivity.
  Qed.

  Theorem bridge_h : forall i, (i < tau)%nat ->
    htab n1 rp1 rp2 rp3 W1 W2 W3 zp alpha beta (pt ell i) = dot (form (rrW i) (nF i)) (point ru rv alpha beta).
  Proof.
    intros i hi. destruct (Hrr i hi) as [h1 h2].
    rewrite (@dot_form F zero one add mul sub div opp inv Hf (rrW i) (nF i) ru rv alpha beta) by lia.
    unfold rrW at 1.
    rewrite (@proj_rerand F zero one add mul sub div opp inv Hf a b pp ru rv (cin i) (wr i) (we1 i) (we2 i))
      by (unfold wr; rewrite length_map, length_seq; lia).
    unfold MixIdentities.htab.
    rewrite lintab_pt, (Hzp i hi), (@idr_pt F zero one add mul sub div opp inv Hf ell i hi). reflexivity.
  Qed.

  Theorem bridge_hh : forall j, (j < tau)%nat ->
    hhtab sg zh alpha beta (pt ell j) = dot (form (cout j) (sg (pt ell j))) (point ru rv alpha beta).
  Proof.
    intros j hj. destruct (Hco j hj) as [h1 h2].
    rewrite (@dot_form F zero one add mul sub div opp inv Hf (cout j) (sg (pt ell j)) ru rv alpha beta) by lia.
    unfold MixIdentities.hhtab. rewrite (Hzh j hj). reflexivity.
  Qed.

End MixBridge.
