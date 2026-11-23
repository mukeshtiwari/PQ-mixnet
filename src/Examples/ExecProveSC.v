(* Prover side, stage 2: the sumcheck prover in evaluation form
   (fp_core.py: sc_prove) and its completeness.

   For a summand gx (executable, refining a function gF on GF(q^2)), the
   message of the round with prefix pre is the values of the round
   polynomial X |-> sum_(b in cube k) g(pre ++ X :: b) at 0, 2, 3, .., d:
   the values fp_core.sc_prove sends. They are computed here by summing
   over the cube (fp_core.py folds tables; the values are the same).

   Theorem xsc_complete: if every round function of gF is a polynomial of
   degree at most the round degree (the certificates certA, certB, certC,
   certZ of the soundness proofs give this), the verifier xsc_verify
   accepts the honest messages for the true sum and returns gF at the
   challenges. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Sumcheck Interp. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecDerive.
Import ListNotations.

Add Field fieldF2s : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation cube2 := (@cube Fq2 fzero fone).
Local Notation tsum2 := (@tsum Fq2 fzero fone fadd).
Local Notation rnd2 := (@rnd Fq2 fzero fone fadd).
Local Notation peval2 := (@eval Fq2 fzero fadd fmul).
Local Notation nF2 := (@nF Fq2 fzero fone fadd).

Fixpoint xcube (k : nat) : list (list xf) :=
  match k with
  | O => [[]]
  | S k' => map (cons xzero) (xcube k') ++ map (cons xone) (xcube k')
  end.

Lemma to_F_cube : forall k, map (map to_F) (xcube k) = cube2 k.
Proof.
  induction k as [| k ih]; [reflexivity |].
  rewrite (@cube_S Fq2 fzero fone). cbn [xcube]. rewrite map_app, !map_map. cbn [map].
  rewrite to_F_zero, to_F_one, <-ih, !map_map. reflexivity.
Qed.

Section Prover.

  Variable gx : list xf -> xf.
  Variable gF : list Fq2 -> Fq2.
  Hypothesis Hg : forall x, to_F (gx x) = gF (map to_F x).

  Definition xsum_cube (pre : list xf) (k : nat) (c : xf) : xf :=
    xfsum (map (fun b => gx (pre ++ c :: b)) (xcube k)).

  Lemma to_F_sum_cube : forall pre k c, to_F (xsum_cube pre k c) = rnd2 gF (map to_F pre) k (to_F c).
  Proof.
    intros pre k c. unfold xsum_cube, Sumcheck.rnd. rewrite to_F_fsum, map_map, <-to_F_cube, map_map.
    f_equal. apply map_ext. intro b. rewrite Hg, map_app. reflexivity.
  Qed.

  (* the message of one round: values at 0, 2, .., d *)
  Definition xround (d : nat) (pre : list xf) (k : nat) : list xf :=
    let R c := xsum_cube pre k (xint (Z.of_nat c)) in R 0%nat :: map R (seq 2 (d - 1)).

  Variable degf : nat -> nat.

  Fixpoint xprove_rounds (pre chals : list xf) : list (list xf) :=
    match chals with
    | [] => []
    | r :: cs => xround (degf (List.length pre)) pre (List.length cs) :: xprove_rounds (pre ++ [r]) cs
    end.

  Variable m : nat.
  Hypothesis Hdeg : forall j, (1 <= degf j <= DMAX)%nat.
  Hypothesis Hpoly : forall pre k, (List.length pre + S k = m)%nat ->
    exists p, (List.length p <= S (degf (List.length pre)))%nat /\ forall X, peval2 p X = rnd2 gF pre k X.

  Theorem xsc_complete : forall chals pre claim, (List.length pre + List.length chals = m)%nat ->
    to_F claim = tsum2 gF (map to_F pre) (List.length chals) ->
    exists c, xsc_verify (xprove_rounds pre chals) chals claim = Some c /\ to_F c = gF (map to_F (pre ++ chals)).
  Proof.
    induction chals as [| r cs ih]; intros pre claim hl hc.
    + exists claim. split; [reflexivity |]. rewrite hc, (@tsum_0 Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
        app_nil_r. reflexivity.
    + cbn [xprove_rounds]. set (d := degf (List.length pre)). set (k := List.length cs).
      destruct (Hpoly (map to_F pre) k ltac:(rewrite length_map; cbn in hl; lia)) as (p & hp & ep).
      rewrite length_map in hp. fold d in hp.
      set (ev := xround d pre k).
      assert (hev : ev = xsum_cube pre k (xint 0) :: map (fun c => xsum_cube pre k (xint (Z.of_nat c))) (seq 2 (d - 1)))
        by reflexivity.
      rewrite hev. cbn [xsc_verify].
      set (claim' := xinterp (xfullvals claim (xsum_cube pre k (xint 0)
                               :: map (fun c => xsum_cube pre k (xint (Z.of_nat c))) (seq 2 (d - 1)))) r).
      assert (hc' : to_F claim' = tsum2 gF (map to_F (pre ++ [r])) (List.length cs)).
      { unfold claim'. rewrite to_F_interp, to_F_fullvals. cbn [map].
        rewrite map_app. cbn [map].
        rewrite <-(@rnd_snoc Fq2 fzero fone fadd gF). fold k.
        rewrite <-(ep (to_F r)).
        apply (@interp_unique Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field DMAX
                 (Fq2_char_upto DMAX ltac:(vm_compute; reflexivity))).
        - cbn [Interp.fullvals List.length]. rewrite !length_map, length_seq. pose proof (Hdeg (List.length pre)). fold d in H. lia.
        - cbn [Interp.fullvals List.length]. rewrite !length_map, length_seq. pose proof (Hdeg (List.length pre)). fold d in H. lia.
        - intros j hj. cbn [Interp.fullvals List.length] in hj. rewrite !length_map, length_seq in hj.
          rewrite ep. cbn [Interp.fullvals].
          destruct j as [| [| j]].
          * cbn [nth]. rewrite to_F_sum_cube, (to_F_xint_nat 0 : to_F (xint 0%Z) = nF2 0). reflexivity.
          * cbn [nth]. cbn [List.length] in hc. fold k in hc. rewrite hc, to_F_sum_cube, (to_F_xint_nat 0 : to_F (xint 0%Z) = nF2 0).
            fold k. rewrite (@tsum_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
            replace (nF2 1) with fone by (cbn; field). cbn [nF]. field.
          * cbn [nth]. rewrite map_map.
            rewrite (nth_indep _ fzero ((fun c => to_F (xsum_cube pre k (xint (Z.of_nat c)))) 0%nat))
              by (rewrite length_map, length_seq; lia).
            rewrite (map_nth (fun c => to_F (xsum_cube pre k (xint (Z.of_nat c)))) (seq 2 (d - 1)) 0%nat j).
            rewrite seq_nth by lia. rewrite to_F_sum_cube, to_F_xint_nat. f_equal. }
      destruct (ih (pre ++ [r]) claim' ltac:(rewrite length_app; cbn in hl |- *; lia) hc') as (c & h1 & h2).
      assert (hne : xsum_cube pre k (xint 0) :: map (fun c => xsum_cube pre k (xint (Z.of_nat c))) (seq 2 (d - 1)) <> [])
        by discriminate.
      exists c. split.
      * fold claim'. exact h1.
      * rewrite h2, <-app_assoc. reflexivity.
  Qed.

End Prover.
