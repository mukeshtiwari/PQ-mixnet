(* The verifier's tables of the shuffle proof, computed from the statement
   (mix_proof.py: public_projection), at GF(q^2) and as executable code.

   At the field (Section Tables): for a statement (a, b, p, cin, cout) over
   GF(q^2) and a first challenge c1 = alpha :: rho_u ++ rho_v ++ [beta],
     rp1T c1, rp2T c1, rp3T c1   the blocks of rho' = rho . M_pk as tables,
     zpT c1, zhT c1              the projections of cin i and cout j,
     alT c1, beT c1              alpha and beta.
   Theorem Hver_tables: these satisfy the hypothesis Hver of mix_full /
   mix_theorem_5_2. So the verifier's tables of the final theorem are no
   longer a hypothesis: they are these functions.

   Executable (xmle, xnadj, xrho_r, xproj, xpublic): the same values from
   integer pairs; to_F_mle, to_F_rho_r, to_F_proj give the refinement.
   xrho_r computes rho' with the adjoint nadj; mix_proof.py computes the
   same vector as <rho_u, a X^y> + <rho_v, b X^y> for every y (compared in
   Unverified/cross_field.py). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex MixMultiset MixBridge LayoutLemmas RowLayout MixSoundA. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecOpen.
From Examples Require Export ExecNadj.
Import ListNotations.

Add Field fieldF2p : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation bidx2 := (@bidx Fq2 fone Fq2_dec).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation ctx2 := (@ctx Fq2).

(* a list as a table on the cube *)
Definition tabOf (l : list Fq2) (bq : list Fq2) : Fq2 := nth (bidx2 bq) l fzero.

Lemma tabOf_pt : forall k l y, (y < 2 ^ k)%nat -> tabOf l (pt2 k y) = nth y l fzero.
Proof.
  intros k l y hy. unfold tabOf.
  rewrite (@bidx_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field k y hy). reflexivity.
Qed.

Section Tables.

  Variables (a b : list Fq2) (pp : Fq2).
  Variables n1 ell : nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Variables cin cout : nat -> ctx2.

  Definition ruOf (c1 : list Fq2) : list Fq2 := firstn N (tl c1).
  Definition rvOf (c1 : list Fq2) : list Fq2 := firstn N (skipn (S N) c1).
  Definition alT (c1 : list Fq2) : Fq2 := nth 0 c1 fzero.
  Definition beT (c1 : list Fq2) : Fq2 := nth (S (N + N)) c1 fzero.

  Definition rp1T (c1 : list Fq2) : list Fq2 -> Fq2 :=
    tabOf (@rho_r Fq2 fadd fmul fopp a b (ruOf c1) (rvOf c1)).
  Definition rp2T (c1 : list Fq2) : list Fq2 -> Fq2 := tabOf (@rho_e1 Fq2 fmul pp (ruOf c1)).
  Definition rp3T (c1 : list Fq2) : list Fq2 -> Fq2 := tabOf (@rho_e2 Fq2 fmul pp (rvOf c1)).
  Definition zpT (c1 : list Fq2) : list Fq2 -> Fq2 :=
    tabOf (map (fun i => @proj Fq2 fzero fadd fmul (ruOf c1) (rvOf c1) (cin i)) (seq 0 tau)).
  Definition zhT (c1 : list Fq2) : list Fq2 -> Fq2 :=
    tabOf (map (fun j => @proj Fq2 fzero fadd fmul (ruOf c1) (rvOf c1) (cout j)) (seq 0 tau)).

  Lemma point_fields : forall ru rv al be, length ru = N -> length rv = N ->
    let c1 := @point Fq2 ru rv al be in
    ruOf c1 = ru /\ rvOf c1 = rv /\ alT c1 = al /\ beT c1 = be.
  Proof.
    intros ru rv al be hu hv c1. unfold c1, MixMultiset.point, ruOf, rvOf, alT, beT. cbn [tl nth].
    split; [| split; [| split]].
    + rewrite firstn_app, hu, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia.
    + cbn [skipn]. rewrite skipn_app, hu, Nat.sub_diag. cbn [skipn].
      rewrite (skipn_all2 (n := N)) by lia. cbn [app].
      rewrite firstn_app, hv, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia.
    + reflexivity.
    + rewrite app_nth2 by lia. rewrite hu. rewrite app_nth2 by lia. rewrite hv.
      replace (N + N - N - N)%nat with 0%nat by lia. reflexivity.
  Qed.

  Theorem Hver_tables : forall lf : list Fq2, forall c1, In c1 (@C1 Fq2 lf N) ->
    exists ru rv, length ru = N /\ length rv = N /\
      c1 = @point Fq2 ru rv (alT c1) (beT c1) /\
      (forall y, (y < N)%nat -> rp1T c1 (pt2 n1 y) = nth y (@rho_r Fq2 fadd fmul fopp a b ru rv) fzero) /\
      (forall y, (y < N)%nat -> rp2T c1 (pt2 n1 y) = nth y (@rho_e1 Fq2 fmul pp ru) fzero) /\
      (forall y, (y < N)%nat -> rp3T c1 (pt2 n1 y) = nth y (@rho_e2 Fq2 fmul pp rv) fzero) /\
      (forall i, (i < tau)%nat -> zpT c1 (pt2 ell i) = @proj Fq2 fzero fadd fmul ru rv (cin i)) /\
      (forall j, (j < tau)%nat -> zhT c1 (pt2 ell j) = @proj Fq2 fzero fadd fmul ru rv (cout j)).
  Proof.
    intros lf c1 hc. unfold MixSoundA.C1 in hc. apply all_lists_In in hc. destruct hc as [hl _].
    destruct (@point_parse Fq2 N c1 hl) as (ru & rv & al & be & hu & hv & e).
    destruct (point_fields ru rv al be hu hv) as (e1 & e2 & e3 & e4).
    rewrite <-e in e1, e2, e3, e4.
    exists ru, rv. split; [exact hu | split; [exact hv | split]].
    { rewrite e3, e4. exact e. }
    split; [| split; [| split; [| split]]]; intros y hy.
    + unfold rp1T. rewrite tabOf_pt by exact hy. rewrite e1, e2. reflexivity.
    + unfold rp2T. rewrite tabOf_pt by exact hy. rewrite e1. reflexivity.
    + unfold rp3T. rewrite tabOf_pt by exact hy. rewrite e2. reflexivity.
    + unfold zpT. rewrite tabOf_pt by exact hy. rewrite e1, e2.
      rewrite (nth_indep _ fzero (@proj Fq2 fzero fadd fmul ru rv (cin 0))) by (rewrite length_map, length_seq; exact hy).
      rewrite (map_nth (fun i => @proj Fq2 fzero fadd fmul ru rv (cin i))), seq_nth by exact hy. reflexivity.
    + unfold zhT. rewrite tabOf_pt by exact hy. rewrite e1, e2.
      rewrite (nth_indep _ fzero (@proj Fq2 fzero fadd fmul ru rv (cout 0))) by (rewrite length_map, length_seq; exact hy).
      rewrite (map_nth (fun j => @proj Fq2 fzero fadd fmul ru rv (cout j))), seq_nth by exact hy. reflexivity.
  Qed.

End Tables.

(* ---------------------------------------------------------------------- *)
(* executable *)

(* mle of a table of 2^(length r) entries *)
Definition xmle (tbl r : list xf) : xf := xdot tbl (xeq_table r).

Theorem to_F_mle : forall tbl r, length tbl = (2 ^ length r)%nat ->
  to_F (xmle tbl r) = mle2 (length r) (tabOf (map to_F tbl)) (map to_F r).
Proof.
  intros tbl r hl. unfold xmle. rewrite to_F_dot, to_F_eq_table.
  unfold RowLayout.eqvec.
  rewrite (@dot_seq0 Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
  rewrite (@mle_seq Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
  apply (@fsum_map_ext Fq2 fzero fadd). intros y hy. apply in_seq in hy.
  rewrite tabOf_pt by lia. reflexivity.
Qed.

Definition xrho_r (a b ru rv : list xf) : list xf := xpadd (xnadj a ru) (xnadj b rv).
Definition xrho_e (pp : xf) (r : list xf) : list xf := xpscale pp r.
Definition xproj (ru rv : list xf) (c : list xf * list xf) : xf := xadd (xdot ru (fst c)) (xdot rv (snd c)).

Theorem to_F_rho_r : forall a b ru rv,
  map to_F (xrho_r a b ru rv) = @rho_r Fq2 fadd fmul fopp (map to_F a) (map to_F b) (map to_F ru) (map to_F rv).
Proof. intros. unfold xrho_r, Bgv.rho_r. rewrite to_F_padd, !to_F_nadj. reflexivity. Qed.

Theorem to_F_rho_e : forall pp r, map to_F (xrho_e pp r) = @rho_e1 Fq2 fmul (to_F pp) (map to_F r).
Proof. intros. unfold xrho_e, Bgv.rho_e1. apply to_F_pscale. Qed.

Definition ctxF (c : list xf * list xf) : ctx2 := (map to_F (fst c), map to_F (snd c)).

Theorem to_F_proj : forall ru rv c,
  to_F (xproj ru rv c) = @proj Fq2 fzero fadd fmul (map to_F ru) (map to_F rv) (ctxF c).
Proof. intros. unfold xproj, Bgv.proj, ctxF. cbn [fst snd]. rewrite to_F_add, !to_F_dot. reflexivity. Qed.
