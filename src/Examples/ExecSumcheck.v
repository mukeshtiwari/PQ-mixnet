(* Executable eq tables, interpolation and sumcheck rounds (fp_core.py:
   eq_table, interp, sc_verify), and their refinement.

   - xeq_table r        the table eq(., r) on the cube; variable 0 is the
                        least significant index bit, as in fp_core.eq_table;
     to_F_eq_table:     map to_F (xeq_table r) = eqvec (length r) (map to_F r).
   - xinterp vals x     fp_core.interp; to_F_interp: it computes interpF.
   - xsc_verify         the rounds of fp_core.sc_verify for given challenges
                        (absorbing and drawing the challenges is not here);
     xsc_sound:         if it accepts with final claim c, the coefficient
                        lists of its messages pass Sumcheck.sc_verify over
                        GF(q^2) with final claim to_F c, and each is at most
                        one longer than its message. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool setoid_ring.Field PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Utility Require Import Zpstar.
From Crypto Require Import Counting LogDer Mle PolyFun Sumcheck CubeIndex RowLayout. From Examples Require Import ConcreteField ExecField. From Crypto Require Import Interp.
Import ListNotations.

Add Field fieldF2 : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation nF2 := (@nF Fq2 fzero fone fadd).
Local Notation eqp2 := (@eqp Fq2 fone fadd fmul fsub).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation eqvec2 := (@eqvec Fq2 fzero fone fadd fmul fsub).
Local Notation fsum2 := (@fsum Fq2 fzero fadd).
Local Notation interpF2 := (@interpF Fq2 fzero fone fadd fmul fsub finv).
Local Notation esc_verify2 := (@esc_verify Fq2 fzero fone fadd fmul fsub finv).

(* ---------------------------------------------------------------------- *)
(* small facts *)

Lemma to_F_xint_nat : forall k : nat, to_F (xint (Z.of_nat k)) = nF2 k.
Proof.
  intro k. destruct (nF2_value k) as [h1 h2]. destruct (nF2 k) as [a b] eqn:e. cbn [fst snd] in h1, h2.
  subst b. unfold to_F, xint. cbn [fst snd]. f_equal.
  + apply zq_eq. cbn [zq_of Zpfield.v]. rewrite h1. apply Zmod_mod.
  + apply zq_eq. reflexivity.
Qed.

Lemma to_F_nth : forall (l : list xf) i, to_F (nth i l xzero) = nth i (map to_F l) fzero.
Proof.
  intros l i. rewrite <-to_F_zero. symmetry. apply (map_nth to_F l xzero i).
Qed.

Definition xfsum (l : list xf) : xf := fold_right xadd xzero l.

Lemma to_F_fsum : forall l, to_F (xfsum l) = fsum2 (map to_F l).
Proof.
  induction l as [| x l ih]; [exact to_F_zero |]. cbn [xfsum fold_right map LogDer.fsum].
  fold (xfsum l). rewrite to_F_add, ih. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* eq tables *)

Fixpoint xeq_table (r : list xf) : list xf :=
  match r with
  | [] => [xone]
  | r0 :: r' => flat_map (fun t => [xmul t (xsub xone r0); xmul t r0]) (xeq_table r')
  end.

Lemma map_seq_double : forall {A : Type} (f : nat -> A) n,
  map f (seq 0 (2 * n)) = flat_map (fun j => [f (2 * j)%nat; f (2 * j + 1)%nat]) (seq 0 n).
Proof.
  intros A f; induction n as [| n ih]; [reflexivity |].
  replace (2 * S n)%nat with (2 * n + 2)%nat by lia.
  rewrite (seq_app (2 * n) 2 0), map_app, ih, (seq_S n 0), flat_map_app.
  f_equal. cbn [flat_map seq map app]. try rewrite app_nil_r.
  replace (0 + 2 * n)%nat with (2 * (0 + n))%nat by lia.
  replace (S (2 * (0 + n)))%nat with (2 * (0 + n) + 1)%nat by lia. reflexivity.
Qed.

Lemma pt_even : forall k j, pt2 (S k) (2 * j) = fzero :: pt2 k j.
Proof.
  intros k j. cbn [CubeIndex.pt]. unfold CubeIndex.bit.
  rewrite Nat.odd_mul. cbn [Nat.odd Nat.even negb andb]. rewrite Nat.div2_double. reflexivity.
Qed.

Lemma pt_odd : forall k j, pt2 (S k) (2 * j + 1) = fone :: pt2 k j.
Proof.
  intros k j. rewrite Nat.add_1_r. cbn [CubeIndex.pt]. unfold CubeIndex.bit.
  rewrite Nat.odd_succ, Nat.even_mul. cbn [Nat.even orb]. rewrite Nat.div2_succ_double. reflexivity.
Qed.

Lemma flat_map_map : forall {A B C : Type} (g : B -> list C) (h : A -> B) (l : list A),
  flat_map g (map h l) = flat_map (fun a => g (h a)) l.
Proof. intros A B C g h; induction l as [| a l ih]; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

Lemma eqvec_cons : forall k x0 x,
  eqvec2 (S k) (x0 :: x)
  = flat_map (fun t => [fmul t (fsub fone x0); fmul t x0]) (eqvec2 k x).
Proof.
  intros k x0 x. unfold RowLayout.eqvec.
  rewrite Nat.pow_succ_r', map_seq_double.
  rewrite flat_map_map.
  apply flat_map_ext. intro j. rewrite pt_even, pt_odd. cbn [Mle.eqp].
  f_equal; [| f_equal]; field.
Qed.

Theorem to_F_eq_table : forall r, map to_F (xeq_table r) = eqvec2 (length r) (map to_F r).
Proof.
  induction r as [| r0 r ih].
  + cbn. rewrite to_F_one. unfold RowLayout.eqvec. cbn. reflexivity.
  + cbn [xeq_table length map]. rewrite eqvec_cons, <-ih.
    rewrite flat_map_map.
    transitivity (flat_map (fun t => map to_F [xmul t (xsub xone r0); xmul t r0]) (xeq_table r)).
    { generalize (xeq_table r). induction l as [| t l ihl]; [reflexivity |].
      cbn [flat_map]. rewrite map_app, ihl. reflexivity. }
    apply flat_map_ext. intro t. cbn [map]. rewrite !to_F_mul, to_F_sub, to_F_one. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* interpolation *)

Fixpoint xnumL (i : nat) (l : list nat) (x : xf) : xf :=
  match l with
  | [] => xone
  | j :: l' => if Nat.eqb j i then xnumL i l' x else xmul (xsub x (xint (Z.of_nat j))) (xnumL i l' x)
  end.

Definition xinterp (vals : list xf) (x : xf) : xf :=
  xfsum (map (fun i => xmul (nth i vals xzero)
                            (xmul (xnumL i (seq 0 (length vals)) x)
                                  (xinv (xnumL i (seq 0 (length vals)) (xint (Z.of_nat i))))))
             (seq 0 (length vals))).

Lemma to_F_numL : forall i l x,
  to_F (xnumL i l x) = @numL Fq2 fzero fone fadd fmul fsub i l (to_F x).
Proof.
  intros i; induction l as [| j l ih]; intro x; [exact to_F_one |].
  cbn [xnumL Interp.numL]. destruct (Nat.eqb j i); [apply ih |].
  rewrite to_F_mul, to_F_sub, to_F_xint_nat, ih. reflexivity.
Qed.

Theorem to_F_interp : forall vals x, to_F (xinterp vals x) = interpF2 (map to_F vals) (to_F x).
Proof.
  intros vals x. unfold xinterp, Interp.interpF. rewrite to_F_fsum, map_map, length_map.
  f_equal. apply map_ext. intro i.
  rewrite to_F_mul, to_F_mul, to_F_inv, !to_F_numL, to_F_xint_nat, to_F_nth. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the rounds *)

Definition xfullvals (claim : xf) (ev : list xf) : list xf :=
  match ev with
  | [] => []
  | e0 :: rest => e0 :: xsub claim e0 :: rest
  end.

Fixpoint xsc_verify (msgs : list (list xf)) (chals : list xf) (claim : xf) : option xf :=
  match msgs, chals with
  | [], [] => Some claim
  | ev :: ms, r :: cs =>
      match ev with
      | [] => None
      | _ => xsc_verify ms cs (xinterp (xfullvals claim ev) r)
      end
  | _, _ => None
  end.

Lemma to_F_fullvals : forall claim ev,
  map to_F (xfullvals claim ev) = @fullvals Fq2 fsub (to_F claim) (map to_F ev).
Proof.
  intros claim [| e0 rest]; [reflexivity |]. cbn [xfullvals Interp.fullvals map]. rewrite to_F_sub. reflexivity.
Qed.

Theorem to_F_sc_verify : forall msgs chals claim c,
  xsc_verify msgs chals claim = Some c ->
  esc_verify2 (map (map to_F) msgs) (map to_F chals) (to_F claim) = Some (to_F c).
Proof.
  induction msgs as [| ev ms ih]; intros chals claim c h; destruct chals as [| r cs]; cbn in h; try discriminate.
  + injection h as <-. reflexivity.
  + destruct ev as [| e0 rest]; [discriminate |].
    cbn [map Interp.esc_verify]. rewrite <-(map_cons to_F e0 rest), <-to_F_fullvals, <-to_F_interp.
    exact (ih cs _ c h).
Qed.

Lemma Fq2_char_upto : forall D : nat, (Z.of_nat D < Q)%Z -> forall k, (0 < k <= D)%nat -> nF2 k <> fzero.
Proof. intros D hD k hk. apply Fq2_char. lia. Qed.

(* The executable sumcheck verifier accepts only what the verifier of the
   soundness proofs accepts. *)
Theorem xsc_sound : forall (D : nat) msgs chals claim c,
  (Z.of_nat D < Q)%Z ->
  Forall (fun ev => (length ev <= D)%nat) msgs ->
  xsc_verify msgs chals claim = Some c ->
  exists cms,
    @Sumcheck.sc_verify Fq2 fzero fone fadd fmul Fq2_dec cms (map to_F chals) (to_F claim) = Some (to_F c) /\
    Forall2 (fun ev p => (length p <= S (length ev))%nat) msgs cms.
Proof.
  intros D msgs chals claim c hD hl h.
  pose proof (to_F_sc_verify msgs chals claim c h) as he.
  assert (hl' : Forall (fun ev => (length ev <= D)%nat) (map (map to_F) msgs)).
  { apply Forall_map. eapply Forall_impl; [| exact hl]. intros ev hev. rewrite length_map. exact hev. }
  destruct (@esc_sound Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field D (Fq2_char_upto D hD)
              _ _ _ _ hl' he) as [h1 h2].
  eexists. split; [exact h1 |].
  clear h1 he hl'. revert h2. generalize (@coefmsgs Fq2 fzero fone fadd fmul fsub fopp finv
                                            (map (map to_F) msgs) (map to_F chals) (to_F claim)).
  clear hl h. induction msgs as [| ev ms ih]; intros cms h2.
  + inversion h2. constructor.
  + cbn [map] in h2. inversion h2 as [| ? p ? cms' hp hcms]; subst. constructor.
    - rewrite length_map in hp. exact hp.
    - apply ih. exact hcms.
Qed.

(* ---------------------------------------------------------------------- *)
(* lo-vectors and hi-coefficients of a table laid out in rows of 2^lo
   entries (fp_core.py: lo_vec, hi_coefs); the table has 2^(length x)
   entries. *)

Local Notation lovec2 := (@lovec Fq2 fzero fone fadd fmul fsub).

Lemma map_repeat' : forall {A B : Type} (f : A -> B) (a : A) n, map f (repeat a n) = repeat (f a) n.
Proof. intros A B f a n; induction n as [| n ih]; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

Definition xlo_vec (lo : nat) (x : list xf) : list xf :=
  if Nat.leb lo (length x) then xeq_table (firstn lo x)
  else xeq_table x ++ repeat xzero (2 ^ lo - 2 ^ length x).

Definition xhi_coefs (lo : nat) (x : list xf) : list xf :=
  if Nat.ltb lo (length x) then xeq_table (skipn lo x) else [xone].

Theorem to_F_lo_vec : forall lo x, map to_F (xlo_vec lo x) = lovec2 (length x) lo (map to_F x).
Proof.
  intros lo x. unfold xlo_vec, RowLayout.lovec, RowLayout.loE.
  destruct (Nat.leb lo (length x)) eqn:e.
  + apply Nat.leb_le in e. rewrite (Nat.min_l lo (length x) e), Nat.sub_diag. cbn [repeat]. rewrite app_nil_r.
    rewrite to_F_eq_table, <-firstn_map, length_firstn, (Nat.min_l lo (length x) e). reflexivity.
  + apply Nat.leb_gt in e. rewrite (Nat.min_r lo (length x) ltac:(lia)).
    rewrite map_app, to_F_eq_table, firstn_all2 by (rewrite length_map; lia).
    rewrite map_repeat', to_F_zero. reflexivity.
Qed.

(* the coefficients of the rows in a tensor claim (RowLayout.tabt) *)
Theorem to_F_hi_coefs : forall lo x,
  map to_F (xhi_coefs lo x)
  = eqvec2 (hiE (length x) lo) (skipn (loE (length x) lo) (map to_F x)).
Proof.
  intros lo x. unfold xhi_coefs, RowLayout.hiE, RowLayout.loE.
  destruct (Nat.ltb lo (length x)) eqn:e.
  + apply Nat.ltb_lt in e. rewrite (Nat.min_l lo (length x) ltac:(lia)).
    rewrite to_F_eq_table, <-skipn_map, length_skipn. reflexivity.
  + apply Nat.ltb_ge in e. rewrite (Nat.min_r lo (length x) e), Nat.sub_diag.
    cbn [map]. rewrite to_F_one. unfold RowLayout.eqvec. cbn. reflexivity.
Qed.
