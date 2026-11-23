(* Prover side, stage 5a: completeness of the folding sumcheck prover
   (ExecProve.v: xsc_prove, fp_core.sc_prove).

   A summand is a list of terms coef * T_f1 * .. * T_fk over tables T (lists
   of 2^m entries; the first variable is the lowest bit of the index),
   extended off the cube multilinearly and, for a masked table, by
   a * Z(x); plus rho times a sumcheck mask g (SumcheckMask.v: gmask).

   Theorem xsc_prove_complete: if every term has at most d factors in the
   first rounds, at most d counting a masked factor twice in the last
   round, and the mask coefficients of each variable fit the round degree,
   then for the true sum
     claim = sum_(i < 2^m) terms(T(i)) + rho * sum_(cube) g,
   the messages of xsc_prove pass xsc_verify; the verifier's final value is
   terms(final values) + rho * g(point); the final value of each table is
   its masked multilinear extension at the point; and the verifier's
   transcript (sc_chals) draws the same point. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle CubeIndex Sumcheck SumcheckMask MaskedExt PolyFun MixSummands Interp. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecOpen ExecPublic ExecDerive ExecVerify ExecProveBase ExecSerial.
Import ListNotations.
Local Open Scope list_scope.

Add Field fieldF2f : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Infix "+" := fadd.
Local Infix "*" := fmul.
Local Infix "-" := fsub.
Local Notation fsum := (@fsum Fq2 fzero fadd).
Local Notation peval := (@eval Fq2 fzero fadd fmul).
Local Notation is_poly := (@is_poly Fq2 fzero fadd fmul).
Local Notation nF := (@nF Fq2 fzero fone fadd).
Local Notation gmask := (@gmask Fq2 fzero fadd fmul).
Local Notation gtail := (@gtail Fq2 fzero fadd fmul).
Local Notation uni := (@SumcheckMask.uni Fq2 fzero fadd fmul).
Local Notation p2 := (@p2 Fq2 fone fadd fmul).
Local Notation Wm := (@SumcheckMask.W Fq2 fzero fone fadd fmul).
Local Notation tsum := (@tsum Fq2 fzero fone fadd).
Local Notation rnd := (@rnd Fq2 fzero fone fadd).
Local Notation Zp := (@Zp Fq2 fone fmul fsub).

Lemma ip_mul : forall d1 d2 f g, is_poly d1 f -> is_poly d2 g -> is_poly (d1 + d2) (fun X => f X * g X).
Proof. exact (@is_poly_mul Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). Qed.
Lemma ip_add : forall d1 d2 f g, is_poly d1 f -> is_poly d2 g -> is_poly (Nat.max d1 d2) (fun X => f X + g X).
Proof. exact (@is_poly_add Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). Qed.
Lemma ip_sub : forall d1 d2 f g, is_poly d1 f -> is_poly d2 g -> is_poly (Nat.max d1 d2) (fun X => f X - g X).
Proof. exact (@is_poly_sub Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). Qed.
Lemma ip_scale : forall d c f, is_poly d f -> is_poly d (fun X => c * f X).
Proof. exact (@is_poly_scale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). Qed.
Lemma ip_const : forall d c, is_poly d (fun _ => c).
Proof. exact (@is_poly_const Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). Qed.
Lemma ip_fsum : forall {A : Type} d (phi : A -> F -> F) (l : list A),
  (forall a, In a l -> is_poly d (phi a)) -> is_poly d (fun X => fsum (map (fun a => phi a X) l)).
Proof. intros A. exact (@is_poly_fsum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field A). Qed.
Lemma ip_mono : forall d d' f, (d <= d')%nat -> is_poly d f -> is_poly d' f.
Proof. exact (@is_poly_mono Fq2 fzero fadd fmul). Qed.
Lemma ip_ext : forall d f g, (forall X, f X = g X) -> is_poly d f -> is_poly d g.
Proof. exact (@is_poly_ext Fq2 fzero fadd fmul). Qed.

(* ---------------------------------------------------------------------- *)
(* lists *)

Lemma zipcons_seq : forall {A : Type} (d : A) (g : nat -> list A) (r : list A) s,
  zipcons r (map g (seq s (List.length r))) = map (fun i => nth (i - s) r d :: g i) (seq s (List.length r)).
Proof.
  intros A d g r; induction r as [| x r ih]; intro s; [reflexivity |].
  cbn [List.length seq map zipcons]. rewrite ih. f_equal.
  + rewrite Nat.sub_diag. reflexivity.
  + apply map_ext_in. intros i hi. apply in_seq in hi.
    replace (i - s)%nat with (S (i - S s)) by lia. reflexivity.
Qed.

Lemma transpose_spec : forall {A : Type} (d : A) n (rows : list (list A)),
  Forall (fun r => List.length r = n) rows ->
  transpose n rows = map (fun i => map (fun r => nth i r d) rows) (seq 0 n).
Proof.
  intros A d n rows h. induction h as [| r rows hr hrows ih].
  + unfold transpose. cbn [fold_right map]. clear. generalize 0%nat as s.
    induction n as [| n ih]; intro s; [reflexivity |]. cbn [repeat seq map]. f_equal. apply ih.
  + unfold transpose in *. cbn [fold_right]. rewrite ih, <-hr, (zipcons_seq d). rewrite hr.
    apply map_ext. intro i. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma pairs_length : forall h t, List.length t = (2 * h)%nat -> List.length (pairs t) = h.
Proof.
  induction h as [| h ih]; intros t ht.
  + destruct t; [reflexivity | cbn in ht; lia].
  + destruct t as [| x [| y t]]; cbn in ht; try lia. cbn. f_equal. apply ih. lia.
Qed.

Lemma pairs_nth : forall t i, (S (2 * i) < List.length t)%nat ->
  nth i (pairs t) (xzero, xzero) = (nth (2 * i) t xzero, nth (S (2 * i)) t xzero).
Proof.
  fix ih 1. intros t i hi. destruct t as [| x [| y t]]; cbn in hi; try lia.
  destruct i as [| i]; [reflexivity |]. cbn [pairs nth].
  replace (2 * S i)%nat with (S (S (2 * i))) by lia. cbn [nth]. apply ih. lia.
Qed.

Lemma fsum_app2 : forall l l' : list F, fsum (l ++ l') = fsum l + fsum l'.
Proof. induction l as [| x l ih]; intro l'; cbn; [field | rewrite ih; field]. Qed.

Lemma fsum_seq_pairs : forall (f : nat -> F) h,
  fsum (map f (seq 0 (2 * h))) = fsum (map (fun i => f (2 * i)%nat + f (S (2 * i))) (seq 0 h)).
Proof.
  intros f h. induction h as [| h ih]; [reflexivity |].
  replace (2 * S h)%nat with (2 * h + 2)%nat by lia.
  rewrite seq_app, map_app, fsum_app2, ih, (seq_S h 0), map_app, fsum_app2. cbn [seq map LogDer.fsum]. rewrite ?Nat.add_0_l, ?Nat.add_1_r. field.
Qed.

Lemma seq_nth' : forall n s i d, (i < n)%nat -> nth i (seq s n) d = (s + i)%nat.
Proof. intros. apply seq_nth. assumption. Qed.

(* ---------------------------------------------------------------------- *)
(* the summand at the field *)

Definition extF (a b x : F) : F := a + x * (b - a).

Definition termF (vals : list F) (t : F * list nat) : F :=
  fold_left (fun p i => p * nth i vals fzero) (snd t) (fst t).

Definition termsF (terms : list (F * list nat)) (vals : list F) : F := fsum (map (termF vals) terms).

Definition sF (t : sterm) : F * list nat := (to_F (fst t), snd t).

Definition colF (T : list (list F)) (i : nat) : list F := map (fun t => nth i t fzero) T.

Definition csum (terms : list (F * list nat)) (T : list (list F)) (n : nat) : F :=
  fsum (map (fun i => termsF terms (colF T i)) (seq 0 n)).

Lemma to_F_term : forall vals t, to_F (term_val vals t) = termF (map to_F vals) (sF t).
Proof.
  intros vals [c facs]. unfold term_val, termF, sF. cbn [fst snd].
  revert c; induction facs as [| i facs ih]; intro c; [reflexivity |].
  cbn [fold_left]. rewrite ih, to_F_mul, to_F_nth. reflexivity.
Qed.

Lemma to_F_terms : forall terms vals, to_F (terms_val terms vals) = termsF (map sF terms) (map to_F vals).
Proof.
  intros terms vals. unfold terms_val, termsF. rewrite to_F_fsum, !map_map. f_equal.
  apply map_ext. intro t. apply to_F_term.
Qed.

Lemma to_F_ext : forall p x, to_F (xext p x) = extF (to_F (fst p)) (to_F (snd p)) (to_F x).
Proof. intros [a b] x. unfold xext, extF. cbn [fst snd]. rewrite to_F_add, to_F_mul, to_F_sub. reflexivity. Qed.

Lemma to_F_xfint : forall c, to_F (xfint c) = nF c.
Proof. intro c. unfold xfint. apply to_F_xint_nat. Qed.

(* degree of a term in X, given the degree of each factor *)
Lemma term_poly : forall (V : F -> list F) (dg : nat -> nat) coef facs,
  (forall i, In i facs -> is_poly (dg i) (fun X => nth i (V X) fzero)) ->
  is_poly (list_sum (map dg facs)) (fun X => termF (V X) (coef, facs)).
Proof.
  intros V dg coef facs h. unfold termF. cbn [fst snd].
  assert (gen : forall (acc : F -> F) e, is_poly e acc ->
            is_poly (e + list_sum (map dg facs)) (fun X => fold_left (fun p i => p * nth i (V X) fzero) facs (acc X))).
  { induction facs as [| i facs ih]; intros acc e he.
    + cbn. rewrite Nat.add_0_r. exact he.
    + cbn [fold_left map].
      replace (e + list_sum (dg i :: map dg facs))%nat with ((e + dg i) + list_sum (map dg facs))%nat
        by (simpl; lia).
      apply (ih (fun j hj => h j (or_intror hj)) (fun X => acc X * nth i (V X) fzero) (e + dg i)%nat).
      apply ip_mul; [exact he | apply h; left; reflexivity]. }
  apply (gen (fun _ => coef) 0%nat). apply ip_const.
Qed.

Lemma terms_poly : forall (V : F -> list F) (dg : nat -> nat) terms d,
  (forall t, In t terms -> forall i, In i (snd t) -> is_poly (dg i) (fun X => nth i (V X) fzero)) ->
  (forall t, In t terms -> (list_sum (map dg (snd t)) <= d)%nat) ->
  is_poly d (fun X => termsF terms (V X)).
Proof.
  intros V dg terms d h hd. unfold termsF.
  apply (ip_fsum d (fun t X => termF (V X) t) terms).
  intros [c facs] ht. apply (ip_mono (list_sum (map dg facs))); [exact (hd _ ht) |].
  apply term_poly. intros i hi. exact (h _ ht i hi).
Qed.

Lemma is_poly_extF : forall a b, is_poly 1 (fun X => extF a b X).
Proof.
  intros a b. exists [a; b - a]. split; [cbn; lia |]. intro X. unfold extF. cbn. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the sumcheck mask *)

Lemma peval_one : forall c, peval c fone = fsum c.
Proof. induction c as [| x c ih]; cbn; [reflexivity | rewrite ih; field]. Qed.

Lemma to_F_uni : forall c x, to_F (xuni c x) = uni (map to_F c) (to_F x).
Proof. intros c x. unfold xuni, SumcheckMask.uni. rewrite to_F_mul, to_F_eval. reflexivity. Qed.

Lemma nF_pow2 : forall k, nF (2 ^ k) = p2 k.
Proof.
  induction k as [| k ih]; [cbn; field |].
  rewrite Nat.pow_succ_r', (@nF_double F fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), ih.
  reflexivity.
Qed.

Lemma to_F_pow2 : forall k, to_F (xpow2 k) = p2 k.
Proof.
  intro k. unfold xpow2. rewrite <-nF_pow2, <-to_F_xint_nat. f_equal. f_equal.
  rewrite Nat2Z.inj_pow. reflexivity.
Qed.

Lemma gtail_combine : forall cs x, gtail cs x = fsum (map (fun p => uni (fst p) (snd p)) (combine cs x)).
Proof. induction cs as [| c cs ih]; intros [| xi x]; cbn; try reflexivity. rewrite ih. reflexivity. Qed.

Lemma fsum_concat : forall l : list (list F), fsum (List.concat l) = fsum (map fsum l).
Proof. induction l as [| x l ih]; cbn; [reflexivity |]. rewrite fsum_app2, ih. reflexivity. Qed.

Lemma W_formula : forall cs, Wm cs = match cs with [] => fzero | _ => p2 (List.length cs - 1) * fsum (List.concat cs) end.
Proof.
  induction cs as [| c cs ih]; [reflexivity |].
  cbn [SumcheckMask.W List.length]. rewrite ih. unfold SumcheckMask.uni. rewrite peval_one.
  destruct cs as [| c' cs'].
  + cbn [List.concat List.length]. rewrite app_nil_r. replace (1 - 1)%nat with 0%nat by reflexivity.
    cbn [p2]. unfold two. field.
  + cbn [List.concat List.length]. rewrite !fsum_app2. replace (S (S (List.length cs')) - 1)%nat with (S (List.length cs')) by lia.
    replace (S (List.length cs') - 1)%nat with (List.length cs') by lia. cbn [p2]. unfold two. field.
Qed.

Lemma to_F_concat : forall l : list (list xf), map to_F (List.concat l) = List.concat (map (map to_F) l).
Proof. induction l as [| x l ih]; cbn; [reflexivity |]. rewrite map_app, ih. reflexivity. Qed.

Definition csF (cs : list (list xf)) : list (list F) := map (map to_F) cs.

Theorem to_F_mtotal : forall a0 cs, cs <> [] ->
  to_F (mtotal a0 cs) = tsum (gmask (to_F a0) (csF cs)) [] (List.length cs).
Proof.
  intros a0 cs hne. unfold csF.
  rewrite <-(length_map (map to_F) cs).
  rewrite (@mask_tsum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), W_formula.
  unfold mtotal. rewrite to_F_add, !to_F_mul, !to_F_pow2, to_F_fsum, to_F_concat, length_map.
  destruct cs as [| c cs]; [contradiction |]. cbn [map]. field.
Qed.

Theorem to_F_mvalue : forall a0 cs j point c, List.length point = j -> (j < List.length cs)%nat ->
  to_F (mvalue a0 cs j point c) = rnd (gmask (to_F a0) (csF cs)) (map to_F point) (List.length cs - j - 1) (nF c).
Proof.
  intros a0 cs j point c hp hj. unfold csF.
  assert (hs : map (map to_F) cs = map (map to_F) (firstn j cs) ++ map to_F (nth j cs []) :: map (map to_F) (skipn (S j) cs)).
  { rewrite <-(firstn_skipn j cs) at 1. rewrite map_app. f_equal.
    rewrite (skipn_nth_cons cs j []) by exact hj. reflexivity. }
  rewrite hs.
  replace (List.length cs - j - 1)%nat with (List.length (map (map to_F) (skipn (S j) cs)))
    by (rewrite length_map, length_skipn; lia).
  rewrite <-(@mask_round_poly Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field)
    by (rewrite !length_map, length_firstn; lia).
  cbn [eval]. rewrite (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), W_formula.
  unfold mvalue. rewrite !length_map, length_skipn.
  set (rem := (List.length cs - j - 1)%nat).
  replace (List.length cs - S j)%nat with rem by (unfold rem; lia).
  rewrite gtail_combine, <-(map_map (map to_F) (fun c => c)).
  assert (hb : to_F (xadd a0 (xfsum (map (fun p => xuni (fst p) (snd p)) (combine (firstn j cs) point))))
               = to_F a0 + fsum (map (fun p => uni (fst p) (snd p)) (combine (map (map to_F) (firstn j cs)) (map to_F point)))).
  { rewrite to_F_add, to_F_fsum, map_map. f_equal. clear.
    generalize (firstn j cs). intro l. revert point. induction l as [| x l ih]; intros [| y pt]; cbn; try reflexivity.
    rewrite to_F_uni, ih. reflexivity. }
  rewrite map_id.
  destruct (Nat.leb 1 rem) eqn:e.
  + apply Nat.leb_le in e. rewrite to_F_add, to_F_mul, to_F_add, hb, to_F_uni, to_F_xfint, !to_F_mul, !to_F_pow2, to_F_fsum.
    rewrite to_F_concat.
    destruct (skipn (S j) cs) as [| c1 cs1] eqn:es.
    - exfalso. assert (List.length (skipn (S j) cs) = 0%nat) by (rewrite es; reflexivity). rewrite length_skipn in H. unfold rem in e. lia.
    - cbn [map List.length]. replace (S (List.length (map (map to_F) cs1)) - 1)%nat with (rem - 1)%nat.
      * unfold SumcheckMask.uni. field.
      * assert (List.length (skipn (S j) cs) = S (List.length cs1)) by (rewrite es; reflexivity).
        rewrite length_skipn in H. rewrite length_map. unfold rem. lia.
  + apply Nat.leb_gt in e. rewrite to_F_mul, to_F_add, hb, to_F_uni, to_F_xfint, to_F_pow2.
    destruct (skipn (S j) cs) as [| c1 cs1] eqn:es.
    - cbn [map]. unfold SumcheckMask.uni. field.
    - exfalso. assert (List.length (skipn (S j) cs) = S (List.length cs1)) by (rewrite es; reflexivity).
      rewrite length_skipn in H. unfold rem in e. lia.
Qed.

(* ---------------------------------------------------------------------- *)
(* folding and multilinear extensions *)

Lemma flat_map_const_length' : forall {A B : Type} (c : nat) (f : A -> list B) (l : list A),
  (forall x, List.length (f x) = c) -> List.length (flat_map f l) = (c * List.length l)%nat.
Proof.
  intros A B c f l h. induction l as [| x l ih]; [cbn; lia |].
  cbn [flat_map List.length]. rewrite length_app, h, ih. lia.
Qed.

Lemma xeq_table_length : forall r, List.length (xeq_table r) = (2 ^ List.length r)%nat.
Proof.
  induction r as [| r0 r ih]; [reflexivity |]. cbn [xeq_table List.length].
  rewrite (flat_map_const_length' 2) by reflexivity. rewrite ih. cbn [Nat.pow]. lia.
Qed.

Lemma dot_fold : forall r0 e t, List.length t = (2 * List.length e)%nat ->
  to_F (xdot t (flat_map (fun x => [xmul x (xsub xone r0); xmul x r0]) e)) = to_F (xdot (xfold t r0) e).
Proof.
  intros r0. induction e as [| x e ih]; intros t ht.
  + destruct t; [reflexivity | cbn in ht; lia].
  + destruct t as [| a [| b t]]; cbn in ht; try lia.
    cbn [flat_map app xdot]. unfold xfold. cbn [pairs map xdot]. fold (xfold t r0).
    rewrite !to_F_add, !to_F_mul, ih by lia. rewrite to_F_ext. cbn [fst snd].
    rewrite ?to_F_mul, ?to_F_sub, ?to_F_one. unfold extF. field.
Qed.

Lemma mle_fold : forall t r0 rs, List.length t = (2 * 2 ^ List.length rs)%nat ->
  to_F (xmle t (r0 :: rs)) = to_F (xmle (xfold t r0) rs).
Proof.
  intros t r0 rs ht. unfold xmle. cbn [xeq_table]. apply dot_fold. rewrite xeq_table_length. exact ht.
Qed.

Lemma length_xfold : forall h t r, List.length t = (2 * h)%nat -> List.length (xfold t r) = h.
Proof. intros h t r ht. unfold xfold. rewrite length_map. apply pairs_length. exact ht. Qed.

(* ---------------------------------------------------------------------- *)
(* one round at the field *)

Definition lastF (zprev : F) (t : list F) (mk : option F) (x : F) : F :=
  extF (nth 0 t fzero) (nth 1 t fzero) x + match mk with Some a => a * zprev * (x * (fone - x)) | None => fzero end.

Lemma to_F_last_uni : forall zprev t mk x,
  to_F (last_uni zprev t mk x) = lastF (to_F zprev) (map to_F t) (option_map to_F mk) (to_F x).
Proof.
  intros zprev t mk x. unfold last_uni, lastF. rewrite <-!to_F_nth.
  destruct mk as [a |]; cbn [option_map].
  + rewrite to_F_add, to_F_ext, !to_F_mul, to_F_sub, to_F_one. reflexivity.
  + rewrite to_F_ext. cbn [fst snd]. unfold extF. field.
Qed.

Definition coreF (terms : list (F * list nat)) (T : list (list F)) (h : nat) (X : F) : F :=
  fsum (map (fun i => termsF terms (map (fun t => extF (nth (2 * i) t fzero) (nth (S (2 * i)) t fzero) X) T)) (seq 0 h)).

Definition lastcore (terms : list (F * list nat)) (zprev : F) (T : list (list F)) (mks : list (option F)) (X : F) : F :=
  termsF terms (map (fun p => lastF zprev (fst p) (snd p) X) (combine T mks)).

Definition tF (tables : list (list xf)) : list (list F) := map (map to_F) tables.
Definition mF (tmask : list (option xf)) : list (option F) := map (option_map to_F) tmask.

Lemma to_F_round_val : forall terms tables h c, Forall (fun t => List.length t = (2 * h)%nat) tables ->
  to_F (round_val terms (transpose h (map pairs tables)) c) = coreF (map sF terms) (tF tables) h (nF c).
Proof.
  intros terms tables h c hT. rewrite (transpose_spec (xzero, xzero)).
  + unfold round_val, coreF. rewrite to_F_fsum, !map_map. f_equal. apply map_ext_in. intros i hi. apply in_seq in hi.
    rewrite to_F_terms, !map_map. f_equal. unfold tF. rewrite map_map. apply map_ext_in. intros t ht.
    rewrite Forall_forall in hT. specialize (hT t ht).
    rewrite pairs_nth by lia. rewrite to_F_ext, to_F_xfint. cbn [fst snd]. rewrite !to_F_nth. reflexivity.
  + apply Forall_map. eapply Forall_impl; [| exact hT]. intros t ht. apply pairs_length. exact ht.
Qed.

Lemma combine_map2 : forall {A B C D : Type} (f : A -> C) (g : B -> D) l l',
  combine (map f l) (map g l') = map (fun p => (f (fst p), g (snd p))) (combine l l').
Proof. intros A B C D f g; induction l as [| x l ih]; intros [| y l']; cbn; try reflexivity. rewrite ih. reflexivity. Qed.

Lemma to_F_last_vals : forall terms zprev tables tmask c,
  to_F (terms_val terms (last_vals zprev tables tmask c))
  = lastcore (map sF terms) (to_F zprev) (tF tables) (mF tmask) (to_F c).
Proof.
  intros. unfold last_vals, lastcore. rewrite to_F_terms, map_map. f_equal.
  unfold tF, mF. rewrite combine_map2, map_map. apply map_ext. intros [t mk]. cbn [fst snd]. apply to_F_last_uni.
Qed.

Lemma fsum_map_add : forall {A : Type} (f g : A -> F) l, fsum (map f l) + fsum (map g l) = fsum (map (fun a => f a + g a) l).
Proof. intros A f g l. induction l as [| x l ih]; cbn; [field | rewrite <-ih; field]. Qed.

Lemma coreF_01 : forall terms T h, Forall (fun t => List.length t = (2 * h)%nat) T ->
  coreF terms T h fzero + coreF terms T h fone = csum terms T (2 * h).
Proof.
  intros terms T h hT. unfold coreF, csum. rewrite fsum_seq_pairs, fsum_map_add.
  apply (@fsum_map_ext F fzero fadd). intros i _. unfold colF. f_equal; f_equal; apply map_ext; intro t; unfold extF; field.
Qed.

Lemma colF_fold : forall tables r h i, Forall (fun t => List.length t = (2 * h)%nat) tables -> (i < h)%nat ->
  colF (tF (map (fun t => xfold t r) tables)) i
  = map (fun t => extF (nth (2 * i) t fzero) (nth (S (2 * i)) t fzero) (to_F r)) (tF tables).
Proof.
  intros tables r h i hT hi. unfold colF, tF. rewrite !map_map. apply map_ext_in. intros t ht.
  rewrite Forall_forall in hT. specialize (hT t ht).
  rewrite <-!to_F_nth.
  rewrite (nth_indep _ xzero (xext (xzero, xzero) r)) by (rewrite (length_xfold h); lia).
  unfold xfold. rewrite (map_nth (fun p => xext p r) (pairs t) (xzero, xzero) i), pairs_nth by lia.
  rewrite to_F_ext. cbn [fst snd].
  rewrite !to_F_nth. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the verifier's interpolation lands on the round polynomial *)

Lemma spoints_length : forall d, (1 <= d)%nat -> List.length (spoints d) = d.
Proof. intros d hd. unfold spoints. cbn [List.length]. rewrite length_seq. lia. Qed.

Lemma interp_step : forall (P : F -> F) d vals claim r,
  (1 <= d <= DMAX)%nat -> is_poly d P ->
  map to_F vals = map (fun c => P (nF c)) (spoints d) ->
  P fzero + P fone = to_F claim ->
  to_F (xinterp (xfullvals claim vals) r) = P (to_F r).
Proof.
  intros P d vals claim r hd (p & hp & ep) hv hs.
  rewrite to_F_interp, to_F_fullvals, hv. unfold spoints. cbn [map Interp.fullvals].
  rewrite <-(ep (to_F r)).
  apply (@interp_unique Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field DMAX
           (Fq2_char_upto DMAX ltac:(vm_compute; reflexivity))).
  - cbn [List.length]. rewrite length_map, length_seq. lia.
  - cbn [List.length]. rewrite length_map, length_seq. lia.
  - intros k hk. cbn [List.length] in hk. rewrite length_map, length_seq in hk.
    destruct k as [| [| k]].
    + cbn [nth]. rewrite ep. reflexivity.
    + cbn [nth]. rewrite <-hs, ep. replace (nF 1) with fone by (cbn; field). cbn [nF]. field.
    + cbn [nth]. rewrite (nth_indep _ fzero (P (nF 0))) by (rewrite length_map, length_seq; lia).
      rewrite (map_nth (fun c => P (nF c)) (seq 2 (d - 1)) 0%nat k), seq_nth by lia. rewrite ep. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the last round at the field *)

Lemma lastF_0 : forall z t mk, lastF z t mk fzero = nth 0 t fzero.
Proof. intros z t [a |]; unfold lastF, extF; field. Qed.

Lemma lastF_1 : forall z t mk, lastF z t mk fone = nth 1 t fzero.
Proof. intros z t [a |]; unfold lastF, extF; field. Qed.

Lemma map_fst_combine : forall {A B : Type} (l : list A) (l' : list B), List.length l = List.length l' ->
  map fst (combine l l') = l.
Proof. intros A B l; induction l as [| x l ih]; intros [| y l'] h; cbn in h |- *; try lia; [reflexivity |]. rewrite ih by lia. reflexivity. Qed.

Lemma lastcore_01 : forall terms z T M, List.length T = List.length M ->
  lastcore terms z T M fzero + lastcore terms z T M fone = csum terms T 2.
Proof.
  intros terms z T M hl. unfold lastcore, csum, colF. cbn [seq map LogDer.fsum].
  rewrite (map_ext (fun p => lastF z (fst p) (snd p) fzero) (fun p => nth 0 (fst p) fzero)) by (intro; apply lastF_0).
  rewrite (map_ext (fun p => lastF z (fst p) (snd p) fone) (fun p => nth 1 (fst p) fzero)) by (intro; apply lastF_1).
  rewrite <-!(map_map fst (fun t => nth _ t fzero)), map_fst_combine by exact hl. field.
Qed.

Lemma lastF_poly : forall z t mk, is_poly (match mk with Some _ => 2 | None => 1 end) (fun X => lastF z t mk X).
Proof.
  intros z t [a |]; unfold lastF.
  + apply (ip_mono (Nat.max 1 2)); [lia |]. apply ip_add; [apply is_poly_extF |].
    exists [fzero; a * z; fzero - a * z]. split; [cbn; lia |]. intro X. cbn. field.
  + apply (ip_ext 1 (fun X => extF (nth 0 t fzero) (nth 1 t fzero) X)); [intro; field | apply is_poly_extF].
Qed.

Lemma nth_combine_map : forall {A B C : Type} (f : A * B -> C) (l : list A) (l' : list B) i da db dc,
  List.length l = List.length l' -> (i < List.length l)%nat ->
  nth i (map f (combine l l')) dc = f (nth i l da, nth i l' db).
Proof.
  intros A B C f l l' i da db dc hl hi.
  rewrite (nth_indep _ dc (f (da, db))) by (rewrite length_map, length_combine; lia).
  rewrite map_nth, combine_nth by exact hl. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the rounds *)

Section Complete.

  Variable draw : chal -> bytes -> option (list xf * chal).
  Variable name : string.
  Variable tmask : list (option xf).
  Variable terms : list sterm.
  Variables (a0 : xf) (cs : list (list xf)) (rho : xf).

  Local Notation TF := (map sF terms).
  Local Notation gF := (gmask (to_F a0) (csF cs)).

  Definition mdeg (i : nat) : nat := match nth i tmask None with Some _ => 2 | None => 1 end.

  Definition round_ok (j d : nat) (last : bool) : Prop :=
    (1 <= d <= DMAX)%nat /\ (List.length (nth j cs []) <= d)%nat /\
    forall t, In t terms -> ((if last then list_sum (map mdeg (snd t)) else List.length (snd t)) <= d)%nat.

  Definition maskv (k : nat) : F := match nth k tmask None with Some a => to_F a | None => fzero end.

  Lemma mask_poly : forall j pre k d, List.length pre = j -> List.length cs = (j + S k)%nat ->
    (List.length (nth j cs []) <= d)%nat -> is_poly d (fun X => rnd gF pre k X).
  Proof.
    intros j pre k d hp hc hd.
    apply (@rnd_is_poly Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). intros b _.
    apply (@gmask_is_poly Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    + unfold csF. rewrite length_map. lia.
    + unfold csF. rewrite hp.
      replace (nth j (map (map to_F) cs) []) with (map to_F (nth j cs [])) by (symmetry; exact (map_nth (map to_F) cs [] j)).
      rewrite length_map. exact hd.
  Qed.

  Lemma vals_ok : forall (f g : nat -> xf) d, (1 <= d)%nat ->
    msg_ok (map (fun c => xadd (f c) (g c)) (spoints d)) d.
  Proof.
    intros f g d hd. split; [rewrite length_map; apply spoints_length; exact hd |].
    apply Forall_map, Forall_forall. intros. apply xadd_reduced.
  Qed.

  Lemma tF_length : forall tables, List.length (tF tables) = List.length tables.
  Proof. intro. unfold tF. apply length_map. Qed.

  Theorem sc_loop_complete : forall ds j tables point ch msgs pt fin ch' claim,
    ds <> [] -> tables <> [] ->
    List.length cs = (j + List.length ds)%nat ->
    (forall i, (i < List.length ds)%nat -> round_ok (j + i) (nth i ds 0%nat) (Nat.eqb (S i) (List.length ds))) ->
    List.length point = j ->
    Forall (fun t => List.length t = (2 ^ List.length ds)%nat) tables ->
    List.length tmask = List.length tables ->
    to_F claim = csum TF (tF tables) (2 ^ List.length ds) + to_F rho * tsum gF (map to_F point) (List.length ds) ->
    sc_loop draw name tmask terms a0 cs rho ds j tables point ch = Some (msgs, pt, fin, ch') ->
    (exists c, xsc_verify msgs (skipn j pt) claim = Some c
               /\ to_F c = termsF TF (map to_F fin) + to_F rho * gF (map to_F pt))
    /\ sc_chalsG draw name j msgs ch = Some (skipn j pt, ch')
    /\ firstn j pt = point /\ List.length pt = (j + List.length ds)%nat
    /\ Forall2 msg_ok msgs ds
    /\ (forall k, (k < List.length tables)%nat ->
          to_F (nth k fin xzero) = to_F (xmle (nth k tables []) (skipn j pt)) + maskv k * Zp (map to_F pt)).
  Proof.
    induction ds as [| d ds ih]; intros j tables point ch msgs pt fin ch' claim hne htne hcs hrok hpt hT htm hclaim H;
      [contradiction |].
    cbn [sc_loop] in H.
    set (k := List.length ds) in *.
    assert (hok := hrok 0%nat ltac:(cbn; lia)). rewrite Nat.add_0_r in hok. cbn [nth] in hok.
    destruct hok as (hd & hcd & hterms).
    assert (hT2 : Forall (fun t => List.length t = (2 * 2 ^ k)%nat) tables)
      by (eapply Forall_impl; [| exact hT]; intros t ht; rewrite ht; cbn [List.length Nat.pow]; reflexivity).
    set (zprev := xzval point) in *.
    set (pre := map to_F point) in *.
    set (vals := map _ (spoints d)) in H.
    destruct (draw _ _) as [[rl chr] |] eqn:hg; cbn [bindo] in H; [| discriminate].
    cbn [fst snd] in H. set (r := nth 0 rl xzero) in *.
    assert (hjc : (j < List.length cs)%nat) by (rewrite hcs; cbn; lia).
    assert (hmv : forall c, to_F (mvalue a0 cs j point c) = rnd gF pre k (nF c)).
    { intro c. rewrite to_F_mvalue by assumption. f_equal. rewrite hcs. cbn [List.length]. lia. }
    assert (hmp : is_poly d (fun X => rnd gF pre k X))
      by (apply (mask_poly j); [unfold pre; rewrite length_map; exact hpt | rewrite hcs; reflexivity | exact hcd]).
    assert (hvne : vals <> []) by (unfold vals, spoints; cbn [map]; discriminate).
    destruct ds as [| d' ds'] eqn:eds.
    - (* last round *)
      cbn [List.length] in k. subst k.
      injection H as <- <- <- <-.
      set (P := fun X => lastcore TF (to_F zprev) (tF tables) (mF tmask) X + to_F rho * rnd gF pre 0 X).
      assert (hv : map to_F vals = map (fun c => P (nF c)) (spoints d)).
      { unfold vals. rewrite map_map. apply map_ext. intro c. rewrite to_F_add, to_F_mul, hmv, to_F_last_vals, to_F_xfint.
        reflexivity. }
      assert (hP : is_poly d P).
      { apply (ip_mono (Nat.max d d)); [lia |]. apply ip_add; [| apply ip_scale; exact hmp].
        unfold lastcore. apply (terms_poly _ mdeg).
        + intros t _ i _. destruct (Nat.lt_ge_cases i (List.length tables)) as [hi | hi].
          * apply (ip_ext _ (fun X => lastF (to_F zprev) (nth i (tF tables) []) (nth i (mF tmask) None) X)).
            { intro X. rewrite (nth_combine_map _ _ _ i [] None) by (unfold tF, mF; rewrite !length_map; lia).
              reflexivity. }
            unfold mF, mdeg. replace (nth i (map (option_map to_F) tmask) None) with (option_map to_F (nth i tmask None))
              by (symmetry; exact (map_nth (option_map to_F) tmask None i)).
            destruct (nth i tmask None) as [x |]; cbn [option_map];
              [exact (lastF_poly _ _ (Some (to_F x))) | exact (lastF_poly _ _ None)].
          * apply (ip_ext _ (fun _ => fzero)); [| apply ip_const]. intro X.
            rewrite nth_overflow by (rewrite length_map, length_combine, tF_length; unfold mF; rewrite length_map; lia).
            reflexivity.
        + intros t ht. apply in_map_iff in ht. destruct ht as (t0 & <- & ht0). cbn [snd sF].
          specialize (hterms t0 ht0). cbn in hterms. exact hterms. }
      assert (hs : P fzero + P fone = to_F claim).
      { unfold P. rewrite hclaim. change (List.length [d]) with 1%nat. change (2 ^ 1)%nat with 2%nat.
        rewrite (@tsum_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
        transitivity ((lastcore TF (to_F zprev) (tF tables) (mF tmask) fzero + lastcore TF (to_F zprev) (tF tables) (mF tmask) fone)
                      + to_F rho * (rnd gF pre 0 fzero + rnd gF pre 0 fone)); [field |].
        rewrite lastcore_01 by (unfold tF, mF; rewrite !length_map; symmetry; exact htm). reflexivity. }
      assert (hfin : to_F (xinterp (xfullvals claim vals) r) = P (to_F r)) by (apply (interp_step P d); assumption).
      assert (hpt' : skipn j (point ++ [r]) = [r]) by (rewrite skipn_app, hpt, Nat.sub_diag, skipn_all2 by lia; reflexivity).
      split; [| split; [| split; [| split; [| split]]]].
      + rewrite hpt'. exists (xinterp (xfullvals claim vals) r). split.
        * cbn [xsc_verify]. destruct vals as [| v0 vs]; [contradiction | reflexivity].
        * rewrite hfin. unfold P. f_equal.
          -- unfold lastcore, last_vals. rewrite map_map. f_equal. unfold tF, mF. rewrite combine_map2, map_map.
             apply map_ext. intros [t mk]. cbn [fst snd]. symmetry. apply to_F_last_uni.
          -- f_equal. rewrite (@rnd_snoc Fq2 fzero fone fadd gF), (@tsum_0 Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field gF).
             unfold pre. rewrite map_app. reflexivity.
      + rewrite hpt'. cbn [sc_chalsG]. rewrite hg. reflexivity.
      + rewrite firstn_app, hpt, Nat.sub_diag, firstn_all2 by lia. cbn [firstn]. apply app_nil_r.
      + rewrite length_app, hpt. reflexivity.
      + constructor; [apply vals_ok; lia | constructor].
      + intros kk hk. rewrite hpt'.
        unfold last_vals. rewrite (nth_combine_map _ _ _ kk [] None) by (exact htm || lia).
        cbn [fst snd]. rewrite to_F_last_uni. unfold lastF, maskv.
        rewrite Forall_forall in hT. assert (hl2 := hT (nth kk tables []) (nth_In _ _ hk)). cbn [List.length Nat.pow] in hl2.
        unfold xmle. cbn [xeq_table flat_map app].
        destruct (nth kk tables []) as [| t0 [| t1 [| t2 tr]]]; cbn in hl2; try lia.
        cbn [xdot nth map]. rewrite map_app, (@Zp_app Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
        unfold zprev. rewrite to_F_zval. fold pre. cbn [map MaskedExt.Zp].
        destruct (nth kk tmask None) as [a |]; cbn [option_map];
          rewrite ?to_F_add, ?to_F_mul, ?to_F_sub, ?to_F_one, ?to_F_zero; unfold extF; field.
    - (* a first round *)
      assert (hdsne : ds <> []) by (rewrite eds; discriminate).
      unfold k in *. clear k. rewrite <-eds in *. clear eds. set (k := List.length ds) in *. set (h := (2 ^ k)%nat) in *.
      assert (hh : List.length (pairs (nth 0 tables [])) = h).
      { destruct tables as [| t0 tr]; [contradiction |]. apply pairs_length. inversion hT2; assumption. }
      set (P := fun X => coreF TF (tF tables) h X + to_F rho * rnd gF pre k X).
      assert (hv : map to_F vals = map (fun c => P (nF c)) (spoints d)).
      { unfold vals. rewrite map_map. apply map_ext. intro c. cbv zeta. rewrite hh.
        rewrite to_F_add, to_F_mul, hmv, to_F_round_val by exact hT2. reflexivity. }
      assert (hP : is_poly d P).
      { apply (ip_mono (Nat.max d d)); [lia |]. apply ip_add; [| apply ip_scale; exact hmp].
        unfold coreF. apply (ip_fsum d (fun i X => termsF TF _) (seq 0 h)). intros i _.
        apply (terms_poly _ (fun _ => 1%nat)).
        + intros t _ i' _. destruct (Nat.lt_ge_cases i' (List.length (tF tables))) as [hi | hi].
          * apply (ip_ext _ (fun X => extF (nth (2 * i) (nth i' (tF tables) []) fzero) (nth (S (2 * i)) (nth i' (tF tables) []) fzero) X));
              [| apply is_poly_extF].
            intro X. rewrite (nth_indep (map (fun t0 => extF (nth (2 * i) t0 fzero) (nth (S (2 * i)) t0 fzero) X) (tF tables))
                                fzero (extF (nth (2 * i) [] fzero) (nth (S (2 * i)) [] fzero) X))
              by (rewrite length_map; exact hi).
            rewrite (map_nth (fun t0 => extF (nth (2 * i) t0 fzero) (nth (S (2 * i)) t0 fzero) X)). reflexivity.
          * apply (ip_ext _ (fun _ => fzero)); [| apply ip_const]. intro X.
            rewrite nth_overflow by (rewrite length_map; lia). reflexivity.
        + intros t ht. apply in_map_iff in ht. destruct ht as (t0 & <- & ht0). cbn [snd sF].
          specialize (hterms t0 ht0).
          assert (hlast : Nat.eqb 1 (List.length (d :: ds)) = false).
          { apply Nat.eqb_neq. clear -hdsne. destruct ds as [| x y]; [contradiction | cbn [List.length]; lia]. }
          rewrite hlast in hterms. cbv iota in hterms.
          assert (h1 : forall l : list nat, list_sum (map (fun _ => 1%nat) l) = List.length l)
            by (clear; induction l as [| x l ihl]; [reflexivity | simpl; rewrite ihl; reflexivity]).
          rewrite h1. exact hterms. }
      assert (hs : P fzero + P fone = to_F claim).
      { unfold P. rewrite hclaim.
        transitivity ((coreF TF (tF tables) h fzero + coreF TF (tF tables) h fone)
                      + to_F rho * (rnd gF pre k fzero + rnd gF pre k fone)); [field |].
        rewrite coreF_01
          by (unfold tF; apply Forall_map; eapply Forall_impl; [| exact hT2]; intros t ht; rewrite length_map; exact ht).
        rewrite <-(@tsum_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). reflexivity. }
      assert (hfin : to_F (xinterp (xfullvals claim vals) r) = P (to_F r)) by (apply (interp_step P d); assumption).
      destruct (sc_loop draw name tmask terms a0 cs rho ds (S j) (map (fun t => xfold t r) tables) (point ++ [r]) chr)
        as [[[[ms pt0] fin0] ch0] |] eqn:hrec; cbn [bindo] in H; [| discriminate].
      injection H as <- <- <- <-.
      assert (hT' : Forall (fun t => List.length t = (2 ^ List.length ds)%nat) (map (fun t => xfold t r) tables)).
      { apply Forall_map. eapply Forall_impl; [| exact hT2]. intros t ht. apply (length_xfold h). exact ht. }
      assert (hclaim' : to_F (xinterp (xfullvals claim vals) r)
                        = csum TF (tF (map (fun t => xfold t r) tables)) (2 ^ List.length ds)
                          + to_F rho * tsum gF (map to_F (point ++ [r])) (List.length ds)).
      { rewrite hfin. unfold P. f_equal.
        + unfold coreF, csum. fold k h. apply (@fsum_map_ext F fzero fadd). intros i hi. apply in_seq in hi.
          rewrite (colF_fold tables r h i hT2) by lia. reflexivity.
        + f_equal. rewrite (@rnd_snoc Fq2 fzero fone fadd gF). unfold pre. rewrite map_app. reflexivity. }
      destruct (ih (S j) (map (fun t => xfold t r) tables) (point ++ [r]) chr ms pt0 fin0 ch0
                  (xinterp (xfullvals claim vals) r))
        as ((c & hv1 & hv2) & hc1 & hc2 & hc3 & hc4 & hc5).
      + exact hdsne.
      + intro e. apply map_eq_nil in e. contradiction.
      + rewrite hcs. cbn [List.length]. lia.
      + intros i hi. specialize (hrok (S i) ltac:(cbn [List.length]; lia)).
        replace (j + S i)%nat with (S j + i)%nat in hrok by lia. cbn [nth List.length] in hrok. exact hrok.
      + rewrite length_app, hpt. cbn. lia.
      + exact hT'.
      + rewrite length_map. exact htm.
      + exact hclaim'.
      + exact hrec.
      + assert (hlen : List.length pt0 = (j + List.length (d :: ds))%nat) by (rewrite hc3; cbn [List.length]; lia).
        assert (hnth : nth j pt0 xzero = r).
        { rewrite <-(firstn_skipn (S j) pt0), app_nth1 by (rewrite length_firstn; lia).
          rewrite hc2, app_nth2 by lia. rewrite hpt, Nat.sub_diag. reflexivity. }
        assert (hsk : skipn j pt0 = r :: skipn (S j) pt0).
        { rewrite (skipn_nth_cons pt0 j xzero) by lia. rewrite hnth. reflexivity. }
        split; [| split; [| split; [| split; [| split]]]].
        * exists c. split; [| exact hv2]. rewrite hsk. cbn [xsc_verify].
          destruct vals as [| v0 vs]; [contradiction | exact hv1].
        * rewrite hsk. cbn [sc_chalsG]. rewrite hg. cbn [bindo fst snd]. rewrite hc1. reflexivity.
        * replace (firstn j pt0) with (firstn j (firstn (S j) pt0)) by (rewrite firstn_firstn, Nat.min_l by lia; reflexivity).
          rewrite hc2, firstn_app, hpt, Nat.sub_diag.
          cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia.
        * exact hlen.
        * constructor; [apply vals_ok; lia | exact hc4].
        * intros kk hk. rewrite (hc5 kk) by (rewrite length_map; exact hk).
          match goal with |- ?A + ?M = ?B + ?M => cut (A = B); [intro e; rewrite e; reflexivity |] end.
          replace (nth kk (map (fun t => xfold t r) tables) []) with (xfold (nth kk tables []) r)
            by (rewrite (nth_indep (map (fun t => xfold t r) tables) [] (xfold [] r)) by (rewrite length_map; exact hk);
                symmetry; exact (map_nth (fun t => xfold t r) tables [] kk)).
          rewrite hsk. symmetry. apply mle_fold.
          rewrite Forall_forall in hT2. rewrite (hT2 _ (nth_In _ _ hk)).
          rewrite length_skipn, hc3. unfold h. f_equal. f_equal. lia.
  Qed.

End Complete.
