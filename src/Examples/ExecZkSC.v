(* The extracted sumcheck prover against the model (zero knowledge for the
   running code, step 1).

   sc_loop (ExecProveBase.v) sends, in every round, the values of a
   polynomial at 0, 2, .., d, computed from the current (folded) tables.
   Here: those values are the round polynomial of the masked summand of the
   ORIGINAL tables,

     Sfull x = sum over terms of coef * prod_i (mle T_i x + mask_i * Z(x)),

   plus rho times the round polynomial of the sumcheck mask, at the nodes
   (sc_loop_msgs). The ingredients: folding a table at r is evaluating its
   multilinear extension at r in the first free variable (fold_mle,
   foldx_entry); a multilinear extension is affine in each variable
   (mle_affine); off the last round the cube point makes Z vanish, so the
   masks drop out of the first rounds. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic CubeIndex Sumcheck SumcheckMask MaskedExt LayoutLemmas Interp ZkBlocks ZkSumcheck.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecPublic ExecVerify ExecProveBase ExecFold.
Import ListNotations.

Add Field fieldF2zs : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation bidx2 := (@RowLayout.bidx Fq2 fone Fq2_dec).
Local Notation cube2 := (@Mle.cube Fq2 fzero fone).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).
Local Notation nF := (@nF Fq2 fzero fone fadd).

(* ---------------------------------------------------------------------- *)
(* folding is evaluation in the first variable *)

Definition fold1 (t : list F) (r : F) (h : nat) : list F :=
  map (fun i => extF (nth (2 * i) t fzero) (nth (S (2 * i)) t fzero) r) (seq 0 h).

Lemma nth_fold1 : forall t r h i, (i < h)%nat ->
  nth i (fold1 t r h) fzero = extF (nth (2 * i) t fzero) (nth (S (2 * i)) t fzero) r.
Proof.
  intros t r h i hi. unfold fold1.
  rewrite (nth_indep _ fzero (extF (nth (2 * 0) t fzero) (nth (S (2 * 0)) t fzero) r)) by (rewrite length_map, length_seq; exact hi).
  rewrite (map_nth (fun i => extF (nth (2 * i) t fzero) (nth (S (2 * i)) t fzero) r)), seq_nth by exact hi. reflexivity.
Qed.

Lemma bidx_cons : forall c b, bidx2 (c :: b) = ((if Fq2_dec c fone then 1 else 0) + 2 * bidx2 b)%nat.
Proof. reflexivity. Qed.

Lemma bidx_cube_lt : forall n b, In b (cube2 n) -> (bidx2 b < 2 ^ n)%nat.
Proof.
  intros n b hb. pose proof (@RowLayout.bidx_lt Fq2 fone Fq2_dec b) as h.
  rewrite (@cube_length Fq2 fzero fone n b hb) in h. exact h.
Qed.

Lemma zero_neq_one : fzero <> fone.
Proof. intro e. apply (@CubeIndex.one_neq_zero Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). symmetry. exact e. Qed.

Lemma fold_mle : forall n (t : list F) r x, length t = (2 * 2 ^ n)%nat -> length x = n ->
  mle2 (S n) (tabOf t) (r :: x) = mle2 n (tabOf (fold1 t r (2 ^ n))) x.
Proof.
  intros n t r x ht hx. rewrite (@mle_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
  rewrite <-(@mle_scale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
          <-(@mle_scale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
          <-(@mle_add Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
  apply (@mle_ext Fq2 fzero fone fadd fmul fsub). intros b hb.
  pose proof (bidx_cube_lt n b hb) as hl.
  unfold tabOf. rewrite !bidx_cons. destruct (Fq2_dec fzero fone) as [e | _]; [exfalso; exact (zero_neq_one e) |].
  destruct (Fq2_dec fone fone) as [_ | ne]; [| exfalso; apply ne; reflexivity].
  rewrite nth_fold1 by exact hl. unfold extF. cbn [Nat.add]. replace (S (2 * bidx2 b)) with (1 + 2 * bidx2 b)%nat by lia. field.
Qed.

(* a multilinear extension is affine in each variable *)
Lemma mle_affine : forall j k (T : list F -> F) pre X b, length pre = j -> length b = k ->
  mle2 (j + S k) T (pre ++ X :: b)
  = extF (mle2 (j + S k) T (pre ++ fzero :: b)) (mle2 (j + S k) T (pre ++ fone :: b)) X.
Proof.
  intros j k T pre X b hp hb.
  rewrite !(@mle_concat Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field j (S k) T pre) by exact hp.
  unfold extF.
  rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub j (fun y => mle2 (S k) (fun bb => T (y ++ bb)) (X :: b))
             (fun y => fadd (fmul (fsub fone X) (mle2 k (fun bb => T (y ++ fzero :: bb)) b))
                            (fmul X (mle2 k (fun bb => T (y ++ fone :: bb)) b))))
    by (intros y _; apply (@mle_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field)).
  rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub j (fun y => mle2 (S k) (fun bb => T (y ++ bb)) (fzero :: b))
             (fun y => mle2 k (fun bb => T (y ++ fzero :: bb)) b))
    by (intros y _; rewrite (@mle_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field); field).
  rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub j (fun y => mle2 (S k) (fun bb => T (y ++ bb)) (fone :: b))
             (fun y => mle2 k (fun bb => T (y ++ fone :: bb)) b))
    by (intros y _; rewrite (@mle_S Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field); field).
  rewrite (@mle_add Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
          !(@mle_scale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). field.
Qed.

(* ---------------------------------------------------------------------- *)
(* the executable fold, and tables folded at several challenges *)

Lemma tF_xfold : forall t r h, List.length t = (2 * h)%nat -> map to_F (xfold t r) = fold1 (map to_F t) (to_F r) h.
Proof.
  intros t r h ht. apply (nth_ext _ _ fzero fzero).
  - rewrite length_map, (length_xfold h t r ht). unfold fold1. rewrite length_map, length_seq. reflexivity.
  - intros i hi. rewrite length_map, (length_xfold h t r ht) in hi.
    rewrite nth_fold1 by exact hi. rewrite <-to_F_nth. unfold xfold.
    rewrite (nth_indep _ xzero (xext (xzero, xzero) r)) by (rewrite length_map, (pairs_length h t ht); exact hi).
    rewrite (map_nth (fun p => xext p r) (pairs t) (xzero, xzero) i), pairs_nth by lia.
    rewrite to_F_ext. cbn [fst snd]. rewrite !to_F_nth. reflexivity.
Qed.

Definition foldx (T : list xf) (rs : list xf) : list xf := fold_left (fun t r => xfold t r) rs T.

Lemma foldx_length : forall rs n T, List.length T = (2 ^ (List.length rs + n))%nat -> List.length (foldx T rs) = (2 ^ n)%nat.
Proof.
  induction rs as [| r rs ih]; intros n T h; [exact h |]. cbn [foldx fold_left]. apply ih.
  apply (length_xfold (2 ^ (List.length rs + n))). rewrite h. cbn [List.length Nat.add Nat.pow]. lia.
Qed.

Lemma foldx_entry : forall rs n T e, List.length T = (2 ^ (List.length rs + n))%nat -> (e < 2 ^ n)%nat ->
  to_F (nth e (foldx T rs) xzero) = mle2 (List.length rs + n) (tabOf (map to_F T)) (map to_F rs ++ pt2 n e).
Proof.
  induction rs as [| r rs ih]; intros n T e hT he.
  - cbn [foldx fold_left List.length Nat.add map app].
    rewrite (@mle_cube Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field) by apply pt_cube.
    rewrite tabOf_pt by exact he. apply to_F_nth.
  - cbn [foldx fold_left]. fold (foldx (xfold T r) rs).
    assert (hT' : List.length T = (2 * 2 ^ (List.length rs + n))%nat) by (rewrite hT; cbn [List.length Nat.add Nat.pow]; lia).
    rewrite (ih n (xfold T r) e) by (first [exact he | apply (length_xfold _ T r hT')]).
    cbn [List.length map app]. change (S (List.length rs) + n)%nat with (S (List.length rs + n)).
    rewrite (fold_mle (List.length rs + n)) by (first [rewrite length_map; exact hT'
                                                     | rewrite length_app, length_map, (@pt_length Fq2 fzero fone); reflexivity]).
    rewrite (tF_xfold T r (2 ^ (List.length rs + n)) hT'). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* one round: the core polynomial is the round polynomial of the masked summand *)

Definition mval (mk : option F) : F := match mk with Some a => a | None => fzero end.

(* the masked summand of the original tables, M variables *)
Definition Sfull (TF : list (F * list nat)) (M : nat) (T0 : list (list xf)) (mks : list (option F)) (x : list F) : F :=
  termsF TF (map (fun p => fadd (mle2 M (tabOf (map to_F (fst p))) x) (fmul (mval (snd p)) (Zp2 x))) (combine T0 mks)).

Lemma Zp_cube_pt : forall k i, (1 <= k)%nat -> Zp2 (pt2 k i) = fzero.
Proof.
  intros k i hk. destruct k as [| k]; [lia |]. cbn [CubeIndex.pt MaskedExt.Zp].
  unfold CubeIndex.bit. destruct (Nat.odd i); field.
Qed.

Lemma Zp_app2 : forall x y, Zp2 (x ++ y) = fmul (Zp2 x) (Zp2 y).
Proof. intros x y. apply (@Zp_app Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). Qed.

Lemma pt_even : forall k i, pt2 (S k) (2 * i) = fzero :: pt2 k i.
Proof.
  intros k i. cbn [CubeIndex.pt]. unfold CubeIndex.bit.
  rewrite Nat.odd_mul, Nat.odd_2. cbn [andb]. f_equal. f_equal.
  rewrite Nat.div2_div. rewrite Nat.mul_comm, Nat.div_mul by lia. reflexivity.
Qed.

Lemma pt_odd : forall k i, pt2 (S k) (S (2 * i)) = fone :: pt2 k i.
Proof.
  intros k i. cbn [CubeIndex.pt]. unfold CubeIndex.bit.
  rewrite Nat.odd_succ, Nat.even_mul, Nat.even_2. cbn [orb]. f_equal. f_equal.
  rewrite Nat.div2_succ_double. reflexivity.
Qed.

Lemma combine_map_fst : forall {A B C : Type} (f : A -> C) (l : list A) (l' : list B), List.length l = List.length l' ->
  map (fun p => f (fst p)) (combine l l') = map f l.
Proof. intros A B C f l; induction l as [| x l ih]; intros [| y l'] h; cbn in h |- *; try lia; [reflexivity |]. rewrite ih by lia. reflexivity. Qed.

Theorem core_rnd : forall TF T0 mks point k X, (1 <= k)%nat -> List.length T0 = List.length mks ->
  Forall (fun t => List.length t = (2 ^ (List.length point + S k))%nat) T0 ->
  coreF TF (tF (map (fun t => foldx t point) T0)) (2 ^ k) X
  = @rnd Fq2 fzero fone fadd (Sfull TF (List.length point + S k) T0 mks) (map to_F point) k X.
Proof.
  intros TF T0 mks point k X hk hlm hT. unfold coreF, Sumcheck.rnd.
  rewrite (@cube_sum_seq Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field k
             (fun b => Sfull TF (List.length point + S k) T0 mks (map to_F point ++ X :: b))).
  apply (@fsum_map_ext Fq2 fzero fadd). intros i hi. apply in_seq in hi. unfold Sfull. f_equal.
  rewrite Forall_forall in hT.
  rewrite (map_ext_in _ (fun p => mle2 (List.length point + S k) (tabOf (map to_F (fst p))) (map to_F point ++ X :: pt2 k i))).
  2: { intros p hp. rewrite Zp_app2. cbn [MaskedExt.Zp]. rewrite Zp_cube_pt by exact hk. field. }
  rewrite (combine_map_fst (fun t => mle2 (List.length point + S k) (tabOf (map to_F t)) (map to_F point ++ X :: pt2 k i))) by exact hlm.
  unfold tF. rewrite !map_map. apply map_ext_in. intros t ht.
  assert (hl : List.length t = (2 ^ (List.length point + S k))%nat) by exact (hT t ht).
  rewrite (mle_affine (List.length point) k) by (first [rewrite length_map; reflexivity | apply (@pt_length Fq2 fzero fone)]).
  assert (h2i : (2 * i < 2 ^ S k)%nat) by (cbn [Nat.pow]; lia).
  assert (h2i1 : (S (2 * i) < 2 ^ S k)%nat) by (cbn [Nat.pow]; lia).
  rewrite <-!to_F_nth.
  rewrite (foldx_entry point (S k) t (2 * i) hl h2i), (foldx_entry point (S k) t (S (2 * i)) hl h2i1).
  rewrite pt_even, pt_odd. reflexivity.
Qed.

Theorem last_rnd : forall TF T0 mks point X, List.length T0 = List.length mks ->
  Forall (fun t => List.length t = (2 ^ (List.length point + 1))%nat) T0 ->
  lastcore TF (Zp2 (map to_F point)) (tF (map (fun t => foldx t point) T0)) mks X
  = Sfull TF (List.length point + 1) T0 mks (map to_F point ++ [X]).
Proof.
  intros TF T0 mks point X hlm hT. unfold lastcore, Sfull. f_equal.
  rewrite Forall_forall in hT.
  assert (gen : forall T0' mks', List.length T0' = List.length mks' -> (forall t, In t T0' -> In t T0) ->
            map (fun p => lastF (Zp2 (map to_F point)) (fst p) (snd p) X) (combine (tF (map (fun t => foldx t point) T0')) mks')
            = map (fun p => fadd (mle2 (List.length point + 1) (tabOf (map to_F (fst p))) (map to_F point ++ [X]))
                                 (fmul (mval (snd p)) (Zp2 (map to_F point ++ [X])))) (combine T0' mks')).
  { induction T0' as [| t T0' ih]; intros [| mk mks'] hl hsub; cbn in hl; try lia; [reflexivity |].
    unfold tF in *. cbn [map combine]. f_equal; [| apply ih; [lia | intros t' h'; apply hsub; right; exact h']].
    cbn [fst snd]. assert (ht : List.length t = (2 ^ (List.length point + 1))%nat) by (apply hT, hsub; left; reflexivity).
    unfold lastF. rewrite <-!to_F_nth.
    rewrite (foldx_entry point 1 t 0 ht ltac:(cbn; lia)), (foldx_entry point 1 t 1 ht ltac:(cbn; lia)).
    replace (pt2 1 0) with [fzero] by reflexivity. replace (pt2 1 1) with [fone] by reflexivity.
    rewrite (mle_affine (List.length point) 0 _ (map to_F point) X []) by (first [rewrite length_map; reflexivity | reflexivity]).
    rewrite Zp_app2. cbn [MaskedExt.Zp]. unfold mval.
    destruct mk as [a |]; field. }
  apply gen; [exact hlm | tauto].
Qed.

(* ---------------------------------------------------------------------- *)
(* all rounds *)

Section Loop.

  Variable draw : chal -> bytes -> option (list xf * chal).
  Variable name : String.string.
  Variable tmask : list (option xf).
  Variable terms : list sterm.
  Variables (a0 : xf) (cs : list (list xf)) (rho : xf).

  Local Notation TF := (map sF terms).
  Local Notation gF := (@gmask Fq2 fzero fadd fmul (to_F a0) (csF cs)).
  Local Notation mks := (mF tmask).

  Lemma sc_loop_prefix : forall ds j tables point ch msgs pt fin ch',
    sc_loop draw name tmask terms a0 cs rho ds j tables point ch = Some (msgs, pt, fin, ch') ->
    firstn (List.length point) pt = point /\ List.length msgs = List.length ds.
  Proof.
    induction ds as [| d ds ih]; intros j tables point ch msgs pt fin ch' H; cbn [sc_loop] in H.
    - injection H as <- <- <- <-. split; [apply firstn_all | reflexivity].
    - destruct (draw _ _) as [[rl chr] |]; cbn [bindo] in H; [| discriminate].
      destruct ds as [| d' ds'].
      + injection H as <- <- <- <-. split; [| reflexivity].
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all.
      + destruct (sc_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[[ms pt0] fin0] ch0] |] eqn:hrec; cbn [bindo] in H; [| discriminate].
        injection H as <- <- <- <-. destruct (ih _ _ _ _ _ _ _ _ hrec) as [hp hl].
        split; [| cbn [List.length]; rewrite hl; reflexivity].
        rewrite length_app in hp. cbn [List.length] in hp.
        replace (List.length point) with (List.length point) by reflexivity.
        transitivity (firstn (List.length point) (firstn (List.length point + 1) pt0)).
        * rewrite firstn_firstn. f_equal. lia.
        * rewrite hp. rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all.
  Qed.

  Theorem sc_loop_msgs : forall ds j T0 point ch msgs pts fin ch',
    ds <> [] -> List.length point = j -> List.length cs = (j + List.length ds)%nat ->
    List.length T0 = List.length tmask -> T0 <> [] ->
    Forall (fun t => List.length t = (2 ^ (j + List.length ds))%nat) T0 ->
    sc_loop draw name tmask terms a0 cs rho ds j (map (fun t => foldx t point) T0) point ch = Some (msgs, pts, fin, ch') ->
    forall i, (i < List.length ds)%nat ->
      map to_F (nth i msgs []) =
      map (fun c => fadd ((@rnd Fq2 fzero fone fadd) (Sfull TF (j + List.length ds) T0 mks) (map to_F (firstn (j + i) pts)) (List.length ds - 1 - i) (nF c))
                         (fmul (to_F rho) ((@rnd Fq2 fzero fone fadd) gF (map to_F (firstn (j + i) pts)) (List.length ds - 1 - i) (nF c))))
          (spoints (nth i ds 0%nat)).
  Proof.
    induction ds as [| d ds ih]; intros j T0 point ch msgs pt fin ch' hne hp hcs hlm hT0 hT H i hi; [contradiction |].
    pose proof (sc_loop_prefix _ _ _ _ _ _ _ _ _ H) as [hpre _].
    cbn [sc_loop] in H.
    destruct (draw _ _) as [[rl chr] |] eqn:hg; cbn [bindo] in H; [| discriminate].
    cbn [fst snd] in H. set (r := nth 0 rl xzero) in *.
    set (k := List.length ds) in *.
    assert (hT' : Forall (fun t => List.length t = (2 ^ (List.length point + S k))%nat) T0)
      by (rewrite hp; replace (j + S k)%nat with (j + List.length (d :: ds))%nat by reflexivity; exact hT).
    (* the values of the first message *)
    assert (hv0 : forall last : bool,
      map to_F (map (fun c => xadd ((if last then terms_val terms (last_vals (xzval point) (map (fun t => foldx t point) T0) tmask (xfint c))
                                     else round_val terms (transpose (List.length (pairs (nth 0 (map (fun t => foldx t point) T0) [])))
                                                                    (map pairs (map (fun t => foldx t point) T0))) c))
                                    (xmul rho (mvalue a0 cs j point c))) (spoints d))
      = map (fun c => fadd ((if last then lastcore TF (Zp2 (map to_F point)) (tF (map (fun t => foldx t point) T0)) mks (nF c)
                             else coreF TF (tF (map (fun t => foldx t point) T0)) (2 ^ k) (nF c)))
                           (fmul (to_F rho) ((@rnd Fq2 fzero fone fadd) gF (map to_F point) k (nF c)))) (spoints d)).
    { intro last. rewrite map_map. apply map_ext. intro c. rewrite to_F_add, to_F_mul.
      rewrite to_F_mvalue by (first [exact hp | rewrite hcs; cbn [List.length]; lia]).
      replace (List.length cs - j - 1)%nat with k by (rewrite hcs; cbn [List.length]; lia).
      f_equal. destruct last.
      - rewrite to_F_last_vals, to_F_zval, to_F_xfint. reflexivity.
      - assert (hT2 : Forall (fun t => List.length t = (2 * 2 ^ k)%nat) (map (fun t => foldx t point) T0)).
        { apply Forall_map. rewrite Forall_forall in hT' |- *. intros t ht.
          rewrite (foldx_length point (S k) t) by (apply hT', ht). reflexivity. }
        assert (hh : List.length (pairs (nth 0 (map (fun t => foldx t point) T0) [])) = (2 ^ k)%nat).
        { destruct T0 as [| t0 T0']; [contradiction |]. cbn [map nth]. apply pairs_length.
          inversion hT2 as [| ? ? h1 _]. exact h1. }
        rewrite hh. apply to_F_round_val. exact hT2. }
    destruct ds as [| d' ds'] eqn:eds.
    - (* the last round *)
      injection H as <- <- <- <-. replace i with 0%nat by (cbn in hi; lia). etransitivity; [exact (hv0 true) |]. apply map_ext. intro c.
      rewrite Nat.add_0_r, <-hp, hpre. replace (List.length [d] - 1 - 0)%nat with k by reflexivity.
      replace (List.length point + List.length [d])%nat with (List.length point + 1)%nat by reflexivity.
      rewrite last_rnd; [| unfold mF; rewrite length_map; exact hlm | exact hT'].
      f_equal. unfold Sumcheck.rnd. cbn [Mle.cube map LogDer.fsum k List.length]. ring_simplify.
      cbn [Mle.cube map LogDer.fsum fold_right fold_left]. cbn. ring.
    - (* a first round, then the induction *)
      rewrite <-eds in *. set (rest := ds) in *.
      destruct (sc_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[[ms pt0] fin0] ch0] |] eqn:hrec; cbn [bindo] in H; [| discriminate].
      injection H as <- <- <- <-.
      destruct i as [| i].
      + etransitivity; [exact (hv0 false) |]. apply map_ext. intro c. rewrite Nat.add_0_r.
        rewrite <-hp, hpre.
        replace (List.length (d :: rest) - 1 - 0)%nat with k by (unfold k; rewrite <-eds; cbn; lia).
        replace (List.length point + List.length (d :: rest))%nat with (List.length point + S k)%nat by (unfold k; rewrite <-eds; cbn; lia).
        rewrite (core_rnd _ _ mks); [reflexivity | unfold k; cbn; lia | unfold mF; rewrite length_map; exact hlm | exact hT'].
      + cbn [nth].
        assert (hfold : map (fun t => xfold t r) (map (fun t => foldx t point) T0) = map (fun t => foldx t (point ++ [r])) T0).
        { rewrite map_map. apply map_ext. intro t. unfold foldx. rewrite fold_left_app. reflexivity. }
        rewrite hfold in hrec.
        assert (hk : List.length rest = k) by (rewrite eds; reflexivity).
        rewrite (ih (S j) T0 (point ++ [r]) chr ms pt0 fin0 ch0).
        { apply map_ext. intro c. cbn [List.length]. rewrite hk.
          replace (S j + k)%nat with (j + S k)%nat by lia.
          replace (S j + i)%nat with (j + S i)%nat by lia.
          replace (k - 1 - i)%nat with (S k - 1 - S i)%nat by lia. reflexivity. }
        { rewrite eds; discriminate. }
        { rewrite length_app, hp; cbn; lia. }
        { rewrite hcs; cbn [List.length]; rewrite hk; lia. }
        { exact hlm. }
        { exact hT0. }
        { eapply Forall_impl; [| exact hT]; intros t ht; rewrite ht; f_equal; cbn [List.length]; rewrite hk; lia. }
        { exact hrec. }
        { cbn [List.length] in hi; rewrite hk in hi; lia. }
  Qed.

  Lemma sc_loop_ptlen : forall ds j tables point ch msgs pt fin ch',
    sc_loop draw name tmask terms a0 cs rho ds j tables point ch = Some (msgs, pt, fin, ch') ->
    List.length pt = (List.length point + List.length ds)%nat.
  Proof.
    induction ds as [| d ds ih]; intros j tables point ch msgs pt fin ch' H; cbn [sc_loop] in H.
    - injection H as <- <- <- <-. cbn. lia.
    - destruct (draw _ _) as [[rl chr] |]; cbn [bindo] in H; [| discriminate].
      destruct ds as [| d' ds'].
      + injection H as <- <- <- <-. rewrite length_app. reflexivity.
      + destruct (sc_loop _ _ _ _ _ _ _ _ _ _ _ _) as [[[[ms pt0] fin0] ch0] |] eqn:hrec; cbn [bindo] in H; [| discriminate].
        injection H as <- <- <- <-. rewrite (ih _ _ _ _ _ _ _ _ hrec), length_app. cbn [List.length]. lia.
  Qed.

  (* a whole run from the start: the messages are the values, at the nodes,
     of the model's honest masked messages hmsg (ZkSumcheck.v), for any
     summand f that agrees with Sfull and any pf interpolating its rounds *)
  Theorem sc_msgs_hmsg : forall ds T0 ch msgs pts fin ch' (f : list F -> F) (pf : list F -> list F),
    ds <> [] -> List.length cs = List.length ds ->
    List.length T0 = List.length tmask -> T0 <> [] ->
    Forall (fun t => List.length t = (2 ^ List.length ds)%nat) T0 ->
    sc_loop draw name tmask terms a0 cs rho ds 0 T0 [] ch = Some (msgs, pts, fin, ch') ->
    (forall x, List.length x = List.length ds -> Sfull TF (List.length ds) T0 mks x = f x) ->
    (forall i X, (i < List.length ds)%nat ->
       @eval F fzero fadd fmul (pf (firstn i (map to_F pts))) X
       = @rnd Fq2 fzero fone fadd f (firstn i (map to_F pts)) (List.length ds - 1 - i) X) ->
    forall i, (i < List.length ds)%nat ->
      map to_F (nth i msgs []) =
      map (fun c => @eval F fzero fadd fmul
                      (@hmsg F fzero fone fadd fmul (List.length ds) pf (to_F rho) (to_F a0) (csF cs) (map to_F pts) i) (nF c))
          (spoints (nth i ds 0%nat)).
  Proof.
    intros ds T0 ch msgs pts fin ch' f pf hne hcs hlm hT0 hT H hS hpf i hi.
    assert (hlen : List.length pts = List.length ds) by (rewrite (sc_loop_ptlen _ _ _ _ _ _ _ _ _ H); reflexivity).
    assert (hid : map (fun t => foldx t []) T0 = T0) by (rewrite <-(map_id T0) at 2; apply map_ext; reflexivity).
    rewrite <-hid in H.
    rewrite (sc_loop_msgs ds 0 T0 [] ch msgs pts fin ch' hne eq_refl hcs hlm hT0 hT H i hi).
    apply map_ext. intro c.
    rewrite (@hmsg_eval F fzero fone fadd fmul fsub fdiv fopp finv Fq2_field (List.length ds) pf (to_F rho) (to_F a0) (csF cs)
               (map to_F pts)) by (first [exact hi | unfold csF; rewrite length_map; exact hcs | rewrite length_map; exact hlen]).
    rewrite hpf by exact hi. cbn [Nat.add]. rewrite firstn_map. unfold csF.
    f_equal. unfold Sumcheck.rnd. f_equal. apply map_ext_in. intros b hb. apply hS.
    rewrite length_app, length_map, length_firstn. cbn [List.length].
    rewrite (cube_length _ _ hb). lia.
  Qed.

End Loop.
