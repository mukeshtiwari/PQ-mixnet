(* Completeness, back end, generic part: the prover's rows read as tables.

   The prover lays a table l (a list of 2^M integers mod q) into rows with
   split_rows and padrow; the verifier's layout (RowLayout.v) reads the
   table back from the rows with rdtab. On the prover's own rows (mapped
   to GF(q^2)) the two agree:

     rdtab_list   rdtab P start M lo (pt M x) = to_F (bx (l[x]))
     mle_list     the multilinear extension of a table that agrees with a
                  list on the cube is to_F of the prover's xmle.

   Plus small facts about to_F on base-field pairs (to_F_split: an element
   is its two base-field coordinates combined with t), cube points
   (pt_split), and the mask-table row. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import Counting LogDer Mle Negacyclic CubeIndex LayoutLemmas RowLayout MixBridge. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecOpen ExecPublic ExecClaims ExecVerify ExecProveBase.
Import ListNotations.

Add Field fieldF2r : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation F := Fq2.
Local Notation fsum := (@LogDer.fsum Fq2 fzero fadd).
Local Notation dot := (@LogDer.dot Fq2 fzero fadd fmul).
Local Notation pt2 := (@pt Fq2 fzero fone).
Local Notation mle2 := (@mle Fq2 fzero fone fadd fmul fsub).

(* ---------------------------------------------------------------------- *)
(* base-field elements *)

Lemma to_F_bx_zm : forall z, to_F (bx (zm z)) = to_F (bx z).
Proof. intro z. unfold to_F, bx, zm. cbn [fst snd]. rewrite zq_of_mod. reflexivity. Qed.

Lemma to_F_bx0 : to_F (bx 0%Z) = fzero.
Proof. unfold to_F, bx. cbn [fst snd]. rewrite zq_of_0. reflexivity. Qed.

Lemma to_F_split : forall x : xf, to_F x = fadd (to_F (bx (fst x))) (fmul ftg (to_F (bx (snd x)))).
Proof.
  intros [p q]. rewrite <-to_F_tg, <-to_F_mul, <-to_F_add. unfold to_F, xadd, xmul, xtg, bx. cbn [fst snd].
  replace (0 * q + 3 * 1 * 0)%Z with 0%Z by ring. replace (0 * 0 + 1 * q)%Z with q by ring.
  rewrite Zmod_0_l, Z.add_0_r, Z.add_0_l, !zq_of_mod. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* cube points and tables *)

Lemma pt_split : forall a b y t, (y < 2 ^ a)%nat -> pt2 (a + b) (y + 2 ^ a * t) = pt2 a y ++ pt2 b t.
Proof.
  induction a as [| a ih]; intros b y t hy.
  + cbn in hy. replace y with 0%nat by lia. cbn. f_equal. lia.
  + cbn [Nat.add CubeIndex.pt app].
    replace (y + 2 ^ S a * t)%nat with (y + 2 * (2 ^ a * t))%nat by (rewrite Nat.pow_succ_r'; lia).
    f_equal.
    - unfold CubeIndex.bit. rewrite Nat.odd_add_mul_2. reflexivity.
    - rewrite <-ih by (rewrite Nat.div2_div; apply Nat.Div0.div_lt_upper_bound; rewrite Nat.pow_succ_r' in hy; lia).
      f_equal. rewrite !Nat.div2_div. rewrite (Nat.mul_comm 2 (2 ^ a * t)), Nat.div_add by lia. reflexivity.
Qed.

Lemma mle_list : forall M (T : list F -> F) (tbl r : list xf), List.length tbl = (2 ^ M)%nat -> List.length r = M ->
  (forall i, (i < 2 ^ M)%nat -> T (pt2 M i) = to_F (nth i tbl xzero)) ->
  mle2 M T (map to_F r) = to_F (xmle tbl r).
Proof.
  intros M T tbl r hl hr h. rewrite to_F_mle by (rewrite hr; exact hl). rewrite hr.
  rewrite !(@mle_seq Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
  apply (@fsum_map_ext Fq2 fzero fadd). intros i hi. apply in_seq in hi.
  rewrite tabOf_pt, h by lia. rewrite to_F_nth. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* rows of a table *)

Lemma chunks_nth : forall {A : Type} fuel C (l : list A) t, (0 < C)%nat -> (t < fuel)%nat -> (t * C < List.length l)%nat ->
  nth t (ExecProveBase.chunks fuel C l) [] = firstn C (skipn (t * C) l).
Proof.
  intros A fuel; induction fuel as [| f ih]; intros C l t hC ht hl; [lia |].
  cbn [ExecProveBase.chunks]. destruct l as [| x l']; [cbn in hl; lia |].
  destruct t as [| t]; [reflexivity |]. cbn [nth].
  rewrite ih by (try lia; rewrite length_skipn; cbn [List.length] in *; lia).
  rewrite skipn_skipn. f_equal. f_equal. lia.
Qed.

Lemma split_rows_nth : forall lo M (l : list Z) y t, List.length l = (2 ^ M)%nat ->
  (y < 2 ^ loE M lo)%nat -> (t < 2 ^ hiE M lo)%nat ->
  nth y (nth t (split_rows (2 ^ lo) l) []) 0%Z = nth (y + 2 ^ loE M lo * t) l 0%Z
  /\ (y < List.length (nth t (split_rows (2 ^ lo) l) []))%nat.
Proof.
  intros lo M l y t hl hy ht. unfold split_rows, loE, hiE in *.
  destruct (Nat.leb_spec (List.length l) (2 ^ lo)) as [hle | hgt].
  + assert (hM : (M <= lo)%nat).
    { destruct (Nat.le_gt_cases M lo) as [h | h]; [exact h |].
      pose proof (Nat.pow_lt_mono_r 2 lo M ltac:(lia) h). lia. }
    replace (Nat.min lo M) with M in * by lia. rewrite Nat.sub_diag in ht. cbn in ht.
    replace t with 0%nat by lia. cbn [nth]. rewrite Nat.mul_0_r, Nat.add_0_r. split; [reflexivity | lia].
  + assert (hM : (lo < M)%nat).
    { destruct (Nat.le_gt_cases M lo) as [h | h]; [| exact h].
      pose proof (Nat.pow_le_mono_r 2 M lo ltac:(lia) h). lia. }
    replace (Nat.min lo M) with lo in * by lia.
    assert (hsplit : (2 ^ M = 2 ^ lo * 2 ^ (M - lo))%nat) by (rewrite <-Nat.pow_add_r; f_equal; lia).
    assert (htl : (t * 2 ^ lo + 2 ^ lo <= List.length l)%nat).
    { rewrite hl, hsplit. replace (t * 2 ^ lo + 2 ^ lo)%nat with (2 ^ lo * S t)%nat by lia.
      apply Nat.mul_le_mono_l. lia. }
    assert (hpos : (0 < 2 ^ lo)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    assert (ht2 : (t < List.length l)%nat) by nia.
    rewrite chunks_nth by lia.
    split.
    - rewrite nth_firstn, nth_skipn. destruct (Nat.ltb_spec y (2 ^ lo)); [| lia]. f_equal. lia.
    - rewrite length_firstn, length_skipn. lia.
Qed.

Lemma nth_padrow : forall C row pads y, (y < List.length row)%nat -> nth y (padrow C row pads) 0%Z = zm (nth y row 0%Z).
Proof.
  intros C row pads y hy. unfold padrow. rewrite app_nth1 by (rewrite length_map; exact hy).
  rewrite (nth_indep _ 0%Z (zm 0%Z)) by (rewrite length_map; exact hy). apply map_nth.
Qed.

(* the entry y of a row, as a field element *)
Lemma nth_row_F : forall (row : list Z) y, nth y (map to_F (map bx row)) fzero = to_F (bx (nth y row 0%Z)).
Proof.
  intros row y. rewrite map_map. rewrite <-to_F_bx0.
  exact (map_nth (fun z => to_F (bx z)) row 0%Z y).
Qed.

(* a table laid out by split_rows / padrow reads back as itself *)
Theorem rdtab_list : forall (P : nat -> list F) start M lo (l : list Z) (pd : nat -> list Z),
  List.length l = (2 ^ M)%nat ->
  (forall t, (t < 2 ^ hiE M lo)%nat ->
     P (start + t)%nat = map to_F (map bx (padrow (2 ^ lo) (nth t (split_rows (2 ^ lo) l) []) (pd t)))) ->
  forall x, (x < 2 ^ M)%nat -> @rdtab F fzero fone Fq2_dec P start M lo (pt2 M x) = to_F (bx (nth x l 0%Z)).
Proof.
  intros P start M lo l pd hl hP x hx.
  set (a := loE M lo) in *. set (b := hiE M lo) in *.
  assert (hM : M = (a + b)%nat) by (unfold a, b, loE, hiE; lia).
  assert (hpa : (0 < 2 ^ a)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (hy : (x mod 2 ^ a < 2 ^ a)%nat) by (apply Nat.mod_upper_bound; lia).
  assert (ht : (x / 2 ^ a < 2 ^ b)%nat).
  { apply Nat.Div0.div_lt_upper_bound. rewrite <-Nat.pow_add_r, <-hM. exact hx. }
  assert (hx2 : x = (x mod 2 ^ a + 2 ^ a * (x / 2 ^ a))%nat) by (pose proof (Nat.div_mod x (2 ^ a)); lia).
  replace (pt2 M x) with (pt2 (a + b) (x mod 2 ^ a + 2 ^ a * (x / 2 ^ a))) by (rewrite <-hM, <-hx2; reflexivity).
  rewrite pt_split by exact hy.
  etransitivity; [symmetry; exact (@rdtab_spec Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field P start M lo
               (x mod 2 ^ a) (x / 2 ^ a) hy ht) |].
  rewrite hP by exact ht. rewrite nth_row_F.
  destruct (split_rows_nth lo M l (x mod 2 ^ a) (x / 2 ^ a) hl hy ht) as [e1 e2].
  rewrite nth_padrow by exact e2. rewrite to_F_bx_zm, e1. fold a. rewrite <-hx2. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the mask-table row: pairs (x, y) stored as two entries *)

Definition mrow (km : list xf) : list Z := flat_map (fun x => [fst x; snd x]) km.

Lemma nth_mrow : forall km e, (e < List.length km)%nat ->
  nth (2 * e) (mrow km) 0%Z = fst (nth e km xzero) /\ nth (2 * e + 1) (mrow km) 0%Z = snd (nth e km xzero).
Proof.
  unfold mrow. induction km as [| x km ih]; intros e he; [cbn in he; lia |].
  destruct e as [| e]; [split; reflexivity |].
  cbn [flat_map app]. replace (2 * S e)%nat with (S (S (2 * e))) by lia.
  replace (S (S (2 * e)) + 1)%nat with (S (S (2 * e + 1))) by lia. cbn [nth].
  apply ih. cbn in he. lia.
Qed.

Lemma mrow_length : forall km, List.length (mrow km) = (2 * List.length km)%nat.
Proof. unfold mrow. induction km as [| x km ih]; cbn [flat_map app List.length]; [reflexivity | rewrite ih; lia]. Qed.

Lemma ment_row : forall C km pads e, (e < List.length km)%nat ->
  @ment Fq2 fzero fadd fmul ftg (map to_F (map bx (padrow C (mrow km) pads))) e = to_F (nth e km xzero).
Proof.
  intros C km pads e he. unfold ment. rewrite !nth_row_F.
  destruct (nth_mrow km e he) as [e1 e2].
  rewrite !nth_padrow by (rewrite mrow_length; lia). rewrite !to_F_bx_zm, e1, e2.
  symmetry. apply to_F_split.
Qed.

Lemma cuts_chunks : forall ds (l : list xf), map (map to_F) (fst (cuts ds l)) = @RowLayout.chunks Fq2 ds (map to_F l).
Proof.
  induction ds as [| d ds ih]; intro l; [reflexivity |].
  cbn [cuts cut]. destruct (cuts ds (skipn d l)) as [xs s2] eqn:e. cbn [fst map RowLayout.chunks].
  rewrite firstn_map, skipn_map, <-ih, e. reflexivity.
Qed.

Lemma chunks_firstn : forall ds (L : list F), RowLayout.chunks ds (firstn (dsumL ds) L) = RowLayout.chunks ds L.
Proof.
  induction ds as [| d ds ih]; intro L; [reflexivity |]. cbn [RowLayout.chunks dsumL].
  rewrite firstn_firstn, Nat.min_l by lia. f_equal.
  rewrite <-(ih (skipn d L)). f_equal. rewrite <-firstn_skipn_comm. f_equal.
Qed.

Lemma tl_skipn : forall {A : Type} n (l : list A), tl (skipn n l) = skipn (S n) l.
Proof. intros A n; induction n as [| n ih]; intro l; destruct l; cbn; try reflexivity. apply ih. Qed.

(* the masks of the sumchecks, read off the row *)
Theorem maskCs_row : forall C km pads off ds, (off + 1 + dsumL ds <= List.length km)%nat ->
  @maskCs Fq2 fzero fadd fmul ftg (map to_F (map bx (padrow C (mrow km) pads))) off ds
  = map (map to_F) (fst (cuts ds (tl (skipn off km)))).
Proof.
  intros C km pads off ds h. unfold maskCs. rewrite cuts_chunks, <-(chunks_firstn ds (map to_F (tl (skipn off km)))). f_equal.
  apply nth_ext with (d := fzero) (d' := fzero).
  + rewrite length_map, length_seq, length_firstn, length_map. rewrite tl_skipn, length_skipn. lia.
  + intros i hi. rewrite length_map, length_seq in hi.
    rewrite (nth_indep _ fzero ((fun i => @ment Fq2 fzero fadd fmul ftg (map to_F (map bx (padrow C (mrow km) pads))) (off + 1 + i)) 0%nat))
      by (rewrite length_map, length_seq; exact hi).
    etransitivity; [exact (map_nth (fun i0 => @ment Fq2 fzero fadd fmul ftg (map to_F (map bx (padrow C (mrow km) pads))) (off + 1 + i0)) (seq 0 (dsumL ds)) 0%nat i) |].
    rewrite seq_nth by exact hi. cbv beta. rewrite ment_row by lia.
    rewrite nth_firstn. destruct (Nat.ltb_spec i (dsumL ds)); [| lia].
    rewrite tl_skipn, <-to_F_zero, map_nth, nth_skipn. f_equal. f_equal. lia.
Qed.

Lemma dsumL_list_sum : forall ds, dsumL ds = list_sum ds.
Proof. induction ds as [| d ds ih]; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.
