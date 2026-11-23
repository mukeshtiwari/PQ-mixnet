(* Prover side, completeness of the front end: the Merkle paths and the
   challenger's draws.

   - lpath_layers, broot_commit: the tree that commit builds once has the
     paths and root of ExecMerkle.v (mpath, mroot).
   - commit_path: every leaf of a committed batch, with its salt and path,
     leads root_from to the batch's root (ExecMerkle.v: root_from_path).
   - merkle_ok_prover: the verifier's check merkle_ok accepts the columns
     the prover opens, at any indices below n, for any list of batches
     committed with n = 2^d leaves.
   - get_F_shape, get_I_shape: the challenger returns as many values as
     asked for, field elements reduced, indices below the bound (a power of
     2). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String.
From Examples Require Import ConcreteField ExecField ExecHash ExecVerify ExecMerkle ExecProveBase ExecSerial ExecNtt.
Import ListNotations.
Local Open Scope list_scope.

(* ---------------------------------------------------------------------- *)
(* the tree built once *)

Fixpoint upn (d : nat) (l : list bytes) : list bytes :=
  match d with O => l | S d' => upn d' (up l) end.

Lemma mroot_upn : forall d l, mroot d l = nth 0 (upn d l) [].
Proof. induction d as [| d ih]; intro l; [reflexivity | apply ih]. Qed.

Lemma last_layers : forall d l, last (layers d l) [] = upn d l.
Proof.
  induction d as [| d ih]; intro l; [reflexivity |].
  cbn [layers upn]. rewrite <-ih. destruct d; reflexivity.
Qed.

Lemma lpath_layers : forall d l j, lpath (layers d l) j = mpath d l j.
Proof.
  induction d as [| d ih]; intros l j; [reflexivity |].
  cbn [layers mpath]. rewrite <-ih. destruct d; reflexivity.
Qed.

Lemma zipcons_length : forall {A : Type} (r : list A) acc,
  List.length (zipcons r acc) = Nat.min (List.length r) (List.length acc).
Proof. intros A r; induction r as [| x r ih]; intros [| a acc]; cbn; try reflexivity. rewrite ih. reflexivity. Qed.

Lemma transpose_length : forall {A : Type} n (rows : list (list A)),
  Forall (fun r => List.length r = n) rows -> List.length (transpose n rows) = n.
Proof.
  intros A n rows h. unfold transpose. induction h as [| r rows hr hrows ih].
  + apply repeat_length.
  + cbn [fold_right]. rewrite zipcons_length, ih, hr. lia.
Qed.

Lemma zpows_length : forall x n acc, List.length (zpows x n acc) = n.
Proof. intros x n; induction n as [| n ih]; intro acc; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.


Lemma bcols_length : forall om n d msgs salts, List.length (bcols (commit om n d msgs salts)) = n.
Proof.
  intros. cbn [commit bcols]. apply transpose_length.
  apply Forall_map, Forall_forall. intros. apply zenc_length.
Qed.

Definition leaves_of (bt : batch) : list bytes := map (fun p => leaf_hash (fst p) (snd p)) (combine (bsalts bt) (bcols bt)).

Lemma commit_layers : forall om n d msgs salts,
  blayers (commit om n d msgs salts) = layers d (leaves_of (commit om n d msgs salts)).
Proof. reflexivity. Qed.

Theorem commit_path : forall om n d msgs salts j,
  n = (2 ^ d)%nat -> List.length salts = n -> (j < n)%nat ->
  let bt := commit om n d msgs salts in
  root_from (leaf_hash (nth j (bsalts bt) []) (nth j (bcols bt) [])) (Z.of_nat j) (lpath (blayers bt) j) = broot bt.
Proof.
  intros om n d msgs salts j hn hs hj bt.
  assert (hc : List.length (bcols bt) = n) by apply bcols_length.
  assert (hl : List.length (leaves_of bt) = (2 ^ d)%nat).
  { unfold leaves_of. rewrite length_map, length_combine. unfold bt. cbn [commit bsalts]. rewrite hs.
    fold bt. rewrite hc. lia. }
  unfold broot. change (blayers bt) with (layers d (leaves_of bt)).
  rewrite lpath_layers, last_layers, <-mroot_upn. rewrite <-(root_from_path d (leaves_of bt) j hl ltac:(lia)).
  f_equal. unfold leaves_of.
  assert (hsb : List.length (bsalts bt) = n) by exact hs.
  rewrite (nth_indep (map (fun p => leaf_hash (fst p) (snd p)) (combine (bsalts bt) (bcols bt))) []
             (leaf_hash (fst (@nil Z, @nil Z)) (snd (@nil Z, @nil Z))))
    by (rewrite length_map, length_combine; lia).
  replace (nth j (map (fun p => leaf_hash (fst p) (snd p)) (combine (bsalts bt) (bcols bt)))
             (leaf_hash (fst (@nil Z, @nil Z)) (snd (@nil Z, @nil Z))))
    with (leaf_hash (fst (nth j (combine (bsalts bt) (bcols bt)) (@nil Z, @nil Z)))
                    (snd (nth j (combine (bsalts bt) (bcols bt)) (@nil Z, @nil Z))))
    by (symmetry; exact (map_nth (fun p => leaf_hash (fst p) (snd p)) (combine (bsalts bt) (bcols bt)) ([], []) j)).
  rewrite combine_nth by (transitivity n; [exact hsb | symmetry; exact hc]). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* merkle_ok on the prover's columns *)

Definition good_batch (n : nat) (bt : batch) : Prop :=
  forall j, (j < n)%nat ->
    root_from (leaf_hash (nth j (bsalts bt) []) (nth j (bcols bt) [])) (Z.of_nat j) (lpath (blayers bt) j) = broot bt.

Lemma good_commit : forall om n d msgs salts, n = (2 ^ d)%nat -> List.length salts = n ->
  good_batch n (commit om n d msgs salts).
Proof. intros om n d msgs salts hn hs j hj. apply commit_path; assumption. Qed.

Lemma in_combine_map : forall {A B : Type} (f : A -> B) (l : list A) x y,
  In (x, y) (combine l (map f l)) -> y = f x /\ In x l.
Proof.
  intros A B f l; induction l as [| a l ih]; intros x y h; [destruct h |].
  cbn in h. destruct h as [e | h]; [injection e as <- <-; split; [reflexivity | left; reflexivity] |].
  destruct (ih x y h) as [e1 e2]. split; [exact e1 | right; exact e2].
Qed.

Lemma in_combine_seq_map : forall {A B : Type} (g : A -> B) (l : list A) i y d,
  In (i, y) (combine (seq 0 (List.length l)) (map g l)) -> (i < List.length l)%nat /\ y = g (nth i l d).
Proof.
  intros A B g l i y d h.
  apply In_nth with (d := (0%nat, g d)) in h. destruct h as (k & hk & e).
  rewrite length_combine, length_seq, length_map, Nat.min_id in hk.
  rewrite combine_nth in e by (rewrite length_seq, length_map; reflexivity).
  rewrite seq_nth in e by exact hk. rewrite (map_nth g l d k) in e. injection e as <- <-.
  split; [exact hk | reflexivity].
Qed.

Theorem merkle_ok_prover : forall n (bts : list batch) (js : list nat),
  Forall (good_batch n) bts -> Forall (fun j => (j < n)%nat) js ->
  merkle_ok (map broot bts) js (map (fun j => map (fun bt => bitem bt j) bts) js) = true.
Proof.
  intros n bts js hb hj. unfold merkle_ok. apply forallb_forall. intros [j pb] hin.
  apply in_combine_map in hin. destruct hin as [-> hjin].
  rewrite Forall_forall in hj. specialize (hj j hjin).
  apply forallb_forall. intros [bi it] hin.
  rewrite length_map in hin.
  destruct (in_combine_seq_map (fun bt => bitem bt j) bts bi it (mk_batch [] [] [] []) hin) as [hbi ->].
  rewrite nth_error_map, (nth_error_nth' bts (mk_batch [] [] [] []) hbi). cbn [option_map].
  unfold bitem. rewrite Forall_forall in hb.
  rewrite (hb (nth bi bts (mk_batch [] [] [] [])) (nth_In _ _ hbi) j hj).
  destruct (list_eq_dec Z.eq_dec _ _) as [_ | ne]; [reflexivity | contradiction].
Qed.

(* ---------------------------------------------------------------------- *)
(* the challenger's draws *)

Lemma base_shape : forall fuel ch v ch', base fuel ch = Some (v, ch') -> zred v.
Proof.
  induction fuel as [| f ih]; intros ch v ch' h; cbn [base] in h; [discriminate |].
  destruct (ExecHash.take EB ch) as [bs c1]. destruct (Z.ltb_spec (Z.land (from_be bs) (2 ^ 79 - 1)) Q) as [hl | hl].
  + injection h as <- <-. split; [| exact hl]. apply Z.land_nonneg. right. lia.
  + exact (ih _ _ _ h).
Qed.

Lemma get_Fs_shape : forall n ch r ch', get_Fs n ch = Some (r, ch') -> List.length r = n /\ Forall reduced r.
Proof.
  induction n as [| n ih]; intros ch r ch' h; cbn [get_Fs] in h.
  + injection h as <- <-. split; [reflexivity | constructor].
  + destruct (base 1000 ch) as [[x c1] |] eqn:e1; [| discriminate].
    destruct (base 1000 c1) as [[y c2] |] eqn:e2; [| discriminate].
    destruct (get_Fs n c2) as [[xs c3] |] eqn:e3; [| discriminate].
    injection h as <- <-. destruct (ih _ _ _ e3) as [hl hr].
    split; [cbn; rewrite hl; reflexivity |]. constructor; [| exact hr].
    split; [exact (base_shape _ _ _ _ e1) | exact (base_shape _ _ _ _ e2)].
Qed.

Theorem get_F_shape : forall ch nm n r ch', get_F ch nm n = Some (r, ch') -> List.length r = n /\ Forall reduced r.
Proof. intros ch nm n r ch' h. exact (get_Fs_shape _ _ _ _ h). Qed.

Lemma get_Is_shape : forall d fuel n seen ch r ch', get_Is fuel n (2 ^ Z.of_nat d) seen ch = Some (r, ch') ->
  List.length r = n /\ Forall (fun z => (0 <= z < 2 ^ Z.of_nat d)%Z) r.
Proof.
  intros d. induction fuel as [| f ih]; intros n seen ch r ch' h; destruct n as [| n]; cbn [get_Is] in h;
    try discriminate; try (injection h as <- <-; split; [reflexivity | constructor]).
  destruct (ExecHash.take 4 ch) as [bs c1].
  destruct (existsb _ _); [exact (ih _ _ _ _ _ h) |].
  destruct (get_Is f n _ _ c1) as [[vs c2] |] eqn:e; [| discriminate].
  injection h as <- <-. destruct (ih _ _ _ _ _ e) as [hl hr].
  split; [cbn; rewrite hl; reflexivity |]. constructor; [| exact hr].
  replace (2 ^ Z.of_nat d - 1)%Z with (Z.ones (Z.of_nat d)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
Qed.

Theorem get_I_shape : forall ch nm n d r ch', get_I ch nm n (2 ^ Z.of_nat d) = Some (r, ch') ->
  List.length r = n /\ Forall (fun z => (0 <= z < 2 ^ Z.of_nat d)%Z) r.
Proof. intros ch nm n d r ch' h. exact (get_Is_shape _ _ _ _ _ _ _ h). Qed.

Lemma drawn_indices : forall nq n d nm (JB : list Z), n = (2 ^ d)%nat ->
  (exists c c', get_I c (sb nm) nq (Z.of_nat n) = Some (JB, c')) -> Forall (fun j => (j < n)%nat) (map Z.to_nat JB).
Proof.
  intros nq n d nm JB hn (c & c' & h). rewrite hn, Nat2Z.inj_pow in h. cbn [Z.of_nat Pos.of_succ_nat] in h.
  replace (Z.pos 2) with 2%Z in h by reflexivity.
  destruct (get_I_shape _ _ _ _ _ _ h) as [_ hr].
  apply Forall_map. eapply Forall_impl; [| exact hr]. intros z hz. cbn beta in hz.
  rewrite hn. apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. rewrite Nat2Z.inj_pow. exact (proj2 hz).
Qed.

(* the column draw rejects repeats: its indices are distinct *)
Lemma get_Is_fresh : forall fuel n bound seen ch r ch', get_Is fuel n bound seen ch = Some (r, ch') ->
  NoDup r /\ Forall (fun v => ~ In v seen) r.
Proof.
  induction fuel as [| f ih]; intros n bound seen ch r ch' h; destruct n as [| n]; cbn [get_Is] in h;
    try discriminate; try (injection h as <- <-; split; constructor).
  destruct (ExecHash.take 4 ch) as [bs c1].
  destruct (existsb _ _) eqn:ex; [exact (ih _ _ _ _ _ _ h) |].
  destruct (get_Is f n _ _ c1) as [[vs c2] |] eqn:e; [| discriminate].
  injection h as <- <-. destruct (ih _ _ _ _ _ _ e) as [nd fr]. rewrite Forall_forall in fr.
  set (v := Z.land (from_be bs) (bound - 1)) in *.
  assert (hv : ~ In v seen).
  { intro hin. assert (existsb (Z.eqb v) seen = true) by (apply existsb_exists; exists v; split; [exact hin | apply Z.eqb_refl]).
    congruence. }
  split.
  - constructor; [| exact nd]. intro hin. exact (fr v hin (or_introl eq_refl)).
  - constructor; [exact hv |]. apply Forall_forall. intros x hx hin. exact (fr x hx (or_intror hin)).
Qed.

Lemma drawn_nodup : forall nq n d nm (JB : list Z), n = (2 ^ d)%nat ->
  (exists c c', get_I c (sb nm) nq (Z.of_nat n) = Some (JB, c')) -> NoDup (map Z.to_nat JB).
Proof.
  intros nq n d nm JB hn (c & c' & h).
  assert (hr : Forall (fun z => (0 <= z)%Z) JB).
  { rewrite hn, Nat2Z.inj_pow in h. cbn [Z.of_nat Pos.of_succ_nat] in h.
    replace (Z.pos 2) with 2%Z in h by reflexivity.
    destruct (get_I_shape _ _ _ _ _ _ h) as [_ hs]. eapply Forall_impl; [| exact hs]. intros z hz. cbv beta in hz. lia. }
  pose proof (proj1 (get_Is_fresh _ _ _ _ _ _ _ h)) as nd.
  rewrite Forall_forall in hr. apply NoDup_map_on; [exact nd |].
  intros x y hx hy e. apply Z2Nat.inj; [exact (hr x hx) | exact (hr y hy) | exact e].
Qed.

Lemma drawn_count : forall nq n d nm (JB : list Z), n = (2 ^ d)%nat ->
  (exists c c', get_I c (sb nm) nq (Z.of_nat n) = Some (JB, c')) -> List.length JB = nq.
Proof.
  intros nq n d nm JB hn (c & c' & h). rewrite hn, Nat2Z.inj_pow in h. cbn [Z.of_nat Pos.of_succ_nat] in h.
  replace (Z.pos 2) with 2%Z in h by reflexivity. exact (proj1 (get_I_shape _ _ _ _ _ _ h)).
Qed.
