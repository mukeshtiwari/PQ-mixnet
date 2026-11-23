(* The row layout of the implementation, piece by piece (fp_core.py:
   split_rows, lo_vec, hi_coefs; mix_proof.py: unit, gfun,
   SCMask.functional).

   Throughout, P is the family of decoded rows and tg is the element t of
   F = Z_q[t]/(t^2 - nu): an F-valued entry is stored as two entries
   (x0, x1) and read as x0 + tg * x1. Nothing here uses t^2 = nu.

   Tables in rows.
     A table of 2^M entries is stored in rows of 2^lo symbols. With
     loE = min lo M and hiE = M - loE it occupies 2^hiE rows; if M < lo the
     single row is padded with zeros.
       lovec M lo x      the slot vector: eq table of the low coordinates
                         of x, padded with zeros           (lo_vec)
       tabt slot start coef M lo x
                         one term per row, coefficient
                         coef * eq(t, high coordinates)    (hi_coefs, tab)
     tensor_claim: the value of these terms is coef * mle T x.
     rdtab: the table read off the rows, which satisfies the hypothesis of
     tensor_claim (rdtab_spec).

   The mask-table row.
       ment Pm e         entry e of the row, an F element
       unitv e           the functional reading it          (unit)
       gfunv off cf      the functional sum_i cf_i * entry (off + i)   (gfun)
       funcv degs r      1 :: [r_j, r_j^2, .., r_j^(d_j)]_j   (SCMask.functional)
       maskOf Pm off degs
                         the sumcheck mask (a0, cs) stored at entries
                         off, off + 1, ..
     mask_row_gmask: the value of that mask at r is the inner product of
     the row with gfunv off (funcv degs r). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Sumcheck SumcheckMask CubeIndex Opening MixBridge LayoutLemmas SlotKinds ZkSumcheck.
Import ListNotations.

Section RowLayout.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation pt := (@pt F zero one).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation pows := (@pows F mul).
  Local Notation maskfn := (@maskfn F mul).
  Local Notation gterm := (@gterm F).

  (* ------------------------------------------------------------------ *)
  (* Inner products with padded or shifted vectors *)

  Lemma dot_zeros : forall (p : list F) (r : nat), dot p (repeat zero r) = zero.
  Proof.
    induction p as [| x p ih]; intro r; [reflexivity |].
    destruct r as [| r]; cbn; [reflexivity | rewrite ih; field].
  Qed.

  Lemma dot_app_zeros : forall (L p : list F) (r : nat), dot p (L ++ repeat zero r) = dot p L.
  Proof.
    induction L as [| l L ih]; intros p r.
    + cbn [app]. rewrite dot_zeros, (@dot_nil_r F zero add mul). reflexivity.
    + destruct p as [| x p]; [reflexivity |]. cbn. rewrite ih. reflexivity.
  Qed.

  Lemma dot_skip : forall (r : nat) (p L : list F), dot p (repeat zero r ++ L) = dot (skipn r p) L.
  Proof.
    induction r as [| r ih]; intros p L; [reflexivity |].
    destruct p as [| x p]; [reflexivity |]. cbn. rewrite ih. field.
  Qed.

  Lemma dot_cons2 : forall (q L : list F) (a b : F),
    dot q (a :: b :: L) = nth 0 q zero * a + nth 1 q zero * b + dot (skipn 2 q) L.
  Proof.
    intros q L a b. destruct q as [| q0 [| q1 q']]; cbn; field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Indices of cube points, and tables read off rows *)

  Fixpoint bidx (b : list F) : nat :=
    match b with
    | [] => 0
    | x :: b' => (if Fdec x one then 1 else 0) + 2 * bidx b'
    end.

  Lemma bidx_pt : forall l i, (i < 2 ^ l)%nat -> bidx (pt l i) = i.
  Proof.
    induction l as [| l ih]; intros i hi.
    + cbn in hi. cbn. lia.
    + cbn [CubeIndex.pt bidx]. rewrite (ih _ (@div2_lt l i hi)).
      pose proof (Nat.div2_odd i) as e. unfold CubeIndex.bit.
      destruct (Nat.odd i) eqn:eo.
      - destruct (Fdec one one) as [_ | n]; [| contradiction]. cbn in e. lia.
      - destruct (Fdec zero one) as [e0 | _];
          [exfalso; exact (@zero_neq_one F eq zero one _ e0) | cbn in e; lia].
  Qed.

  Definition loE (M lo : nat) : nat := Nat.min lo M.
  Definition hiE (M lo : nat) : nat := (M - Nat.min lo M)%nat.

  Variable P : nat -> list F.

  Definition rdtab (start M lo : nat) (b : list F) : F :=
    nth (bidx (firstn (loE M lo) b)) (P (start + bidx (skipn (loE M lo) b))) zero.

  Lemma rdtab_spec : forall start M lo y t, (y < 2 ^ loE M lo)%nat -> (t < 2 ^ hiE M lo)%nat ->
    nth y (P (start + t)) zero = rdtab start M lo (pt (loE M lo) y ++ pt (hiE M lo) t).
  Proof.
    intros start M lo y t hy ht. unfold rdtab.
    rewrite firstn_app, (@pt_length F zero one), Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
    rewrite (firstn_all2 (n := loE M lo)) by (rewrite (@pt_length F zero one); lia).
    rewrite skipn_app, (@pt_length F zero one), Nat.sub_diag. cbn [skipn].
    rewrite (skipn_all2 (n := loE M lo)) by (rewrite (@pt_length F zero one); lia). cbn [app].
    rewrite (bidx_pt _ _ hy), (bidx_pt _ _ ht). reflexivity.
  Qed.

  Lemma bidx_lt : forall b : list F, (bidx b < 2 ^ length b)%nat.
  Proof.
    induction b as [| x b ih]; cbn [bidx length Nat.pow]; [lia |].
    destruct (Fdec x one); lia.
  Qed.

  (* the table depends only on the rows start .. start + 2^hiE - 1 *)
  Lemma rdtab_rows : forall (P' : nat -> list F) (start M lo : nat) (b : list F),
    length b = M ->
    (forall i, (start <= i < start + 2 ^ hiE M lo)%nat -> P i = P' i) ->
    rdtab start M lo b =
    nth (bidx (firstn (loE M lo) b)) (P' (start + bidx (skipn (loE M lo) b))%nat) zero.
  Proof.
    intros P' start M lo b hb hP. unfold rdtab. rewrite hP; [reflexivity |].
    pose proof (bidx_lt (skipn (loE M lo) b)) as h. rewrite length_skipn, hb in h.
    unfold hiE, loE in *. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Tensor claims *)

  Variable kind : nat -> bool.
  Variable Lt : nat -> list F.
  Local Notation gtval := (@gtval F zero add mul P kind Lt).
  Local Notation Lof := (@Lof F kind Lt).

  Lemma gtval_app : forall cl cl' : list gterm, gtval (cl ++ cl') = gtval cl + gtval cl'.
  Proof. induction cl as [| t cl ih]; intro cl'; cbn; [field | rewrite ih; field]. Qed.

  Lemma gtval_map : forall {A : Type} (f : A -> gterm) (l : list A),
    gtval (map f l) = fsum (map (fun t => tcoef (f t) * dot (P (trow (f t))) (Lof (f t))) l).
  Proof. intros A f; induction l as [| t l ih]; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Definition eqvec (lo : nat) (xlo : list F) : list F := map (fun y => eqp (pt lo y) xlo) (seq 0 (2 ^ lo)).

  Definition lovec (M lo : nat) (x : list F) : list F :=
    eqvec (loE M lo) (firstn (loE M lo) x) ++ repeat zero (2 ^ lo - 2 ^ loE M lo).

  Definition tabt (slot start : nat) (coef : F) (M lo : nat) (x : list F) : list gterm :=
    map (fun t => mk_gterm slot (start + t) (coef * eqp (pt (hiE M lo) t) (skipn (loE M lo) x)) [])
        (seq 0 (2 ^ hiE M lo)).

  Theorem tensor_claim : forall (slot start : nat) (coef : F) (M lo : nat) (x : list F) (T : list F -> F),
    kind slot = false -> Lt slot = lovec M lo x -> length x = M ->
    (forall y t, (y < 2 ^ loE M lo)%nat -> (t < 2 ^ hiE M lo)%nat ->
       nth y (P (start + t)) zero = T (pt (loE M lo) y ++ pt (hiE M lo) t)) ->
    gtval (tabt slot start coef M lo x) = coef * mle M T x.
  Proof.
    intros slot start coef M lo x T hk hL hx hread.
    assert (hM : M = (loE M lo + hiE M lo)%nat) by (unfold loE, hiE; lia).
    assert (hxs : x = firstn (loE M lo) x ++ skipn (loE M lo) x) by (symmetry; apply firstn_skipn).
    assert (hfl : length (firstn (loE M lo) x) = loE M lo) by (rewrite length_firstn; unfold loE; lia).
    rewrite hxs at 2. rewrite hM at 2.
    rewrite (@mle_rows F zero one add mul sub div opp inv Hf (loE M lo) (hiE M lo) T P
               (fun _ => eqvec (loE M lo) (firstn (loE M lo) x)) 0%nat (fun t => (start + t)%nat)
               (firstn (loE M lo) x) (skipn (loE M lo) x) hfl hread eq_refl).
    rewrite (@tval_map F zero add mul).
    unfold tabt. rewrite gtval_map. cbn [tcoef trow].
    rewrite <-(@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros t _.
    unfold SlotKinds.Lof. cbn [tslot]. rewrite hk, hL. unfold lovec. rewrite dot_app_zeros. field.
  Qed.

  Lemma tabt_terms : forall slot start coef M lo x t, In t (tabt slot start coef M lo x) ->
    tslot t = slot /\ exists j, (j < 2 ^ hiE M lo)%nat /\ trow t = (start + j)%nat.
  Proof.
    intros slot start coef M lo x t h. unfold tabt in h. apply in_map_iff in h.
    destruct h as (j & <- & hj). apply in_seq in hj. cbn. split; [reflexivity | exists j; split; [lia | reflexivity]].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The mask-table row *)

  Variable tg : F.

  Definition ment (Pm : list F) (e : nat) : F := nth (2 * e) Pm zero + tg * nth (2 * e + 1) Pm zero.

  Definition unitv (e : nat) : list F := repeat zero (2 * e) ++ [one; tg].

  Lemma dot_unitv : forall Pm e, dot Pm (unitv e) = ment Pm e.
  Proof.
    intros Pm e. unfold unitv, ment. rewrite dot_skip, dot_cons2, !nth_skipn.
    rewrite (@dot_nil_r F zero add mul). rewrite Nat.add_0_r. field.
  Qed.

  Definition gfunv (off : nat) (cf : list F) : list F :=
    repeat zero (2 * off) ++ flat_map (fun c => [c; c * tg]) cf.

  Lemma dot_flat : forall (cf q : list F) (s : nat),
    dot (skipn (2 * s) q) (flat_map (fun c => [c; c * tg]) cf)
    = dot (map (fun i => ment q (s + i)) (seq 0 (length cf))) cf.
  Proof.
    induction cf as [| c cf ih]; intros q s.
    + cbn. apply (@dot_nil_r F zero add mul).
    + cbn [flat_map app length]. rewrite dot_cons2, !nth_skipn, skipn_skipn.
      replace (2 + 2 * s)%nat with (2 * S s)%nat by lia. rewrite (ih q (S s)).
      cbn [seq map]. rewrite <-seq_shift, map_map. cbn [LogDer.dot].
      rewrite (map_ext (fun i => ment q (s + S i)) (fun i => ment q (S s + i)))
        by (intro i; f_equal; lia).
      assert (e : ment q (s + 0) = nth (2 * s) q zero + tg * nth (2 * s + 1) q zero)
        by (unfold ment; rewrite Nat.add_0_r; reflexivity).
      rewrite e, !Nat.add_0_r. field.
  Qed.

  Lemma dot_gfunv : forall Pm off cf,
    dot Pm (gfunv off cf) = dot (map (fun i => ment Pm (off + i)) (seq 0 (length cf))) cf.
  Proof. intros Pm off cf. unfold gfunv. rewrite dot_skip. apply dot_flat. Qed.

  (* [r_j, r_j^2, .., r_j^(d_j)] for every variable j *)
  Fixpoint fnl (degs : list nat) (r : list F) : list F :=
    match degs, r with
    | d :: ds, ri :: r' => pows ri d ri ++ fnl ds r'
    | _, _ => []
    end.

  Definition funcv (degs : list nat) (r : list F) : list F := one :: fnl degs r.

  Fixpoint chunks (degs : list nat) (l : list F) : list (list F) :=
    match degs with
    | [] => []
    | d :: ds => firstn d l :: chunks ds (skipn d l)
    end.

  Fixpoint dsumL (degs : list nat) : nat :=
    match degs with
    | [] => 0
    | d :: ds => d + dsumL ds
    end.

  Lemma firstn_add : forall (a b : nat) (l : list F), firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
  Proof.
    induction a as [| a ih]; intros b l; [reflexivity |].
    destruct l as [| x l]; [cbn; rewrite firstn_nil; reflexivity |]. cbn. rewrite ih. reflexivity.
  Qed.

  Lemma concat_chunks : forall degs l, concat (chunks degs l) = firstn (dsumL degs) l.
  Proof.
    induction degs as [| d ds ih]; intro l; cbn [chunks concat dsumL]; [reflexivity |].
    rewrite ih, firstn_add. reflexivity.
  Qed.

  Lemma chunks_shaped : forall degs l, (dsumL degs <= length l)%nat ->
    @shaped F degs (chunks degs l).
  Proof.
    induction degs as [| d ds ih]; intros l hl; cbn [chunks]; constructor.
    + rewrite length_firstn. cbn in hl. lia.
    + apply ih. rewrite length_skipn. cbn in hl. lia.
  Qed.

  Lemma chunks_length : forall degs l, length (chunks degs l) = length degs.
  Proof. induction degs as [| d ds ih]; intro l; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Lemma shaped_nth : forall degs (ls : list (list F)), @shaped F degs ls ->
    forall i, (i < length degs)%nat -> length (nth i ls []) = nth i degs 0%nat.
  Proof.
    intros degs ls h; induction h as [| d l degs ls hd h ih]; intros i hi; [cbn in hi; lia |].
    destruct i as [| i]; [exact hd | apply ih; cbn in hi; lia].
  Qed.

  Lemma maskfn_chunks : forall degs l r, (dsumL degs <= length l)%nat ->
    maskfn (chunks degs l) r = fnl degs r.
  Proof.
    induction degs as [| d ds ih]; intros l r hl; cbn [chunks LayoutLemmas.maskfn fnl]; [reflexivity |].
    destruct r as [| ri r']; [reflexivity |].
    rewrite length_firstn. cbn in hl. replace (Nat.min d (length l)) with d by lia.
    rewrite ih by (rewrite length_skipn; lia). reflexivity.
  Qed.

  Lemma fnl_length : forall degs r, length r = length degs -> length (fnl degs r) = dsumL degs.
  Proof.
    induction degs as [| d ds ih]; intros r hl; destruct r as [| ri r']; cbn in hl; try lia; [reflexivity |].
    cbn [fnl dsumL]. rewrite length_app, (@pows_length F mul), ih by lia. reflexivity.
  Qed.

  (* the sumcheck mask stored at entries off, off + 1, .. of the row *)
  Definition maskA0 (Pm : list F) (off : nat) : F := ment Pm off.
  Definition maskCs (Pm : list F) (off : nat) (degs : list nat) : list (list F) :=
    chunks degs (map (fun i => ment Pm (off + 1 + i)) (seq 0 (dsumL degs))).

  Theorem mask_row_gmask : forall (Pm : list F) (off : nat) (degs : list nat) (r : list F),
    length r = length degs ->
    gmask (maskA0 Pm off) (maskCs Pm off degs) r = dot Pm (gfunv off (funcv degs r)).
  Proof.
    intros Pm off degs r hr. unfold maskA0, maskCs.
    set (E := map (fun i => ment Pm (off + 1 + i)) (seq 0 (dsumL degs))).
    assert (hE : length E = dsumL degs) by (unfold E; rewrite length_map, length_seq; reflexivity).
    rewrite (@gmask_functional F zero one add mul sub div opp inv Hf).
    rewrite concat_chunks, (firstn_all2 (n := dsumL degs)) by lia.
    rewrite maskfn_chunks by lia.
    rewrite dot_gfunv. unfold funcv. cbn [length seq map LogDer.dot].
    rewrite (fnl_length degs r hr), <-seq_shift, map_map.
    rewrite Nat.add_0_r. f_equal.
    unfold E. f_equal. apply map_ext. intro i. f_equal. lia.
  Qed.

End RowLayout.
