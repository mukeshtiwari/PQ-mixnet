(* Round messages as evaluations (fp_core.py: interp, sc_verify).

   The implementation sends, in each round, the values of the round
   polynomial at 0, 2, 3, .., d; the value at 1 is claim minus the value at
   0, and the next claim is the Lagrange interpolant through 0, 1, .., d
   evaluated at the challenge. The soundness proofs use coefficient lists.

   - interpF vals x     the Lagrange formula of fp_core.interp, over a field;
   - lagr vals          the interpolating polynomial as a coefficient list;
   - lagr_eval          peval (lagr vals) x = interpF vals x;
   - lagr_nodes         peval (lagr vals) (nF k) = vals_k for k < length vals,
                        if 1, .., length vals - 1 are non-zero in the field;
   - lagr_length        length (lagr vals) <= length vals;
   - esc_verify         the verifier of the rounds, on evaluations;
   - esc_sound          if esc_verify accepts with final claim c, then the
                        coefficient lists lagr (..) of its messages pass
                        sc_verify of Sumcheck.v with the same final claim, and
                        have length at most one more than the message.
   So the soundness theorems, stated for coefficient lists of bounded
   length, apply to the verifier of the implementation. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle PolyFun Sumcheck Negacyclic.
Import ListNotations.

Section Interp.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation fsum := (@fsum F zero add).
  Local Notation nF := (@nF F zero one add).
  Local Notation peval := (@eval F zero add mul).
  Local Notation pmul := (@pmul F zero add mul).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation sc_verify := (@sc_verify F zero one add mul Fdec).

  (* prod_(j in l, j <> i) (x - j) *)
  Fixpoint numL (i : nat) (l : list nat) (x : F) : F :=
    match l with
    | [] => one
    | j :: l' => if Nat.eqb j i then numL i l' x else (x - nF j) * numL i l' x
    end.

  (* the same as a coefficient list *)
  Fixpoint lnumL (i : nat) (l : list nat) : list F :=
    match l with
    | [] => [one]
    | j :: l' => if Nat.eqb j i then lnumL i l' else pmul (lnumL i l') [opp (nF j); one]
    end.

  Lemma lnumL_eval : forall i l x, peval (lnumL i l) x = numL i l x.
  Proof.
    intros i; induction l as [| j l ih]; intro x; cbn [lnumL numL].
    + cbn. field.
    + destruct (Nat.eqb j i); [apply ih |].
      rewrite (@eval_pmul F zero one add mul sub div opp inv Hf), ih. cbn. field.
  Qed.

  Lemma lnumL_length : forall i l, (length (lnumL i l) <= S (length l))%nat.
  Proof.
    intros i; induction l as [| j l ih]; cbn [lnumL length]; [cbn; lia |].
    destruct (Nat.eqb j i); [lia |].
    pose proof (@length_pmul F zero add mul (lnumL i l) [opp (nF j); one] ltac:(discriminate)) as h.
    cbn [length] in h. lia.
  Qed.

  Lemma numL_root : forall i k l, In k l -> k <> i -> numL i l (nF k) = zero.
  Proof.
    intros i k; induction l as [| j l ih]; intros hin hne; [contradiction |].
    cbn [numL]. destruct hin as [e | hin].
    + subst j. rewrite (proj2 (Nat.eqb_neq k i) hne). field.
    + destruct (Nat.eqb j i); [apply ih; assumption |]. rewrite (ih hin hne). field.
  Qed.

  Variable D : nat.
  Hypothesis Hchar : forall k, (0 < k <= D)%nat -> nF k <> zero.

  Lemma numL_self : forall i l, (i <= D)%nat -> (forall j, In j l -> (j <= D)%nat) -> numL i l (nF i) <> zero.
  Proof.
    intros i; induction l as [| j l ih]; intros hi hl; cbn [numL].
    + intro h. apply (@zero_neq_one F eq zero one _). symmetry. exact h.
    + destruct (Nat.eqb j i) eqn:e; [apply ih; [exact hi | intros; apply hl; right; assumption] |].
      apply Nat.eqb_neq in e.
      apply (@mul_nonzero F zero one add mul sub div opp inv Hf).
      - intro h0. apply e. symmetry.
        apply (@nF_inj F zero one add mul sub div opp inv Hf D Hchar i j hi (hl j (or_introl eq_refl))).
        transitivity (nF i - nF j + nF j); [field |]. rewrite h0. field.
      - apply ih; [exact hi | intros; apply hl; right; assumption].
  Qed.

  (* the Lagrange interpolant through the nodes 0 .. n-1 *)
  Definition coefL (vals : list F) (i : nat) : F :=
    nth i vals zero * inv (numL i (seq 0 (length vals)) (nF i)).

  Definition interpF (vals : list F) (x : F) : F :=
    fsum (map (fun i => nth i vals zero * (numL i (seq 0 (length vals)) x
                                           * inv (numL i (seq 0 (length vals)) (nF i))))
              (seq 0 (length vals))).

  Fixpoint lagrK (vals : list F) (ks : list nat) : list F :=
    match ks with
    | [] => []
    | i :: ks' => padd (pscale (coefL vals i) (lnumL i (seq 0 (length vals)))) (lagrK vals ks')
    end.

  Definition lagr (vals : list F) : list F := lagrK vals (seq 0 (length vals)).

  Lemma lagrK_eval : forall vals ks x,
    peval (lagrK vals ks) x = fsum (map (fun i => coefL vals i * numL i (seq 0 (length vals)) x) ks).
  Proof.
    intros vals; induction ks as [| i ks ih]; intro x; [reflexivity |].
    cbn [lagrK map LogDer.fsum].
    rewrite (@eval_padd F zero one add mul sub div opp inv Hf), (@eval_pscale F zero one add mul sub div opp inv Hf),
            lnumL_eval, ih. reflexivity.
  Qed.

  Theorem lagr_eval : forall vals x, peval (lagr vals) x = interpF vals x.
  Proof.
    intros vals x. unfold lagr, interpF. rewrite lagrK_eval.
    apply (@fsum_map_ext F zero add). intros i _. unfold coefL. ring.
  Qed.

  Lemma lagrK_length : forall vals ks, (length (lagrK vals ks) <= S (length vals))%nat.
  Proof.
    intros vals; induction ks as [| i ks ih]; cbn [lagrK length]; [lia |].
    rewrite (@length_padd F add), (@length_pscale F mul).
    pose proof (lnumL_length i (seq 0 (length vals))) as h. rewrite length_seq in h. lia.
  Qed.

  Lemma lagrK_length_nodes : forall vals ks, (forall i, In i ks -> (i < length vals)%nat) ->
    (length (lagrK vals ks) <= length vals)%nat.
  Proof.
    intros vals; induction ks as [| i ks ih]; intro hks; cbn [lagrK length]; [lia |].
    rewrite (@length_padd F add), (@length_pscale F mul).
    assert (hi : (i < length vals)%nat) by (apply hks; left; reflexivity).
    assert (sk : forall l, In i l -> NoDup l -> (length (lnumL i l) <= length l)%nat).
    { induction l as [| j l ihl]; intros hin hnd; [contradiction |].
      inversion hnd as [| ? ? hj hnd']; subst. cbn [lnumL length].
      destruct (Nat.eqb j i) eqn:e.
      + apply Nat.eqb_eq in e. subst j. pose proof (lnumL_length i l). lia.
      + apply Nat.eqb_neq in e. destruct hin as [-> | hin]; [contradiction |].
        pose proof (@length_pmul F zero add mul (lnumL i l) [opp (nF j); one] ltac:(discriminate)) as h.
        cbn [length] in h. pose proof (ihl hin hnd'). lia. }
    pose proof (sk (seq 0 (length vals)) ltac:(apply in_seq; lia) (seq_NoDup _ _)) as h.
    rewrite length_seq in h.
    pose proof (ih (fun j hj => hks j (or_intror hj))). lia.
  Qed.

  Theorem lagr_length : forall vals, (length (lagr vals) <= length vals)%nat.
  Proof.
    intro vals. unfold lagr. apply lagrK_length_nodes. intros i hi. apply in_seq in hi. lia.
  Qed.

  Theorem lagr_nodes : forall vals k, (length vals <= S D)%nat -> (k < length vals)%nat ->
    peval (lagr vals) (nF k) = nth k vals zero.
  Proof.
    intros vals k hD hk. unfold lagr. rewrite lagrK_eval.
    assert (hnodes : forall j, In j (seq 0 (length vals)) -> (j <= D)%nat) by (intros j hj; apply in_seq in hj; lia).
    rewrite (@fsum_map_ext F zero add _ _
               (fun i => (if Nat.eq_dec k i then one else zero) * nth k vals zero)).
    + apply (@fsum_indicator F zero one add mul sub div opp inv Hf nat Nat.eq_dec (fun _ => nth k vals zero) k);
        [apply seq_NoDup | apply in_seq; lia].
    + intros i hi. unfold coefL. destruct (Nat.eq_dec k i) as [<- | hne].
      - field. apply numL_self; [lia | exact hnodes].
      - rewrite (numL_root i k (seq 0 (length vals)) ltac:(apply in_seq; lia) hne). field.
        apply numL_self; [apply hnodes; exact hi | exact hnodes].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The verifier of the rounds on evaluations *)

  (* the values at 0, 1, .., d from the message (values at 0, 2, .., d) *)
  Definition fullvals (claim : F) (ev : list F) : list F :=
    match ev with
    | [] => []
    | e0 :: rest => e0 :: (claim - e0) :: rest
    end.

  Fixpoint esc_verify (msgs : list (list F)) (chals : list F) (claim : F) : option F :=
    match msgs, chals with
    | [], [] => Some claim
    | ev :: ms, r :: cs =>
        match ev with
        | [] => None
        | _ => esc_verify ms cs (interpF (fullvals claim ev) r)
        end
    | _, _ => None
    end.

  (* the coefficient lists the verifier implicitly accepts *)
  Fixpoint coefmsgs (msgs : list (list F)) (chals : list F) (claim : F) : list (list F) :=
    match msgs, chals with
    | ev :: ms, r :: cs =>
        lagr (fullvals claim ev) :: coefmsgs ms cs (interpF (fullvals claim ev) r)
    | _, _ => []
    end.

  Lemma fullvals_length : forall claim ev, ev <> [] -> length (fullvals claim ev) = S (length ev).
  Proof. intros claim [| e0 rest] h; [contradiction | reflexivity]. Qed.

  Theorem esc_sound : forall msgs chals claim c,
    Forall (fun ev => (length ev <= D)%nat) msgs ->
    esc_verify msgs chals claim = Some c ->
    sc_verify (coefmsgs msgs chals claim) chals claim = Some c /\
    Forall2 (fun ev p => (length p <= S (length ev))%nat) msgs (coefmsgs msgs chals claim).
  Proof.
    induction msgs as [| ev ms ih]; intros chals claim c hlen hv; destruct chals as [| r cs]; cbn in hv;
      try discriminate.
    + injection hv as <-. split; [reflexivity | constructor].
    + destruct ev as [| e0 rest]; [discriminate |].
      inversion hlen as [| ? ? hl hls]; subst.
      set (vals := fullvals claim (e0 :: rest)) in *.
      assert (hvl : length vals = S (length (e0 :: rest))) by (apply fullvals_length; discriminate).
      destruct (ih cs (interpF vals r) c hls hv) as [h1 h2].
      cbn [length] in hl, hvl.
      cbn [coefmsgs]. fold vals. split.
      - cbn [Sumcheck.sc_verify].
        assert (e0v : peval (lagr vals) zero = e0).
        { change zero with (nF 0) at 2. rewrite (lagr_nodes vals 0 ltac:(lia) ltac:(lia)). reflexivity. }
        assert (e1v : peval (lagr vals) one = claim - e0).
        { transitivity (peval (lagr vals) (nF 1)); [f_equal; cbn; field |].
          rewrite (lagr_nodes vals 1 ltac:(lia) ltac:(lia)). reflexivity. }
        assert (hc : @feqb F Fdec (peval (lagr vals) zero + peval (lagr vals) one) claim = true).
        { apply (@feqb_true F Fdec). rewrite e0v, e1v. field. }
        rewrite hc, lagr_eval. exact h1.
      - constructor; [| exact h2].
        pose proof (lagr_length vals) as h. rewrite hvl in h. exact h.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Uniqueness: the interpolant of the values of a polynomial of degree
     at most d at 0 .. d is that polynomial. *)

  Lemma eval_zeros : forall n x, peval (repeat zero n) x = zero.
  Proof. induction n as [| n ih]; intro x; cbn; [reflexivity | rewrite ih; field]. Qed.

  Definition padto (L : nat) (q : list F) : list F := q ++ repeat zero (L - length q).

  Lemma eval_padto : forall L q x, peval (padto L q) x = peval q x.
  Proof.
    intros L q x. unfold padto. rewrite (@peval_app F zero one add mul sub div opp inv Hf), eval_zeros. field.
  Qed.

  Lemma length_padto : forall L q, (length q <= L)%nat -> length (padto L q) = L.
  Proof. intros L q h. unfold padto. rewrite length_app, repeat_length. lia. Qed.

  Lemma NoDup_map_on' : forall {R V : Type} (f : R -> V) (l : list R), NoDup l ->
    (forall x x', In x l -> In x' l -> f x = f x' -> x = x') -> NoDup (map f l).
  Proof.
    intros R V f l h; induction h as [| x l hx h ih]; intro hinj; cbn; constructor.
    + intro hin. apply in_map_iff in hin. destruct hin as (x' & e & hx').
      assert (x' = x) by (apply hinj; [right; exact hx' | left; reflexivity | exact e]). subst x'. contradiction.
    + apply ih. intros a a' ha ha'. apply hinj; right; assumption.
  Qed.

  Theorem interp_unique : forall vals p, (length vals <= S D)%nat -> (length p <= length vals)%nat ->
    (forall k, (k < length vals)%nat -> nth k vals zero = peval p (nF k)) ->
    forall x, interpF vals x = peval p x.
  Proof.
    intros vals p hD hp hv x. rewrite <-lagr_eval.
    set (L := length vals).
    assert (e : padto L (lagr vals) = padto L p).
    { apply (@poly_eq_of_evals F zero one add mul sub div opp inv Fdec Hf L (map nF (seq 0 L))).
      + apply NoDup_map_on'; [apply seq_NoDup |].
        intros i j hi hj e. apply in_seq in hi, hj.
        apply (@nF_inj F zero one add mul sub div opp inv Hf D Hchar i j); [lia | lia | exact e].
      + rewrite length_map, length_seq. reflexivity.
      + apply length_padto. apply lagr_length.
      + apply length_padto. exact hp.
      + intros z hz. apply in_map_iff in hz. destruct hz as (k & <- & hk). apply in_seq in hk.
        rewrite !eval_padto, (lagr_nodes vals k hD ltac:(lia)). apply hv. lia. }
    rewrite <-(eval_padto L (lagr vals)), e, eval_padto. reflexivity.
  Qed.

End Interp.
