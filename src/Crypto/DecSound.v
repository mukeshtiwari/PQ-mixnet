(* Knowledge soundness of the decryption proof, sumcheck layer (paper,
   Section 7 and Theorem 7.1, without the opening).

   Statement: the public key (a, b) and, for every ciphertext i < tau, its
   first component us i and the partial decryption ts i. First message of
   the prover: digit tables dts (kd tables on the cube of m = n1 + ell
   variables), and tables stab, etab of the key share and its noise on the
   cube of n1 variables. The decoded witness is

     sK, eK                  the coefficient lists of stab, etab
     Ecoef i x               = sum_d base^d * digit_d(x, i) - offB

   and it is a witness when
     the range polynomial phiR vanishes on every digit,
     stab and etab are ternary,
     (D)  ts i = sK * us i + p * E_i   coefficient by coefficient,
     (K)  b = a * sK + p * eK.

   Protocol with an ideal opening (the linear claims are checked against
   the tables):
     challenge th = (theta1 ++ theta, theta2);  the two compressed claims
       mle Dtab (theta1 ++ theta) = 0  and  mle Ktab theta2 = 0,
       where Dtab and Ktab are the tables of the defects of (D) and (K);
     zero-test sumcheck for the digits (ZeroTest.v, phi = phiR);
     zero-test sumcheck for stab, etab (phi = w^3 - w).

   Theorem dec_sound: if the first message is not a witness, the verifier
   accepts for at most dec_bound challenge tuples. As fractions of all
   tuples its terms are  m/|F| and n1/|F| (theta),  (m + 1)/|F| and
   ((base + 1) m + base)/|F| (digits),  (n1 + 1)/|F| and (4 n1 + 3)/|F|
   (key share): together the numerator (base + 3) m + 6 n1 + base + 5 of
   Theorem 7.1, without its two opening lines.

   Also here: the range polynomial rangep base = prod_(v < base) (X - v)
   with its roots (rangep_root), and exactness of the digit decomposition
   over the integers (dval_bound).

   Not here: that the verifier's two linear claims on committed rows equal
   the mle of the defect tables (this uses nmul_adjoint, as in the shuffle
   proof), and the opening. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Bgv Sumcheck SumcheckMask SumcheckSound PolyFun MaskedExt CubeIndex EqBatch ZeroTest.
Import ListNotations.

Section DecSound.

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
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation pt := (@pt F zero one).
  Local Notation nmul := (@nmul F zero add mul opp).
  Local Notation tern := (@tern F zero one opp).
  Local Notation pmul := (@pmul F zero add mul).
  Local Notation AccZ := (@AccZ F zero one add mul sub Fdec).

  (* ------------------------------------------------------------------ *)
  (* The range polynomial and the digit decomposition *)

  Fixpoint rangep (k : nat) : list F :=
    match k with
    | 0 => [one]
    | S k' => pmul (rangep k') [opp (nF k'); one]
    end.

  Lemma rangep_eval : forall k x, peval (rangep (S k)) x = peval (rangep k) x * (x - nF k).
  Proof.
    intros k x. cbn [rangep]. rewrite (@eval_pmul F zero one add mul sub div opp inv Hf). cbn. field.
  Qed.

  Theorem rangep_root : forall k x, peval (rangep k) x = zero <-> exists v, (v < k)%nat /\ x = nF v.
  Proof.
    induction k as [| k ih]; intro x.
    + cbn. split.
      - intro e. exfalso. apply (@zero_neq_one F eq zero one _). rewrite <-e. field.
      - intros (v & hv & _). lia.
    + rewrite rangep_eval. split.
      - intro e. destruct (Fdec (peval (rangep k) x) zero) as [e0 | e0].
        * apply ih in e0. destruct e0 as (v & hv & ev). exists v; split; [lia | exact ev].
        * destruct (Fdec (x - nF k) zero) as [e1 | e1].
          -- exists k; split; [lia |]. assert (hx : x = (x - nF k) + nF k) by field. rewrite hx, e1. field.
          -- exfalso. exact (@mul_nonzero F zero one add mul sub div opp inv Hf _ _ e0 e1 e).
      - intros (v & hv & ev). destruct (Nat.eq_dec v k) as [-> | hne].
        * rewrite ev. field.
        * assert (h0 : peval (rangep k) x = zero) by (apply ih; exists v; split; [lia | exact ev]).
          rewrite h0. field.
  Qed.

  Lemma rangep_length : forall k, (length (rangep k) <= S k)%nat.
  Proof.
    induction k as [| k ih]; [cbn; lia |]. cbn [rangep].
    pose proof (@length_pmul F zero add mul (rangep k) [opp (nF k); one] ltac:(discriminate)) as h.
    cbn [length] in h. lia.
  Qed.

  (* digits below the base represent an integer below base^k: no slack *)
  Fixpoint dval (base : nat) (vs : list nat) : nat :=
    match vs with
    | [] => 0
    | v :: vs' => v + base * dval base vs'
    end.

  Theorem dval_bound : forall (base : nat) (vs : list nat),
    Forall (fun v => (v < base)%nat) vs -> (dval base vs < base ^ length vs)%nat.
  Proof.
    intros base vs h; induction h as [| v vs hv h ih]; cbn; [lia |]. nia.
  Qed.

  (* w^3 - w *)
  Definition phi3 : list F := [zero; opp one; zero; one].

  Lemma phi3_eval : forall w, peval phi3 w = w * w * w - w.
  Proof. intro w. unfold phi3. cbn. field. Qed.

  Lemma phi3_tern : forall w, ~ tern w -> peval phi3 w <> zero.
  Proof.
    intros w hn e. apply hn. apply (@cube_ternary F zero one add mul sub div opp inv Fdec Hf).
    rewrite phi3_eval in e. assert (hx : w * w * w = (w * w * w - w) + w) by field. rewrite hx, e. field.
  Qed.

  (* ------------------------------------------------------------------ *)

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.

  Variables (a b : list F) (pp offB : F).
  Variables n1 ell base kd : nat.
  Hypothesis Hn1 : (1 <= n1)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.

  (* statement *)
  Variables us ts : nat -> list F.
  (* first message *)
  Variable dts : list (list F -> F).
  Variables stab etab : list F -> F.
  Variable phiR : list F.
  Hypothesis HphiR : (length phiR <= S base)%nat.

  Definition sK : list F := map (fun x => stab (pt n1 x)) (seq 0 N).
  Definition eK : list F := map (fun x => etab (pt n1 x)) (seq 0 N).

  Fixpoint Esum (ds : list (list F -> F)) (d : nat) (bq : list F) : F :=
    match ds with
    | [] => zero
    | T :: ds' => nF (base ^ d) * T bq + Esum ds' (S d) bq
    end.

  Definition Ecoef (i x : nat) : F := Esum dts 0 (pt n1 x ++ pt ell i) - offB.

  Definition Dcoef (i x : nat) : F :=
    nth x (ts i) zero - nth x (nmul (us i) sK) zero - pp * Ecoef i x.
  Definition Kcoef (x : nat) : F :=
    nth x b zero - nth x (nmul a sK) zero - pp * nth x eK zero.

  Definition is_dec_witness : Prop :=
    (forall T, In T dts -> forall bq, In bq (cube m) -> peval phiR (T bq) = zero) /\
    (forall bq, In bq (cube n1) -> tern (stab bq) /\ tern (etab bq)) /\
    (forall i x, (i < tau)%nat -> (x < N)%nat -> Dcoef i x = zero) /\
    (forall x, (x < N)%nat -> Kcoef x = zero).

  (* the defect tables on the cube *)
  Variables Dtab Ktab : list F -> F.
  Hypothesis HD : forall i x, (i < tau)%nat -> (x < N)%nat -> Dtab (pt n1 x ++ pt ell i) = Dcoef i x.
  Hypothesis HK : forall x, (x < N)%nat -> Ktab (pt n1 x) = Kcoef x.

  (* challenge spaces *)
  Definition ThT : Type := (list F * list F)%type.
  Definition OTh : list ThT := list_prod (all_lists lf m) (all_lists lf n1).
  Definition GT : Type := ((list F * list F) * list F)%type.
  Definition OmG : list GT := list_prod (@C4Z F m lf dts) (@RZZ F m lf).
  Definition P2 : Type := (ThT * GT)%type.
  Definition OP2 : list P2 := list_prod OTh OmG.
  Definition OmT : list GT := list_prod (@C4Z F n1 lf [stab; etab]) (@RZZ F n1 lf).

  (* the prover *)
  Variable avsG : ThT -> list F.
  Variables a0G GGG : ThT -> F.
  Variable csG : ThT -> list (list F).
  Variables stratG zsG : ThT -> list F * list F -> list F -> list F.
  Variable avsT : P2 -> list F.
  Variables a0T GGT : P2 -> F.
  Variable csT : P2 -> list (list F).
  Variables stratT zsT : P2 -> list F * list F -> list F -> list F.

  Hypothesis HavsG : forall p, length (avsG p) = length dts.
  Hypothesis HcsG : forall p, length (csG p) = m.
  Hypothesis HdegG : forall p i, (i < m)%nat -> (length (nth i (csG p) []) <= degZ m base i)%nat.
  Hypothesis HmsgG : forall p c4 pre, (length (stratG p c4 pre) <= S (degZ m base (length pre)))%nat.
  Hypothesis HavsT : forall p, length (avsT p) = 2%nat.
  Hypothesis HcsT : forall p, length (csT p) = n1.
  Hypothesis HdegT : forall p i, (i < n1)%nat -> (length (nth i (csT p) []) <= degZ n1 3 i)%nat.
  Hypothesis HmsgT : forall p c4 pre, (length (stratT p c4 pre) <= S (degZ n1 3 (length pre)))%nat.

  Definition accTh (th : ThT) : Prop := mle m Dtab (fst th) = zero /\ mle n1 Ktab (snd th) = zero.

  Definition AccDec (w : P2 * GT) : Prop :=
    accTh (fst (fst w)) /\
    AccZ m phiR dts ThT avsG a0G GGG csG stratG zsG (fst (fst w)) (fst (snd (fst w))) (snd (snd (fst w))) /\
    AccZ n1 phi3 [stab; etab] P2 avsT a0T GGT csT stratT zsT (fst w) (fst (snd w)) (snd (snd w)).

  Definition bTh : nat :=
    (m * length lf ^ (m - 1) * length (all_lists lf n1) + n1 * length lf ^ (n1 - 1) * length (all_lists lf m))%nat.

  Definition dec_bound : nat :=
    (bTh * length OmG * length OmT
     + @boundZ F m base lf dts * length OTh * length OmT
     + @boundZ F n1 3 lf [stab; etab] * length OP2)%nat.

  Lemma pt_app_cube : forall x i, In (pt n1 x ++ pt ell i) (cube m).
  Proof.
    intros x i. unfold Mle.cube. apply all_lists_In. split.
    + rewrite length_app, !(@pt_length F zero one). reflexivity.
    + apply Forall_app. split.
      - pose proof (@pt_cube F zero one n1 x) as h. unfold Mle.cube in h. apply all_lists_In in h. tauto.
      - pose proof (@pt_cube F zero one ell i) as h. unfold Mle.cube in h. apply all_lists_In in h. tauto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the bound as a fraction: dec_bound / |challenges| = dec_K / |F| *)

  Definition dec_K : nat :=
    (m + n1 + (m + 1) + dsum (degZ m base) 0 m + (n1 + 1) + dsum (degZ n1 3) 0 n1)%nat.

  Lemma dsum_degZ : forall L D k i, (i + S k = L)%nat -> dsum (degZ L D) i (S k) = ((1 + D) * S k + D)%nat.
  Proof.
    intros L D; induction k as [| k ih]; intros i h.
    + cbn [dsum]. unfold degZ. replace (S i) with L by lia. rewrite Nat.eqb_refl. lia.
    + change (dsum (degZ L D) i (S (S k))) with (degZ L D i + dsum (degZ L D) (S i) (S k))%nat.
      rewrite (ih (S i)) by lia. unfold degZ. rewrite (proj2 (Nat.eqb_neq _ _)) by lia. lia.
  Qed.

  (* the numerator of Theorem 7.1 without its two opening lines *)
  Theorem dec_K_value : dec_K = ((base + 3) * m + 6 * n1 + base + 5)%nat.
  Proof.
    unfold dec_K.
    replace (dsum (degZ m base) 0 m) with (dsum (degZ m base) 0 (S (m - 1))) by (f_equal; lia).
    rewrite (dsum_degZ m base (m - 1) 0 ltac:(lia)).
    replace (dsum (degZ n1 3) 0 n1) with (dsum (degZ n1 3) 0 (S (n1 - 1))) by (f_equal; lia).
    rewrite (dsum_degZ n1 3 (n1 - 1) 0 ltac:(lia)).
    replace (S (m - 1)) with m by lia. replace (S (n1 - 1)) with n1 by lia. nia.
  Qed.

  Theorem dec_bound_fraction : (dec_bound * length lf = dec_K * length (list_prod OP2 OmT))%nat.
  Proof.
    unfold dec_bound, dec_K, bTh, OP2, OTh, OmG, OmT, boundZ, C4Z, RZZ, GT, ThT, P2.
    repeat (rewrite length_prod || rewrite all_lists_length). cbn [length].
    set (q := length lf). set (L := length dts).
    set (dG := dsum (degZ m base) 0 m). set (dT := dsum (degZ n1 3) 0 n1).
    assert (hm : (q ^ m = q * q ^ (m - 1))%nat) by (replace m with (S (m - 1)) at 1 by lia; reflexivity).
    assert (hn : (q ^ n1 = q * q ^ (n1 - 1))%nat) by (replace n1 with (S (n1 - 1)) at 1 by lia; reflexivity).
    assert (hGL : (q ^ (m + (L + 1) - 1) = q ^ m * q ^ L)%nat)
      by (replace (m + (L + 1) - 1)%nat with (m + L)%nat by lia; apply Nat.pow_add_r).
    assert (hL1 : (q ^ (L + 1) = q ^ L * q)%nat) by (rewrite Nat.pow_add_r; cbn; lia).
    assert (hT3 : (q ^ (n1 + (2 + 1) - 1) = q ^ n1 * q ^ 2)%nat)
      by (replace (n1 + (2 + 1) - 1)%nat with (n1 + 2)%nat by lia; apply Nat.pow_add_r).
    assert (h3 : (q ^ (2 + 1) = q ^ 2 * q)%nat) by (cbn; lia).
    repeat (rewrite length_prod || rewrite all_lists_length). fold q.
    rewrite hGL, hL1, hT3, h3. rewrite hm, hn. ring.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* the range proof is exact: digits in 0..base-1 give E = v - offB with 0 <= v < base^kd *)

  Lemma nF_mul : forall i j, nF (i * j)%nat = nF i * nF j.
  Proof.
    induction i as [| i ih]; intro j; cbn [Nat.mul nF]; [field |].
    rewrite (@nF_add F zero one add mul sub div opp inv Hf), ih. field.
  Qed.

  Lemma Esum_digits : forall ds d bq,
    (forall T, In T ds -> exists v, (v < base)%nat /\ T bq = nF v) ->
    exists v, (v < base ^ length ds)%nat /\ Esum ds d bq = nF (base ^ d * v).
  Proof.
    induction ds as [| T ds ih]; intros d bq h.
    - exists 0%nat. split; [cbn; lia |]. cbn [Esum]. rewrite Nat.mul_0_r. reflexivity.
    - destruct (h T (or_introl eq_refl)) as (v0 & hv0 & e0).
      destruct (ih (S d) bq (fun T' hT' => h T' (or_intror hT'))) as (w & hw & ew).
      exists (v0 + base * w)%nat. split.
      + cbn [length Nat.pow]. nia.
      + cbn [Esum]. rewrite e0, ew, <-nF_mul.
        rewrite <-(@nF_add F zero one add mul sub div opp inv Hf). f_equal. cbn [Nat.pow]. nia.
  Qed.

  (* Theorem 7.1, "the range proof is exact": if the range polynomial vanishes on every digit, every
     noise coefficient is v - offB for a natural number v < base^kd (kd = number of digit tables).
     With offB = B/2, B = base^kd and B < q this is -B/2 <= E < B/2 over the integers. *)
  Theorem range_exact : phiR = rangep base ->
    (forall T, In T dts -> forall bq, In bq (cube m) -> peval phiR (T bq) = zero) ->
    forall i x, exists v, (v < base ^ length dts)%nat /\ Ecoef i x = nF v - offB.
  Proof.
    intros eR h i x.
    destruct (Esum_digits dts 0 (pt n1 x ++ pt ell i)) as (v & hv & ev).
    { intros T hT. apply rangep_root. rewrite <-eR. apply h; [exact hT | apply pt_app_cube]. }
    exists v. split; [exact hv |]. unfold Ecoef. rewrite ev. cbn [Nat.pow]. rewrite Nat.mul_1_l. reflexivity.
  Qed.

  Lemma mle_zero_card : forall (k : nat) (T : list F -> F),
    (exists bq, In bq (cube k) /\ T bq <> zero) ->
    card_le (all_lists lf k) (fun th => mle k T th = zero) (k * length lf ^ (k - 1)).
  Proof.
    intros k T hT. apply (card_le_of_filter (list_eq_dec Fdec)). intros bb hb.
    eapply Nat.le_trans; [| exact (@mle_zero_count F zero one add mul sub div opp inv Fdec Hf lf Hnd k T hT)].
    apply filter_length_imp. intros th hth. apply feqb_true. exact (hb th hth).
  Qed.

  Theorem dec_sound : ~ is_dec_witness -> card_le (list_prod OP2 OmT) AccDec dec_bound.
  Proof.
    intro hnw.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (thdec : forall x y : ThT, {x = y} + {x <> y}) by (unfold ThT; decide equality).
    assert (gdec : forall x y : GT, {x = y} + {x <> y}) by (unfold GT; repeat decide equality).
    assert (p2dec : forall x y : P2, {x = y} + {x <> y}) by (unfold P2; decide equality).
    assert (hM : NoDup (all_lists lf m)) by (apply all_lists_NoDup; exact Hnd).
    assert (hN1 : NoDup (all_lists lf n1)) by (apply all_lists_NoDup; exact Hnd).
    assert (hOTh : NoDup OTh) by (apply NoDup_list_prod; assumption).
    assert (hOmG : NoDup OmG).
    { unfold OmG, ZeroTest.C4Z, ZeroTest.RZZ. repeat apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd. }
    assert (hOmT : NoDup OmT).
    { unfold OmT, ZeroTest.C4Z, ZeroTest.RZZ. repeat apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd. }
    assert (hOP2 : NoDup OP2) by (apply NoDup_list_prod; assumption).
    assert (hm : (1 <= m)%nat) by lia.
    (* 1. a digit out of range? *)
    destruct (Exists_dec (fun T => Exists (fun bq => peval phiR (T bq) <> zero) (cube m)) dts) as [hdig | hdig].
    { intro T. apply Exists_dec. intro bq. destruct (Fdec (peval phiR (T bq)) zero); [right | left]; tauto. }
    { apply Exists_exists in hdig. destruct hdig as (T & hT & hex). apply Exists_exists in hex.
      pose proof (@soundZ F zero one add mul sub div opp inv Fdec Hf m hm phiR base HphiR lf Hnd dts ThT OTh hOTh thdec
                    avsG a0G GGG csG stratG zsG HavsG HcsG HdegG HmsgG
                    (ex_intro _ T (conj hT hex))) as h.
      pose proof (card_le_prod_cyl gdec OP2 OmT _ _ hOmT h) as h'.
      eapply card_le_mono; [ | | exact h'].
      + intros w _ (_ & hg & _). exact hg.
      + unfold dec_bound. lia. }
    (* 2. the key share not ternary? *)
    destruct (Exists_dec (fun bq => ~ tern (stab bq) \/ ~ tern (etab bq)) (cube n1)) as [hter | hter].
    { intro bq.
      assert (td : forall x : F, {tern x} + {~ tern x}).
      { intro x. unfold Bgv.tern. destruct (Fdec x zero); [left; tauto |].
        destruct (Fdec x one); [left; tauto |]. destruct (Fdec x (opp one)); [left; tauto | right; tauto]. }
      destruct (td (stab bq)); [| left; tauto]. destruct (td (etab bq)); [right; tauto | left; tauto]. }
    { apply Exists_exists in hter. destruct hter as (bq & hbq & hnt).
      assert (hex : exists T, In T [stab; etab] /\ exists b0, In b0 (cube n1) /\ peval phi3 (T b0) <> zero).
      { destruct hnt as [h | h].
        + exists stab. split; [cbn; tauto | exists bq; split; [exact hbq | apply phi3_tern; exact h]].
        + exists etab. split; [cbn; tauto | exists bq; split; [exact hbq | apply phi3_tern; exact h]]. }
      pose proof (@soundZ F zero one add mul sub div opp inv Fdec Hf n1 Hn1 phi3 3 ltac:(cbn; lia) lf Hnd
                    [stab; etab] P2 OP2 hOP2 p2dec avsT a0T GGT csT stratT zsT HavsT HcsT HdegT HmsgT hex) as h.
      eapply card_le_mono; [ | | exact h].
      + intros w _ (_ & _ & ht). exact ht.
      + unfold dec_bound. lia. }
    (* 3. then (D) or (K) fails at some coefficient *)
    assert (hrange : forall T, In T dts -> forall bq, In bq (cube m) -> peval phiR (T bq) = zero).
    { intros T hT bq hbq. destruct (Fdec (peval phiR (T bq)) zero) as [e | e]; [exact e | exfalso].
      apply hdig. apply Exists_exists. exists T. split; [exact hT |]. apply Exists_exists. exists bq. tauto. }
    assert (htern : forall bq, In bq (cube n1) -> tern (stab bq) /\ tern (etab bq)).
    { intros bq hbq. split.
      + destruct (Fdec (stab bq) zero) as [e0 | e0]; [left; exact e0 |].
        destruct (Fdec (stab bq) one) as [e1 | e1]; [right; left; exact e1 |].
        destruct (Fdec (stab bq) (opp one)) as [e2 | e2]; [right; right; exact e2 | exfalso].
        apply hter. apply Exists_exists. exists bq. split; [exact hbq | left]. unfold Bgv.tern. tauto.
      + destruct (Fdec (etab bq) zero) as [e0 | e0]; [left; exact e0 |].
        destruct (Fdec (etab bq) one) as [e1 | e1]; [right; left; exact e1 |].
        destruct (Fdec (etab bq) (opp one)) as [e2 | e2]; [right; right; exact e2 | exfalso].
        apply hter. apply Exists_exists. exists bq. split; [exact hbq | right]. unfold Bgv.tern. tauto. }
    (* the event on theta, lifted to the whole space *)
    assert (lift : forall (E : ThT -> Prop) (K : nat), card_le OTh E K ->
              card_le (list_prod OP2 OmT) (fun w => E (fst (fst w))) (K * length OmG * length OmT)).
    { intros E K hE.
      pose proof (card_le_prod_cyl gdec OTh OmG E K hOmG hE) as h1.
      exact (card_le_prod_cyl gdec OP2 OmT (fun p => E (fst p)) _ hOmT h1). }
    destruct (Exists_dec (fun i => Exists (fun x => Dcoef i x <> zero) (seq 0 N)) (seq 0 tau)) as [hDn | hDn].
    { intro i. apply Exists_dec. intro x. destruct (Fdec (Dcoef i x) zero); [right | left]; tauto. }
    { apply Exists_exists in hDn. destruct hDn as (i & hi & hex). apply Exists_exists in hex.
      destruct hex as (x & hx & hne). apply in_seq in hi. apply in_seq in hx.
      assert (hT : exists bq, In bq (cube m) /\ Dtab bq <> zero).
      { exists (pt n1 x ++ pt ell i). split; [apply pt_app_cube |]. rewrite HD by lia. exact hne. }
      pose proof (mle_zero_card m Dtab hT) as hc.
      pose proof (card_le_prod_cyl ldec (all_lists lf m) (all_lists lf n1) _ _ hN1 hc) as hth.
      pose proof (lift _ _ hth) as hfull.
      eapply card_le_mono; [ | | exact hfull].
      + intros w _ ((hd & _) & _). exact hd.
      + unfold dec_bound, bTh. lia. }
    destruct (Exists_dec (fun x => Kcoef x <> zero) (seq 0 N)) as [hKn | hKn].
    { intro x. destruct (Fdec (Kcoef x) zero); [right | left]; tauto. }
    { apply Exists_exists in hKn. destruct hKn as (x & hx & hne). apply in_seq in hx.
      assert (hT : exists bq, In bq (cube n1) /\ Ktab bq <> zero).
      { exists (pt n1 x). split; [apply (@pt_cube F zero one) |]. rewrite HK by lia. exact hne. }
      pose proof (mle_zero_card n1 Ktab hT) as hc.
      pose proof (card_le_prod_fiber ldec (all_lists lf m) (all_lists lf n1)
                    (fun th => mle n1 Ktab (snd th) = zero) _ hM (fun _ _ => hc)) as hth.
      pose proof (lift _ _ hth) as hfull.
      eapply card_le_mono; [ | | exact hfull].
      + intros w _ ((_ & hk) & _). exact hk.
      + unfold dec_bound, bTh. lia. }
    (* 4. otherwise it is a witness *)
    exfalso. apply hnw. split; [exact hrange | split; [exact htern | split]].
    + intros i x hi hx. destruct (Fdec (Dcoef i x) zero) as [e | e]; [exact e | exfalso].
      apply hDn. apply Exists_exists. exists i. split; [apply in_seq; lia |].
      apply Exists_exists. exists x. split; [apply in_seq; lia | exact e].
    + intros x hx. destruct (Fdec (Kcoef x) zero) as [e | e]; [exact e | exfalso].
      apply hKn. apply Exists_exists. exists x. split; [apply in_seq; lia | exact e].
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The protocol with an opening: claimed values instead of ideal checks.

     The verifier has kd + 6 claims on the committed rows. Their claimed
     values are: the public sides VD, VK of the two compressed relations,
     the evaluations zsG and zsT sent by the prover, and the two mask
     values that the final sumcheck claims determine. LD and LK are the
     values of the linear forms of the first two claims on the committed
     rows; HlinD and HlinK say that public side minus linear form is the
     extension of the defect table (proved for the layout of dec_derive
     in DecLayout.v, with nmul_adjoint). *)

  Local Notation sc_run := (@sc_run F zero one add mul Fdec).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation innerZ := (@innerZ F zero add mul).
  Local Notation evalsOf := (@evalsOf F zero one add mul sub).
  Local Notation rhoOf := (@rhoOf F zero).
  Local Notation claimZ := (@claimZ F zero mul).

  Variables VD VK LD LK : ThT -> F.
  Hypothesis HlinD : forall th, In th OTh -> VD th - LD th = mle m Dtab (fst th).
  Hypothesis HlinK : forall th, In th OTh -> VK th - LK th = mle n1 Ktab (snd th).

  Definition WD : Type := (P2 * GT)%type.
  Definition OmD : list WD := list_prod OP2 OmT.
  Definition wTh (w : WD) : ThT := fst (fst w).
  Definition wcG (w : WD) : list F * list F := fst (snd (fst w)).
  Definition wrG (w : WD) : list F := snd (snd (fst w)).
  Definition wcT (w : WD) : list F * list F := fst (snd w).
  Definition wrT (w : WD) : list F := snd (snd w).

  Definition runG (w : WD) : option F :=
    sc_run (stratG (wTh w) (wcG w)) [] (wrG w) (claimZ dts ThT GGG (wTh w) (wcG w)).
  Definition runT (w : WD) : option F :=
    sc_run (stratT (fst w) (wcT w)) [] (wrT w) (claimZ [stab; etab] P2 GGT (fst w) (wcT w)).

  Definition unoptD (o : option F) : F := match o with Some x => x | None => zero end.

  Definition zG (w : WD) : list F := zsG (wTh w) (wcG w) (wrG w).
  Definition zT (w : WD) : list F := zsT (fst w) (wcT w) (wrT w).
  Definition fGv (w : WD) : F := eqp (wrG w) (fst (wcG w)) * innerZ phiR (ksOf dts (wcG w)) (zG w).
  Definition fTv (w : WD) : F := eqp (wrT w) (fst (wcT w)) * innerZ phi3 (ksOf [stab; etab] (wcT w)) (zT w).

  Definition valsD (w : WD) : list F :=
    [VD (wTh w); VK (wTh w)] ++ zG w ++ zT w
    ++ [ (unoptD (runG w) - fGv w) * inv (rhoOf dts (wcG w));
         (unoptD (runT w) - fTv w) * inv (rhoOf [stab; etab] (wcT w)) ].

  Definition tvD (w : WD) : list F :=
    [LD (wTh w); LK (wTh w)] ++ evalsOf m dts (avsG (wTh w)) (wrG w)
    ++ evalsOf n1 [stab; etab] (avsT (fst w)) (wrT w)
    ++ [ gmask (a0G (wTh w)) (csG (wTh w)) (wrG w); gmask (a0T (fst w)) (csT (fst w)) (wrT w) ].

  (* the format checks on the claimed evaluations *)
  Definition LenD (w : WD) : Prop := length (zG w) = length dts /\ length (zT w) = 2%nat.

  (* the checks of the verifier before the opening *)
  Definition PreAccD (w : WD) : Prop :=
    LenD w /\ runG w <> None /\ runT w <> None /\
    rhoOf dts (wcG w) <> zero /\ rhoOf [stab; etab] (wcT w) <> zero.

  Lemma evalsOf_length : forall k (Ts : list (list F -> F)) avs r, length avs = length Ts ->
    length (evalsOf k Ts avs r) = length Ts.
  Proof.
    intros k; induction Ts as [| T Ts ih]; intros avs r hl; destruct avs as [| a0 avs]; cbn in hl; try lia;
      [reflexivity |]. cbn. rewrite ih by lia. reflexivity.
  Qed.

  Lemma app_inj_len : forall (l1 l2 r1 r2 : list F), length l1 = length l2 ->
    l1 ++ r1 = l2 ++ r2 -> l1 = l2 /\ r1 = r2.
  Proof.
    induction l1 as [| x l1 ih]; intros l2 r1 r2 hl e; destruct l2 as [| y l2]; cbn in hl; try lia.
    + split; [reflexivity | exact e].
    + cbn in e. injection e as -> e. destruct (ih l2 r1 r2 ltac:(lia) e) as [-> ->]. split; reflexivity.
  Qed.

  Lemma linkD : forall w, In (wTh w) OTh -> PreAccD w -> valsD w = tvD w -> AccDec w.
  Proof.
    intros w hth ((hlG & hlT) & hG & hT & hrG & hrT) hv.
    unfold valsD, tvD in hv. cbn [app] in hv. injection hv as eD eK hv.
    assert (h1 : length (zG w) = length (evalsOf m dts (avsG (wTh w)) (wrG w)))
      by (rewrite hlG, (evalsOf_length m dts _ _ (HavsG _)); reflexivity).
    destruct (app_inj_len _ _ _ _ h1 hv) as [ezG hv'].
    assert (h2 : length (zT w) = length (evalsOf n1 [stab; etab] (avsT (fst w)) (wrT w)))
      by (rewrite hlT, (evalsOf_length n1 [stab; etab] _ _ (HavsT _)); reflexivity).
    destruct (app_inj_len _ _ _ _ h2 hv') as [ezT hv''].
    injection hv'' as eG eT.
    destruct (runG w) as [clG |] eqn:erG; [| contradiction].
    destruct (runT w) as [clT |] eqn:erT; [| contradiction].
    cbn [unoptD] in eG, eT.
    split; [| split].
    + split.
      - change (mle m Dtab (fst (wTh w)) = zero). rewrite <-(HlinD _ hth), eD. field.
      - change (mle n1 Ktab (snd (wTh w)) = zero). rewrite <-(HlinK _ hth), eK. field.
    + exists clG. split; [exact erG |]. split; [exact ezG |].
      fold (wTh w) (wcG w) (wrG w). rewrite <-eG. fold (zG w).
      transitivity (fGv w + rhoOf dts (wcG w) * ((clG - fGv w) * inv (rhoOf dts (wcG w)))); [field; exact hrG | reflexivity].
    + exists clT. split; [exact erT |]. split; [exact ezT |].
      fold (wcT w) (wrT w). rewrite <-eT. fold (zT w).
      transitivity (fTv w + rhoOf [stab; etab] (wcT w) * ((clT - fTv w) * inv (rhoOf [stab; etab] (wcT w))));
        [field; exact hrT | reflexivity].
  Qed.

  (* An opening protocol, abstractly (as in MixSound.v). The bound is
     needed only for tuples at which the claimed evaluations have the
     right number of entries. *)
  Variable O : Type.
  Variable Oo : list O.
  Hypothesis HOo : NoDup Oo.
  Hypothesis decO : forall x y : O, {x = y} + {x <> y}.
  Variable AccOw : WD -> O -> Prop.
  Variable Bo : nat.
  Hypothesis Hopen : forall w, In w OmD -> LenD w -> valsD w <> tvD w -> card_le Oo (AccOw w) Bo.

  Definition RealAccD (x : WD * O) : Prop := PreAccD (fst x) /\ AccOw (fst x) (snd x).

  Theorem dec_full : ~ is_dec_witness ->
    card_le (list_prod OmD Oo) RealAccD (dec_bound * length Oo + Bo * length OmD).
  Proof.
    intro hnw.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (wdec : forall x y : WD, {x = y} + {x <> y}) by (unfold WD, P2, GT, ThT; repeat decide equality).
    assert (hOmD : NoDup OmD).
    { unfold OmD, OP2, OTh, OmG, OmT, ZeroTest.C4Z, ZeroTest.RZZ.
      repeat apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd. }
    apply (card_join wdec decO OmD Oo AccDec (fun w => valsD w = tvD w) (fun w o => PreAccD w /\ AccOw w o)
             dec_bound Bo hOmD HOo).
    + intro w. destruct (ldec (valsD w) (tvD w)); [left | right]; assumption.
    + exact (dec_sound hnw).
    + intros w o hw hd [hp _]. apply (linkD w); [| exact hp | exact hd].
      destruct w as [[th g] gt]. unfold OmD, OP2 in hw. apply in_prod_iff in hw. destruct hw as [hw _].
      apply in_prod_iff in hw. destruct hw as [hw _]. exact hw.
    + intros w hw hd.
      destruct (Nat.eq_dec (length (zG w)) (length dts)) as [e1 | e1];
        [destruct (Nat.eq_dec (length (zT w)) 2%nat) as [e2 | e2] |].
      - eapply card_le_mono; [ | apply le_n | exact (Hopen w hw (conj e1 e2) hd)].
        intros o _ [_ h]. exact h.
      - apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros o _ [((_ & h) & _) _]. exact (e2 h).
      - apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros o _ [((h & _) & _) _]. exact (e1 h).
  Qed.

End DecSound.
