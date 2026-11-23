(* Knowledge soundness of the shuffle proof, sumcheck layer (paper,
   Theorem 5.2 without the opening).

   The protocol is that of Figure 1 with an ideal opening: the nine
   linear claims are checked against the committed tables themselves. The
   prover is adaptive: everything it sends is a function of the challenges
   it has seen.

     first message      W1, W2, W3 (witness tables), sg (the table sigma)
     challenge c1       alpha :: rho_u ++ rho_v ++ [beta]
     second message     u, uh, the mask coefficients a_T, the three
                        sumcheck masks and their sums G_A, G_B, G_C
     challenge c2       (tc, [k1; k2; k3; rhoA]);  sumcheck A, end point rA
     message            U, Uhat, s, H
     challenge rhoB;    sumcheck B, end point ry
     challenge c4       (tz, [kc1; kc2; kc3; rhoC]);  sumcheck C, end point rz
     message            wz1, wz2, wz3

   The verifier's own tables (rho' as rp1..3, the projections zp, zh) and
   alpha, beta are functions of c1 that satisfy Hver: c1 is the point
   (rho, alpha, beta) and the tables have the right values on the cube.

   Theorem mix_sound. Let the witness read off the first message be
   rrW (re-randomised inputs) and sg. If it is not a witness, that is, not
   (a shuffle of the inputs and ternary), then the challenge tuples for
   which the verifier accepts number at most mix_bound, which is

     [ (2 tau - 1) + (ell + 1) + (3 ell + 2) + 1 + 2 log N
       + (m + 1) + (4 m + 3) ] / |F|

   of all tuples, written without division: the first seven lines of the
   error budget of Theorem 5.2. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Bgv CubeIndex MaskedExt MixMultiset Sumcheck SumcheckMask MixSummands MixIdentities SumcheckSound MixSoundA MixSoundB MixSoundC MixBridge.
Import ListNotations.

Section MixSound.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Local Notation nF := (@nF F zero one add).
  Local Notation cube := (@cube F zero one).
  Local Notation pt := (@pt F zero one).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation tern := (@tern F zero one opp).
  Local Notation proj := (@proj F zero add mul).
  Local Notation rho_r := (@rho_r F add mul opp).
  Local Notation rho_e1 := (@rho_e1 F mul).
  Local Notation rho_e2 := (@rho_e2 F mul).
  Local Notation point := (@point F).
  Local Notation htab := (@htab F zero one add mul sub).
  Local Notation is_shuffle := (@is_shuffle F zero one add).
  Local Notation rrW := (@rrW F zero one add mul opp).
  Local Notation sgf := (@sgf F zero one).
  Local Notation AccA := (@AccA F zero one add mul sub Fdec).
  Local Notation Good := (@Good F zero one add mul sub).
  Local Notation AccB := (@AccB F zero one add mul sub inv Fdec).
  Local Notation hstarB := (@hstarB F zero one add mul sub).
  Local Notation AccC := (@AccC F zero one add mul sub Fdec).
  Local Notation ctx := (@ctx F).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Variables (a b : list F) (pp : F).
  Variables n1 ell : nat.
  Hypothesis Hell : (1 <= ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.

  Hypothesis Hchar : forall k, (0 < k <= tau)%nat -> nF k <> zero.
  Hypothesis HN : nF N <> zero.

  (* statement and first message *)
  Variables cin cout : nat -> ctx.
  Variables W1 W2 W3 sg : list F -> F.
  Local Notation rr := (rrW a b pp n1 ell cin W1 W2 W3).

  Hypothesis Hrr : forall i, (i < tau)%nat -> length (fst (rr i)) = N /\ length (snd (rr i)) = N.
  Hypothesis Hco : forall j, (j < tau)%nat -> length (fst (cout j)) = N /\ length (snd (cout j)) = N.

  (* challenge spaces *)
  Local Notation C1 := (@C1 F lf N).
  Local Notation C2 := (@C2 F lf ell).
  Local Notation RA := (@RA F lf ell).
  Local Notation RY := (all_lists lf n1).
  Local Notation C4 := (@C4 F lf m).
  Local Notation RZ := (@RZ F lf m).

  Definition P3 : Type := (list F * ((list F * list F) * list F))%type.
  Definition P5 : Type := (P3 * (F * list F))%type.
  Definition OP3 : list P3 := list_prod C1 (list_prod C2 RA).
  Definition OP5 : list P5 := list_prod OP3 (list_prod lf RY).

  (* the verifier's tables *)
  Variables rp1T rp2T rp3T zpT zhT : list F -> list F -> F.
  Variables alT beT : list F -> F.

  Hypothesis Hver : forall c1, In c1 C1 ->
    exists ru rv, length ru = N /\ length rv = N /\
      c1 = point ru rv (alT c1) (beT c1) /\
      (forall y, (y < N)%nat -> rp1T c1 (pt n1 y) = nth y (rho_r a b ru rv) zero) /\
      (forall y, (y < N)%nat -> rp2T c1 (pt n1 y) = nth y (rho_e1 pp ru) zero) /\
      (forall y, (y < N)%nat -> rp3T c1 (pt n1 y) = nth y (rho_e2 pp rv) zero) /\
      (forall i, (i < tau)%nat -> zpT c1 (pt ell i) = proj ru rv (cin i)) /\
      (forall j, (j < tau)%nat -> zhT c1 (pt ell j) = proj ru rv (cout j)).

  Definition htabT (c1 : list F) : list F -> F :=
    htab n1 (rp1T c1) (rp2T c1) (rp3T c1) W1 W2 W3 (zpT c1) (alT c1) (beT c1).

  (* the prover *)
  Variables u uh : list F -> list F -> F.
  Variables au auh asg ah aw1 aw2 aw3 a0A a0B a0C GA GB GC : list F -> F.
  Variables csA csB csC : list F -> list (list F).
  Variable stratA : list F -> list F * list F -> list F -> list F.
  Variables eU eUh eS eH : list F -> list F * list F -> list F -> F.
  Variable stratB : P3 -> F -> list F -> list F.
  Variable stratC : P5 -> list F * list F -> list F -> list F.
  Variables wz1 wz2 wz3 : P5 -> list F * list F -> list F -> F.

  (* what the verifier enforces on the shape of the messages *)
  Hypothesis HcsA : forall c1, length (csA c1) = ell.
  Hypothesis HdegA : forall c1 i, (i < ell)%nat -> (length (nth i (csA c1) []) <= degA ell i)%nat.
  Hypothesis HmsgA : forall c1 c2 pre, (length (stratA c1 c2 pre) <= S (degA ell (length pre)))%nat.
  Hypothesis HcsB : forall c1, length (csB c1) = n1.
  Hypothesis HdegB : forall c1 i, (i < n1)%nat -> (length (nth i (csB c1) []) <= 2)%nat.
  Hypothesis HmsgB : forall p rB pre, (length (stratB p rB pre) <= S (degB (length pre)))%nat.
  Hypothesis HcsC : forall c1, length (csC c1) = m.
  Hypothesis HdegC : forall c1 i, (i < m)%nat -> (length (nth i (csC c1) []) <= degC m i)%nat.
  Hypothesis HmsgC : forall p c4 pre, (length (stratC p c4 pre) <= S (degC m (length pre)))%nat.

  Definition accA (p : P3) : Prop :=
    AccA ell sg zhT alT beT u uh au auh asg a0A GA csA stratA eU eUh eS eH (fst p) (fst (snd p)) (snd (snd p)).

  Definition goodA (p : P3) : Prop :=
    Good ell htabT ah eH (fst p) (fst (snd p)) (snd (snd p)).

  Definition accB (p : P3) (rB : F) (ry : list F) : Prop :=
    AccB n1 ell W1 W2 W3 P3
      (fun p => rp1T (fst p)) (fun p => rp2T (fst p)) (fun p => rp3T (fst p)) (fun p => zpT (fst p))
      (fun p => alT (fst p)) (fun p => beT (fst p)) (fun p => ah (fst p)) (fun p => a0B (fst p))
      (fun p => GB (fst p)) (fun p => eH (fst p) (fst (snd p)) (snd (snd p))) (fun p => csB (fst p))
      (fun p => snd (snd p)) stratB p rB ry.

  Definition accC (p : P5) (c4 : list F * list F) (rz : list F) : Prop :=
    AccC m W1 W2 W3 P5
      (fun p => aw1 (fst (fst p))) (fun p => aw2 (fst (fst p))) (fun p => aw3 (fst (fst p)))
      (fun p => a0C (fst (fst p))) (fun p => GC (fst (fst p))) (fun p => csC (fst (fst p)))
      stratC wz1 wz2 wz3 p c4 rz.

  (* The verifier accepts. *)
  Definition Acc (w : P5 * ((list F * list F) * list F)) : Prop :=
    accA (fst (fst w)) /\
    accB (fst (fst w)) (fst (snd (fst w))) (snd (snd (fst w))) /\
    accC (fst w) (fst (snd w)) (snd (snd w)).

  (* The first message is a witness. *)
  Definition is_witness : Prop :=
    is_shuffle tau rr cout (sgf ell sg) /\
    (forall bq, In bq (cube m) -> tern (W1 bq) /\ tern (W2 bq) /\ tern (W3 bq)).

  Definition mix_bound : nat :=
    ((@boundA F lf N ell * length (list_prod lf RY) + @boundB F lf n1 * length OP3) * length (list_prod C4 RZ)
     + @boundC F lf m * length OP5)%nat.

  Lemma tern_dec : forall x : F, {tern x} + {~ tern x}.
  Proof.
    intro x. unfold Bgv.tern.
    destruct (Fdec x zero); [left; tauto |].
    destruct (Fdec x one); [left; tauto |].
    destruct (Fdec x (opp one)); [left; tauto | right; tauto].
  Qed.

  Theorem mix_sound : ~ is_witness ->
    card_le (list_prod OP5 (list_prod C4 RZ)) Acc mix_bound.
  Proof.
    intro hnw.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (pdec : forall x y : list F * list F, {x = y} + {x <> y}) by (decide equality).
    assert (p3dec : forall x y : P3, {x = y} + {x <> y}) by (unfold P3; repeat decide equality).
    assert (rydec : forall x y : F * list F, {x = y} + {x <> y}) by (decide equality).
    assert (p5dec : forall x y : P5, {x = y} + {x <> y}) by (unfold P5; decide equality).
    assert (czdec : forall x y : (list F * list F) * list F, {x = y} + {x <> y}) by (decide equality).
    assert (hC1 : NoDup C1) by (apply all_lists_NoDup; exact Hnd).
    assert (hC2 : NoDup C2) by (apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd).
    assert (hRA : NoDup RA) by (apply all_lists_NoDup; exact Hnd).
    assert (hRY : NoDup RY) by (apply all_lists_NoDup; exact Hnd).
    assert (hOP3 : NoDup OP3) by (apply NoDup_list_prod; [exact hC1 | apply NoDup_list_prod; assumption]).
    assert (hBY : NoDup (list_prod lf RY)) by (apply NoDup_list_prod; assumption).
    assert (hOP5 : NoDup OP5) by (apply NoDup_list_prod; assumption).
    assert (hCZ : NoDup (list_prod C4 RZ)).
    { apply NoDup_list_prod; [apply NoDup_list_prod |]; apply all_lists_NoDup; exact Hnd. }
    assert (hm : (1 <= m)%nat) by lia.
    (* is every entry of the witness tables ternary? *)
    destruct (Exists_dec (fun bq => ~ tern (W1 bq) \/ ~ tern (W2 bq) \/ ~ tern (W3 bq)) (cube m)) as [hex | hall].
    { intro bq. destruct (tern_dec (W1 bq)); [| left; tauto].
      destruct (tern_dec (W2 bq)); [| left; tauto].
      destruct (tern_dec (W3 bq)); [right; tauto | left; tauto]. }
    + (* no: the shortness part rejects *)
      apply Exists_exists in hex.
      pose proof (@soundC F zero one add mul sub div opp inv Fdec Hf lf Hnd m hm W1 W2 W3 P5 OP5 hOP5 p5dec
                    (fun p => aw1 (fst (fst p))) (fun p => aw2 (fst (fst p))) (fun p => aw3 (fst (fst p)))
                    (fun p => a0C (fst (fst p))) (fun p => GC (fst (fst p))) (fun p => csC (fst (fst p)))
                    stratC wz1 wz2 wz3
                    (fun p => HcsC (fst (fst p))) (fun p => HdegC (fst (fst p))) HmsgC hex) as h.
      eapply card_le_mono; [ | | exact h].
      - intros w _ (_ & _ & hc). exact hc.
      - unfold mix_bound. lia.
    + (* yes: then it is not a shuffle *)
      assert (hns : ~ is_shuffle tau rr cout (sgf ell sg)).
      { intro hs. apply hnw. split; [exact hs |]. intros bq hbq.
        destruct (tern_dec (W1 bq)) as [t1 | t1]; [| exfalso; apply hall; apply Exists_exists; exists bq; tauto].
        destruct (tern_dec (W2 bq)) as [t2 | t2]; [| exfalso; apply hall; apply Exists_exists; exists bq; tauto].
        destruct (tern_dec (W3 bq)) as [t3 | t3]; [| exfalso; apply hall; apply Exists_exists; exists bq; tauto].
        tauto. }
      (* the two table hypotheses of soundA, from the bridge *)
      assert (hh : forall c1, In c1 C1 -> forall i, (i < tau)%nat ->
                htabT c1 (pt ell i) = @dot F zero add mul (@form F one opp (rr i) (nF i)) c1).
      { intros c1 hc1 i hi. destruct (Hver c1 hc1) as (ru & rv & hru & hrv & hpt & h1 & h2 & h3 & h4 & _).
        pose proof (@bridge_h F zero one add mul sub div opp inv Hf a b pp n1 ell cin W1 W2 W3 Hrr
                      ru rv (alT c1) (beT c1) hru hrv (rp1T c1) (rp2T c1) (rp3T c1) (zpT c1) h1 h2 h3 h4 i hi) as e.
        rewrite <-hpt in e. exact e. }
      assert (hhh : forall c1, In c1 C1 -> forall j, (j < tau)%nat ->
                @hhtab F add mul sub sg (zhT c1) (alT c1) (beT c1) (pt ell j)
                = @dot F zero add mul (@form F one opp (cout j) (sgf ell sg j)) c1).
      { intros c1 hc1 j hj. destruct (Hver c1 hc1) as (ru & rv & hru & hrv & hpt & _ & _ & _ & _ & h5).
        pose proof (@bridge_hh F zero one add mul sub div opp inv Hf n1 ell cout sg Hco
                      ru rv (alT c1) (beT c1) hru hrv (zhT c1) h5 j hj) as e.
        rewrite <-hpt in e. exact e. }
      pose proof (@soundA F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall N ell Hell rr cout sg
                    Hchar Hrr Hco htabT zhT alT beT hh hhh u uh au auh asg ah a0A GA csA stratA eU eUh eS eH
                    HcsA HdegA HmsgA hns) as hA.
      fold OP3 in hA.
      pose proof (card_le_prod_cyl rydec OP3 (list_prod lf RY) (fun p => accA p /\ goodA p) _ hBY hA) as hA'.
      pose proof (@soundB F zero one add mul sub div opp inv Fdec Hf lf Hnd n1 ell HN W1 W2 W3 P3 OP3 hOP3 p3dec
                    (fun p => rp1T (fst p)) (fun p => rp2T (fst p)) (fun p => rp3T (fst p)) (fun p => zpT (fst p))
                    (fun p => alT (fst p)) (fun p => beT (fst p)) (fun p => ah (fst p)) (fun p => a0B (fst p))
                    (fun p => GB (fst p)) (fun p => eH (fst p) (fst (snd p)) (snd (snd p))) (fun p => csB (fst p))
                    (fun p => snd (snd p)) stratB) as hB.
      assert (hr : forall p : P3, In p OP3 -> length (snd (snd p)) = ell).
      { intros [c1 [c2 rA]] hp. unfold OP3 in hp. apply in_prod_iff in hp. destruct hp as [_ hp].
        apply in_prod_iff in hp. destruct hp as [_ hp]. apply all_lists_In in hp. cbn. tauto. }
      specialize (hB hr (fun p => HcsB (fst p)) (fun p => HdegB (fst p)) HmsgB).
      pose proof (card_le_or _ _ _ _ _ hA' hB) as hAB.
      assert (hAB' : card_le OP5 (fun w => accA (fst w) /\ accB (fst w) (fst (snd w)) (snd (snd w)))
                       (@boundA F lf N ell * length (list_prod lf RY) + @boundB F lf n1 * length OP3)).
      { eapply card_le_mono; [ | apply le_n | exact hAB].
        intros [p [rB ry]] _ [ha hb]. cbn [fst snd] in *.
        destruct (Fdec (eH (fst p) (fst (snd p)) (snd (snd p)))
                       (mstar ell (htabT (fst p)) (ah (fst p)) (snd (snd p)))) as [e | e].
        + left. split; [exact ha | exact e].
        + right. split; [exact e | exact hb]. }
      pose proof (card_le_prod_cyl czdec OP5 (list_prod C4 RZ) _ _ hCZ hAB') as hfull.
      eapply card_le_mono; [ | | exact hfull].
      - intros w _ (ha & hb & _). split; assumption.
      - unfold mix_bound. lia.
  Qed.

  (* The bound as a fraction of all challenge tuples: mix_bound / |Omega| = K / |F|. *)
  Definition mix_K : nat :=
    ((2 * tau - 1) + (ell + 1) + dsum (degA ell) 0 ell + 1 + dsum degB 0 n1 + (m + 1) + dsum (degC m) 0 m)%nat.

  Theorem mix_bound_fraction :
    (mix_bound * length lf = mix_K * length (list_prod OP5 (list_prod C4 RZ)))%nat.
  Proof.
    unfold mix_bound, mix_K, OP5, OP3, MixSoundA.boundA, MixSoundA.b1, MixSoundB.boundB, MixSoundC.boundC,
      MixSoundA.C1, MixSoundA.C2, MixSoundA.RA, MixSoundC.C4, MixSoundC.RZ.
    cbv delta [P3 P5].
    repeat (rewrite length_prod || rewrite all_lists_length).
    set (q := length lf).
    set (dA := dsum (degA ell) 0 ell). set (dB := dsum degB 0 n1). set (dC := dsum (degC m) 0 m).
    assert (hE : (q ^ ell = q * q ^ (ell - 1))%nat).
    { replace ell with (S (ell - 1)) at 1 by lia. reflexivity. }
    assert (hM : (q ^ m = q * q ^ (m - 1))%nat).
    { replace m with (S (m - 1)) at 1 by lia. reflexivity. }
    assert (hE4 : (q ^ (ell + (2 + 2) - 1) = q ^ (ell - 1) * q ^ 4)%nat).
    { replace (ell + (2 + 2) - 1)%nat with ((ell - 1) + 4)%nat by lia. apply Nat.pow_add_r. }
    assert (hM4 : (q ^ (m + (3 + 1) - 1) = q ^ (m - 1) * q ^ 4)%nat).
    { replace (m + (3 + 1) - 1)%nat with ((m - 1) + 4)%nat by lia. apply Nat.pow_add_r. }
    assert (hB : (dB * q ^ (n1 - 1) * q = dB * q ^ n1)%nat).
    { destruct n1 as [| n']; [unfold dB; cbn; lia |].
      replace (S n' - 1)%nat with n' by lia. cbn [Nat.pow]. lia. }
    rewrite hE4, hM4.
    cbn [Nat.pow] in *.
    set (P1 := (q ^ (N + N + 1))%nat) in *.
    set (Em := (q ^ (ell - 1))%nat) in *. set (Mm := (q ^ (m - 1))%nat) in *.
    set (Y := (q ^ n1)%nat) in *. set (Ym := (q ^ (n1 - 1))%nat) in *.
    rewrite hE, hM.
    set (T := (2 * tau - 1)%nat).
    set (Q4 := (q * (q * (q * (q * 1))))%nat).
    set (A3 := (q * P1 * (q * Em * Q4 * (q * Em)))%nat).
    set (BY := (q * Y)%nat).
    set (CZ := (q * Mm * Q4 * (q * Mm))%nat).
    set (XA := (T * P1 * (q * Em * Q4 * (q * Em))
                + ((ell + 1) * (Em * Q4) * (q * Em) + dA * Em * (q * Em * Q4)) * (q * P1))%nat).
    set (XB := (1 * Y + dB * Ym * q)%nat).
    set (XC := ((m + 1) * (Mm * Q4) * (q * Mm) + dC * Mm * (q * Mm * Q4))%nat).
    assert (hXA : (XA * q = (T + (ell + 1) + dA) * A3)%nat) by (unfold XA, A3; ring).
    assert (hXB : (XB * q = (1 + dB) * BY)%nat).
    { unfold XB, BY. rewrite Nat.mul_add_distr_r, hB. ring. }
    assert (hXC : (XC * q = ((m + 1) + dC) * CZ)%nat) by (unfold XC, CZ; ring).
    transitivity ((XA * q) * BY * CZ + (XB * q) * A3 * CZ + (XC * q) * (A3 * BY))%nat; [ring |].
    rewrite hXA, hXB, hXC. ring.
  Qed.

  Lemma dsum_degB : forall i k, dsum degB i k = (2 * k)%nat.
  Proof. intros i k; revert i; induction k as [| k ih]; intro i; cbn [dsum]; [lia | rewrite ih; unfold degB; lia]. Qed.

  Lemma dsum_degA : forall L k i, (i + S k = L)%nat -> dsum (degA L) i (S k) = (3 * S k + 2)%nat.
  Proof.
    intros L; induction k as [| k ih]; intros i h.
    + cbn [dsum]. unfold degA. replace (S i) with L by lia. rewrite Nat.eqb_refl. lia.
    + change (dsum (degA L) i (S (S k))) with (degA L i + dsum (degA L) (S i) (S k))%nat.
      rewrite (ih (S i)) by lia. unfold degA. rewrite (proj2 (Nat.eqb_neq _ _)) by lia. lia.
  Qed.

  Lemma dsum_degC : forall L k i, (i + S k = L)%nat -> dsum (degC L) i (S k) = (4 * S k + 3)%nat.
  Proof.
    intros L; induction k as [| k ih]; intros i h.
    + cbn [dsum]. unfold degC. replace (S i) with L by lia. rewrite Nat.eqb_refl. lia.
    + change (dsum (degC L) i (S (S k))) with (degC L i + dsum (degC L) (S i) (S k))%nat.
      rewrite (ih (S i)) by lia. unfold degC. rewrite (proj2 (Nat.eqb_neq _ _)) by lia. lia.
  Qed.

  (* The numerator: the paper's 2 tau + 9 ell + 7 log N + 9 minus the two
     opening lines for kappa and c. *)
  Theorem mix_K_value : mix_K = (2 * tau + 4 * ell + 2 * n1 + 5 * m + 7)%nat.
  Proof.
    unfold mix_K. rewrite dsum_degB.
    replace (dsum (degA ell) 0 ell) with (dsum (degA ell) 0 (S (ell - 1))) by (f_equal; lia).
    rewrite (dsum_degA ell (ell - 1) 0 ltac:(lia)).
    replace (dsum (degC m) 0 m) with (dsum (degC m) 0 (S (m - 1))) by (f_equal; lia).
    rewrite (dsum_degC m (m - 1) 0 ltac:(lia)).
    assert (hp : (1 <= 2 ^ ell)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The protocol with an opening: claimed values instead of ideal checks *)

  Add Field fieldMS : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation kk := (@kk F zero).
  Local Notation sc_run := (@sc_run F zero one add mul Fdec).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation cube3 := (@cube3 F mul sub).
  Local Notation idr := (@idr F zero one add mul).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation gB := (@gB F zero one add mul sub).

  (* a full tuple of sumcheck-layer challenges, and its components *)
  Definition Wm : Type := (P5 * ((list F * list F) * list F))%type.
  Definition Om : list Wm := list_prod OP5 (list_prod C4 RZ).
  Definition w1 (w : Wm) : list F := fst (fst (fst w)).
  Definition w2 (w : Wm) : list F * list F := fst (snd (fst (fst w))).
  Definition wA (w : Wm) : list F := snd (snd (fst (fst w))).
  Definition wB (w : Wm) : F := fst (snd (fst w)).
  Definition wY (w : Wm) : list F := snd (snd (fst w)).
  Definition w4 (w : Wm) : list F * list F := fst (snd w).
  Definition wZ (w : Wm) : list F := snd (snd w).

  (* the three sumcheck runs: final claims, if the round checks pass *)
  Definition runA (w : Wm) : option F :=
    sc_run (stratA (w1 w) (w2 w)) [] (wA w)
           (kk (snd (w2 w)) 0 + kk (snd (w2 w)) 1 + kk (snd (w2 w)) 3 * GA (w1 w)).
  Definition runB (w : Wm) : option F :=
    sc_run (stratB (fst (fst w)) (wB w)) [] (wY w)
           (eH (w1 w) (w2 w) (wA w) - mle ell (zpT (w1 w)) (wA w) - beT (w1 w) * idr (wA w) + alT (w1 w)
            + wB w * GB (w1 w)).
  Definition runC (w : Wm) : option F :=
    sc_run (stratC (fst w) (w4 w)) [] (wZ w) (kk (snd (w4 w)) 3 * GC (w1 w)).

  Definition unopt (o : option F) : F := match o with Some x => x | None => zero end.

  Definition fAv (w : Wm) : F :=
    eqp (wA w) (fst (w2 w))
      * (kk (snd (w2 w)) 0 * (eU (w1 w) (w2 w) (wA w) * eH (w1 w) (w2 w) (wA w))
         + kk (snd (w2 w)) 1 * (eUh (w1 w) (w2 w) (wA w)
                                * (mle ell (zhT (w1 w)) (wA w) + beT (w1 w) * eS (w1 w) (w2 w) (wA w) - alT (w1 w))))
    + kk (snd (w2 w)) 2 * (eU (w1 w) (w2 w) (wA w) - eUh (w1 w) (w2 w) (wA w)).

  Definition fCv (w : Wm) : F :=
    eqp (wZ w) (fst (w4 w))
      * (kk (snd (w4 w)) 0 * cube3 (wz1 (fst w) (w4 w) (wZ w)) + kk (snd (w4 w)) 1 * cube3 (wz2 (fst w) (w4 w) (wZ w))
         + kk (snd (w4 w)) 2 * cube3 (wz3 (fst w) (w4 w) (wZ w))).

  (* The nine claimed values of Figure 1, step 7. *)
  Definition vals9 (w : Wm) : list F :=
    [ eU (w1 w) (w2 w) (wA w); eUh (w1 w) (w2 w) (wA w); eS (w1 w) (w2 w) (wA w);
      unopt (runB w);
      wz1 (fst w) (w4 w) (wZ w); wz2 (fst w) (w4 w) (wZ w); wz3 (fst w) (w4 w) (wZ w);
      (unopt (runA w) - fAv w) * inv (kk (snd (w2 w)) 3);
      (unopt (runC w) - fCv w) * inv (kk (snd (w4 w)) 3) ].

  (* What these nine values are for the committed tables. *)
  Definition tvI (w : Wm) : list F :=
    [ mstar ell (u (w1 w)) (au (w1 w)) (wA w); mstar ell (uh (w1 w)) (auh (w1 w)) (wA w);
      mstar ell sg (asg (w1 w)) (wA w);
      gB n1 ell (rp1T (w1 w)) (rp2T (w1 w)) (rp3T (w1 w)) W1 W2 W3 (wA w)
         (ah (w1 w) * Zp (wA w) * inv (nF N)) (wB w) (a0B (w1 w)) (csB (w1 w)) (wY w);
      mstar m W1 (aw1 (w1 w)) (wZ w); mstar m W2 (aw2 (w1 w)) (wZ w); mstar m W3 (aw3 (w1 w)) (wZ w);
      gmask (a0A (w1 w)) (csA (w1 w)) (wA w);
      gmask (a0C (w1 w)) (csC (w1 w)) (wZ w) ].

  (* the checks of the verifier before the opening *)
  Definition PreAcc (w : Wm) : Prop :=
    runA w <> None /\ runB w <> None /\ runC w <> None /\
    kk (snd (w2 w)) 3 <> zero /\ kk (snd (w4 w)) 3 <> zero.

  Lemma link : forall w, PreAcc w -> vals9 w = tvI w -> Acc w.
  Proof.
    intros w (hA & hB & hC & hrA & hrC) hv.
    pose proof (f_equal (fun l => nth 0 l zero) hv) as e0.
    pose proof (f_equal (fun l => nth 1 l zero) hv) as e1.
    pose proof (f_equal (fun l => nth 2 l zero) hv) as e2.
    pose proof (f_equal (fun l => nth 3 l zero) hv) as e3.
    pose proof (f_equal (fun l => nth 4 l zero) hv) as e4.
    pose proof (f_equal (fun l => nth 5 l zero) hv) as e5.
    pose proof (f_equal (fun l => nth 6 l zero) hv) as e6.
    pose proof (f_equal (fun l => nth 7 l zero) hv) as e7.
    pose proof (f_equal (fun l => nth 8 l zero) hv) as e8.
    cbn [nth vals9 tvI] in e0, e1, e2, e3, e4, e5, e6, e7, e8.
    destruct (runA w) as [clA |] eqn:eA; [| contradiction].
    destruct (runB w) as [clB |] eqn:eB; [| contradiction].
    destruct (runC w) as [clC |] eqn:eC; [| contradiction].
    cbn [unopt] in e3, e7, e8.
    split; [| split].
    + exists clA. split; [exact eA |]. split; [exact e0 |]. split; [exact e1 |]. split; [exact e2 |].
      fold (w1 w) (w2 w) (wA w). rewrite <-e7.
      transitivity (fAv w + kk (snd (w2 w)) 3 * ((clA - fAv w) * inv (kk (snd (w2 w)) 3))); [field; exact hrA | reflexivity].
    + unfold accB, MixSoundB.AccB. transitivity (Some clB); [exact eB | f_equal; exact e3].
    + exists clC. split; [exact eC |]. split; [exact e4 |]. split; [exact e5 |]. split; [exact e6 |].
      fold (w1 w) (w4 w) (wZ w). rewrite <-e8.
      transitivity (fCv w + kk (snd (w4 w)) 3 * ((clC - fCv w) * inv (kk (snd (w4 w)) 3))); [field; exact hrC | reflexivity].
  Qed.

  (* An opening protocol, abstractly: any acceptance predicate AccOw over a
     finite challenge space Oo which, for every tuple w at which the
     claimed values are wrong, holds for at most Bo challenges. For the
     opening of the paper this is open_sound in OpenSound.v, with the
     layout of the nine claims on the committed rows. *)
  Variable O : Type.
  Variable Oo : list O.
  Hypothesis HOo : NoDup Oo.
  Hypothesis decO : forall x y : O, {x = y} + {x <> y}.
  Variable AccOw : Wm -> O -> Prop.
  Variable Bo : nat.
  Hypothesis Hopen : forall w, In w Om -> vals9 w <> tvI w -> card_le Oo (AccOw w) Bo.

  (* The verifier of the whole protocol accepts. *)
  Definition RealAcc (x : Wm * O) : Prop := PreAcc (fst x) /\ AccOw (fst x) (snd x).

  Theorem mix_full : ~ is_witness ->
    card_le (list_prod Om Oo) RealAcc (mix_bound * length Oo + Bo * length Om).
  Proof.
    intro hnw.
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (wdec : forall x y : Wm, {x = y} + {x <> y}) by (unfold Wm, P5, P3; repeat decide equality).
    assert (hOm : NoDup Om).
    { unfold Om, OP5, OP3. repeat apply NoDup_list_prod; try (apply all_lists_NoDup; exact Hnd); exact Hnd. }
    apply (card_join wdec decO Om Oo Acc (fun w => vals9 w = tvI w) (fun w o => PreAcc w /\ AccOw w o)
             mix_bound Bo hOm HOo).
    + intro w. destruct (ldec (vals9 w) (tvI w)); [left | right]; assumption.
    + exact (mix_sound hnw).
    + intros w o _ hd [hp _]. exact (link w hp hd).
    + intros w hw hd. eapply card_le_mono; [ | apply le_n | exact (Hopen w hw hd)].
      intros o _ [_ h]. exact h.
  Qed.

End MixSound.
