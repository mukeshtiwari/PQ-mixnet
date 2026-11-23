(* Building blocks of the zero-knowledge proof (paper, Theorem 5.3, steps
   (1), (2) and (4) of its proof), as bijections between the prover's
   randomness and what the verifier sees.

   (1) Masked evaluations. At a point r with Z(r) <> 0 the map
       a |-> T*(r) = mle T r + a * Z(r) is a bijection of F
       (mstar_inj, mstar_surj). Z(r) = 0 for at most 2 m |F|^(m-1) points
       (Zp_zero_card): the "good challenges" condition on r and r_z.

   (2) Masked sumcheck.
       - A round message that passes the verifier's check is determined by
         the running claim and its non-constant coefficients:
         it is sim_msg claim (tail) (check_head, sim_msg_check). Needs
         2 <> 0.
       - Hence an accepted list of round messages is sim_run of its tails
         (sim_run_complete): the simulator's "uniform among the messages
         consistent with the running claim".
       - The tail of the honest masked message of the round of variable j
         is tl pf + (rho * 2^k) * c_j (masked_tail), and c |-> t + s * c is
         a bijection on lists of the right length when s <> 0
         (affine_list_inj, affine_list_surj). So the tails are uniform when
         the mask coefficients c_j are, whatever the unmasked part pf.
       - a0 |-> G = 2^m a0 + W cs is a bijection (affine_inj, affine_surj
         with mask_tsum).

   (4) Opening. m |-> m + c * u is a bijection on vectors of length k
       (the same affine_list lemmas with s = 1 after exchanging roles; see
       shift_list_inj, shift_list_surj): the vectors ubar_v and the
       proximity vectors are uniform.

   Step (5), opened columns of data rows are uniform, is rs_hiding in
   ReedSolomon.v. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Sumcheck SumcheckMask MaskedExt.
Import ListNotations.

Section ZkBlocks.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation fsum := (@fsum F zero add).
  Local Notation peval := (@eval F zero add mul).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation sc_verify := (@sc_verify F zero one add mul Fdec).
  Local Notation two := (one + one).

  (* ------------------------------------------------------------------ *)
  (* Affine maps of F *)

  Lemma affine_inj : forall s b a a' : F, s <> zero -> b + a * s = b + a' * s -> a = a'.
  Proof.
    intros s b a a' hs e.
    assert (h : a = ((b + a * s) - b) * inv s) by (field; exact hs).
    rewrite h, e. field. exact hs.
  Qed.

  Lemma affine_surj : forall s b y : F, s <> zero -> b + ((y - b) * inv s) * s = y.
  Proof. intros s b y hs. field. exact hs. Qed.

  (* (1) masked evaluations *)
  Theorem mstar_inj : forall m T r a a', Zp r <> zero -> mstar m T a r = mstar m T a' r -> a = a'.
  Proof. intros m T r a a' hz e. unfold MaskedExt.mstar in e. exact (affine_inj _ _ _ _ hz e). Qed.

  Theorem mstar_surj : forall m T r y, Zp r <> zero ->
    mstar m T ((y - mle m T r) * inv (Zp r)) r = y.
  Proof. intros m T r y hz. unfold MaskedExt.mstar. apply affine_surj. exact hz. Qed.

  Theorem Zp_zero_card : forall (lf : list F), NoDup lf -> forall m : nat,
    card_le (all_lists lf m) (fun r => Zp r = zero) (2 * m * length lf ^ (m - 1)).
  Proof.
    intros lf hnd; induction m as [| m ih].
    + apply card_le_false. intros x hx e. cbn in hx. destruct hx as [<- | []]. cbn in e.
      exact (@zero_neq_one F eq zero one _ (eq_sym e)).
    + (* the first coordinate is 0 or 1, or the rest has a zero factor *)
      assert (h01 : card_le lf (fun x => x = zero \/ x = one) 2).
      { intros l hl _ hE.
        assert (hincl : incl l [zero; one]) by (intros x hx; destruct (hE x hx) as [-> | ->]; cbn; tauto).
        pose proof (NoDup_incl_length hl hincl) as h. cbn in h. exact h. }
      pose proof (card_le_head Fdec lf m (fun x => x = zero \/ x = one) 2 hnd h01) as hhead.
      pose proof (card_le_cons Fdec lf m (fun r => match r with x :: xs => Zp xs = zero | [] => False end)
                    _ hnd (fun x _ => ih)) as htail.
      pose proof (card_le_or _ _ _ _ _ hhead htail) as hor.
      eapply card_le_mono; [ | | exact hor].
      - intros r hin e. apply all_lists_In in hin. destruct hin as [hl _].
        destruct r as [| x xs]; [discriminate |]. cbn in e.
        destruct (Fdec x zero) as [e0 | e0]; [left; left; exact e0 |].
        destruct (Fdec x one) as [e1 | e1]; [left; right; exact e1 |].
        right.
        destruct (Fdec (Zp xs) zero) as [ez | ez]; [exact ez | exfalso].
        assert (h1 : one - x <> zero).
        { intro e2. apply e1. assert (hx : x = one - (one - x)) by field. rewrite hx, e2. field. }
        apply (@mul_nonzero F zero one add mul sub div opp inv Hf (x * (one - x)) (Zp xs));
          [apply (@mul_nonzero F zero one add mul sub div opp inv Hf); assumption | exact ez | exact e].
      - replace (S m - 1)%nat with m by lia.
        destruct m as [| m']; [cbn; lia |].
        replace (S m' - 1)%nat with m' by lia. cbn [Nat.pow]. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* (2) sumcheck messages from their tails *)

  Lemma peval_one : forall p : list F, peval p one = fsum p.
  Proof. induction p as [| c p ih]; cbn; [reflexivity | rewrite ih; field]. Qed.

  Definition sim_msg (claim : F) (nc : list F) : list F := ((claim - fsum nc) * inv two) :: nc.

  Lemma sim_msg_check : forall claim nc, two <> zero ->
    peval (sim_msg claim nc) zero + peval (sim_msg claim nc) one = claim.
  Proof.
    intros claim nc h2. unfold sim_msg. cbn [PolyRoots.eval]. rewrite peval_one. field. exact h2.
  Qed.

  Lemma check_head : forall (c0 : F) (nc : list F) (claim : F), two <> zero ->
    peval (c0 :: nc) zero + peval (c0 :: nc) one = claim -> c0 :: nc = sim_msg claim nc.
  Proof.
    intros c0 nc claim h2 e. unfold sim_msg. f_equal.
    cbn [PolyRoots.eval] in e. rewrite peval_one in e. rewrite <-e. field. exact h2.
  Qed.

  Fixpoint sim_run (tails : list (list F)) (chals : list F) (claim : F) : list (list F) :=
    match tails, chals with
    | nc :: ts, r :: cs => sim_msg claim nc :: sim_run ts cs (peval (sim_msg claim nc) r)
    | _, _ => []
    end.

  (* An accepted run is the simulator's run on its tails. *)
  Theorem sim_run_complete : two <> zero ->
    forall (msgs : list (list F)) (chals : list F) (claim c : F),
    Forall (fun p => p <> []) msgs ->
    sc_verify msgs chals claim = Some c ->
    msgs = sim_run (map (@tl F) msgs) chals claim.
  Proof.
    intros h2; induction msgs as [| p ms ih]; intros chals claim c hne hv.
    + reflexivity.
    + destruct chals as [| r cs]; [cbn in hv; discriminate |].
      inversion hne as [| ? ? hp hms]; subst.
      destruct p as [| c0 nc]; [contradiction |].
      cbn [Sumcheck.sc_verify] in hv.
      destruct (feqb (peval (c0 :: nc) zero + peval (c0 :: nc) one) claim) eqn:eb; [| discriminate].
      apply feqb_true in eb.
      pose proof (check_head c0 nc claim h2 eb) as ep.
      cbn [map tl sim_run]. rewrite <-ep. f_equal.
      exact (ih cs _ c hms hv).
  Qed.

  (* ------------------------------------------------------------------ *)
  (* lists under t + s * c and under m + t *)

  Lemma padd_nil_r : forall p : list F, padd p [] = p.
  Proof. destruct p; reflexivity. Qed.

  Lemma tl_padd : forall p q : list F, tl (padd p q) = padd (tl p) (tl q).
  Proof.
    intros p q. destruct p as [| x p]; [reflexivity |].
    destruct q as [| y q]; [cbn; rewrite padd_nil_r; reflexivity | reflexivity].
  Qed.

  Lemma pscale_pscale : forall a b (c : list F), pscale a (pscale b c) = pscale (a * b) c.
  Proof.
    intros a b c. unfold LogDer.pscale. rewrite map_map. apply map_ext. intro x. field.
  Qed.

  Theorem affine_list_inj : forall (s : F) (t c c' : list F), s <> zero ->
    length c = length c' -> padd t (pscale s c) = padd t (pscale s c') -> c = c'.
  Proof.
    intros s t c c' hs hl e.
    apply (nth_ext c c' zero zero hl). intros i _.
    pose proof (f_equal (fun l => nth i l zero) e) as ei. cbn beta in ei.
    rewrite !(@nth_padd F zero one add mul sub div opp inv Hf),
            !(@nth_pscale F zero one add mul sub div opp inv Hf) in ei.
    assert (h : nth i c zero = ((nth i t zero + s * nth i c zero) - nth i t zero) * inv s) by (field; exact hs).
    rewrite h, ei. field. exact hs.
  Qed.

  Theorem affine_list_surj : forall (s : F) (t y : list F), s <> zero -> (length t <= length y)%nat ->
    exists c, length c = length y /\ padd t (pscale s c) = y.
  Proof.
    intros s t y hs hl.
    exists (pscale (inv s) (padd y (pscale (opp one) t))).
    assert (hlen : length (pscale (inv s) (padd y (pscale (opp one) t))) = length y).
    { rewrite (@length_pscale F mul), (@length_padd F add), (@length_pscale F mul). lia. }
    split; [exact hlen |].
    apply (nth_ext _ _ zero zero).
    + rewrite (@length_padd F add), (@length_pscale F mul), hlen. lia.
    + intros i _.
      rewrite !(@nth_padd F zero one add mul sub div opp inv Hf),
              !(@nth_pscale F zero one add mul sub div opp inv Hf),
              (@nth_padd F zero one add mul sub div opp inv Hf),
              (@nth_pscale F zero one add mul sub div opp inv Hf).
      field. exact hs.
  Qed.

  (* m |-> m + t, for the masked vectors of the opening *)
  Theorem shift_list_inj : forall (t m1 m2 : list F), length m1 = length m2 ->
    padd m1 t = padd m2 t -> m1 = m2.
  Proof.
    intros t m1 m2 hl e.
    apply (nth_ext m1 m2 zero zero hl). intros i _.
    pose proof (f_equal (fun l => nth i l zero) e) as ei. cbn beta in ei.
    rewrite !(@nth_padd F zero one add mul sub div opp inv Hf) in ei.
    assert (h : nth i m1 zero = (nth i m1 zero + nth i t zero) - nth i t zero) by field.
    rewrite h, ei. field.
  Qed.

  Theorem shift_list_surj : forall (t y : list F), (length t <= length y)%nat ->
    exists m0, length m0 = length y /\ padd m0 t = y.
  Proof.
    intros t y hl.
    exists (padd y (pscale (opp one) t)).
    assert (hlen : length (padd y (pscale (opp one) t)) = length y).
    { rewrite (@length_padd F add), (@length_pscale F mul). lia. }
    split; [exact hlen |].
    apply (nth_ext _ _ zero zero).
    + rewrite (@length_padd F add), hlen. lia.
    + intros i _.
      rewrite !(@nth_padd F zero one add mul sub div opp inv Hf),
              (@nth_pscale F zero one add mul sub div opp inv Hf). field.
  Qed.

  (* The tail of the honest masked round message: pf is the coefficient
     list of the unmasked part, h :: s * c that of the mask (mask_round_poly). *)
  Theorem masked_tail : forall (pf c : list F) (rho h s : F),
    tl (padd pf (pscale rho (h :: pscale s c))) = padd (tl pf) (pscale (rho * s) c).
  Proof.
    intros pf c rho h s. rewrite tl_padd. cbn [LogDer.pscale map tl].
    fold (pscale rho (pscale s c)). rewrite pscale_pscale. reflexivity.
  Qed.

End ZkBlocks.
