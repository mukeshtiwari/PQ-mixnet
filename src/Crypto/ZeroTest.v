(* A generic zero-test sumcheck and its soundness.

   Given tables T_1, .., T_n on the cube of m variables and a polynomial
   phi of degree at most D, the prover shows phi (T_i b) = 0 for all i and
   all cube points b by a masked sumcheck with summand

       gZ x = eq(x, t) * sum_i k_i * phi (T_i*(x)) + rho * gmask x

   and claim rho * G. The challenge is (t, k_1 .. k_n, rho).

   Instances:
     shortness of the shuffle proof     phi = w^3 - w,            3 tables
     digit range of the decryption proof  phi = prod_(v<base) (d - v), k tables
     ternary key share                  phi = w^3 - w,            2 tables (s, e)

   - certZ: the round functions have degree at most 1 + D, and 1 + 2 D in
     the last round;
   - Z_claim_diff: true sum minus claim is
     sum_i k_i * mle (phi o T_i) t + rho * (G' - G);
   - soundZ: if phi (T_i b) <> 0 for some i and cube point b, the verifier
     accepts for at most
       ((m + 1) |F|^(m+n) |F|^m + dsum |F|^(m-1) |C4|) |P|
     challenge tuples, for an adaptive prover and an arbitrary finite type
     P of earlier challenges. Acceptance includes the ideal claims: the
     claimed evaluations are the masked extensions at the end point, and
     the final claim is consistent with the mask at that point. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting Card LogDer Mle Negacyclic Sumcheck SumcheckMask SumcheckSound PolyFun MaskedExt CubeIndex EqBatch MixSummands MixIdentities.
Import ListNotations.

Section ZeroTest.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation peval := (@eval F zero add mul).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation is_poly := (@is_poly F zero add mul).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation rnd := (@rnd F zero one add).
  Local Notation sc_run := (@sc_run F zero one add mul Fdec).
  Local Notation coefs := (@coefs F zero one add mul sub).
  Local Notation lastdeg := MaskedExt.lastdeg.

  Variable m : nat.
  Hypothesis Hm : (1 <= m)%nat.
  Variable phi : list F.
  Variable D : nat.
  Hypothesis Hphi : (length phi <= S D)%nat.

  (* sum_i k_i * phi (T_i*(x)) *)
  Fixpoint inner (ks : list F) (Ts : list (list F -> F)) (avs : list F) (x : list F) : F :=
    match ks, Ts, avs with
    | k :: ks', T :: Ts', a :: avs' => k * peval phi (mstar m T a x) + inner ks' Ts' avs' x
    | _, _, _ => zero
    end.

  (* the same from claimed evaluations *)
  Fixpoint innerZ (ks zl : list F) : F :=
    match ks, zl with
    | k :: ks', z :: zl' => k * peval phi z + innerZ ks' zl'
    | _, _ => zero
    end.

  Fixpoint evalsOf (Ts : list (list F -> F)) (avs : list F) (r : list F) : list F :=
    match Ts, avs with
    | T :: Ts', a :: avs' => mstar m T a r :: evalsOf Ts' avs' r
    | _, _ => []
    end.

  Lemma innerZ_evals : forall ks Ts avs r, length avs = length Ts ->
    innerZ ks (evalsOf Ts avs r) = inner ks Ts avs r.
  Proof.
    induction ks as [| k ks ih]; intros Ts avs r hl; [reflexivity |].
    destruct Ts as [| T Ts], avs as [| a avs]; cbn in hl; try lia; [reflexivity |].
    cbn [evalsOf innerZ inner]. rewrite ih by lia. reflexivity.
  Qed.

  Definition gZ (ks : list F) (Ts : list (list F -> F)) (avs : list F) (t : list F) (rho a0 : F)
    (cs : list (list F)) (x : list F) : F :=
    eqp x t * inner ks Ts avs x + rho * gmask a0 cs x.

  Definition degZ (i : nat) : nat := if Nat.eqb (S i) m then 1 + (D + D) else 1 + D.

  Lemma inner_is_poly : forall ks Ts avs pre k b, (length pre + S k = m)%nat -> In b (cube k) ->
    is_poly (D * lastdeg k) (fun X => inner ks Ts avs (pre ++ X :: b)).
  Proof.
    induction ks as [| k0 ks ih]; intros Ts avs pre k b e hb.
    + cbn. apply is_poly_const.
    + destruct Ts as [| T Ts]; [cbn; apply is_poly_const |].
      destruct avs as [| a avs]; [cbn; apply is_poly_const |].
      cbn [inner].
      apply (is_poly_mono (Nat.max (D * lastdeg k) (D * lastdeg k))); [lia |].
      apply is_poly_add; [| apply ih; assumption].
      apply is_poly_scale. apply (is_poly_peval phi D _ _ Hphi).
      rewrite <-e. apply mstar_is_poly. exact hb.
  Qed.

  Theorem certZ : forall ks Ts avs t rho a0 cs,
    length cs = m -> (forall i, (i < m)%nat -> (length (nth i cs []) <= degZ i)%nat) ->
    forall pre k, (length pre + S k = m)%nat ->
    exists pstar, (length pstar <= S (degZ (length pre)))%nat /\
      forall X, peval pstar X = rnd (gZ ks Ts avs t rho a0 cs) pre k X.
  Proof.
    intros ks Ts avs t rho a0 cs hcs hdeg pre k e.
    apply (@rnd_is_poly F zero one add mul sub div opp inv Hf). intros b hb.
    assert (hD : degZ (length pre) = (1 + D * lastdeg k)%nat).
    { unfold degZ. destruct k as [| k'].
      + replace (S (length pre)) with m by lia. rewrite Nat.eqb_refl. cbn [MaskedExt.lastdeg]. lia.
      + rewrite (proj2 (Nat.eqb_neq _ _)) by lia. cbn [MaskedExt.lastdeg]. lia. }
    unfold gZ.
    apply (is_poly_mono (Nat.max (1 + D * lastdeg k) (degZ (length pre)))); [lia |].
    apply is_poly_add.
    + apply is_poly_mul; [apply (@eqp_coord_poly F zero one add mul sub div opp inv Hf) | apply inner_is_poly; assumption].
    + apply is_poly_scale.
      apply (@gmask_is_poly F zero one add mul sub div opp inv Hf); [lia | apply hdeg; lia].
  Qed.

  (* on the cube the masks disappear *)
  Fixpoint innerT (ks : list F) (Ts : list (list F -> F)) (b : list F) : F :=
    match ks, Ts with
    | k :: ks', T :: Ts' => k * peval phi (T b) + innerT ks' Ts' b
    | _, _ => zero
    end.

  Lemma inner_cube : forall ks Ts avs b, length avs = length Ts -> In b (cube m) ->
    inner ks Ts avs b = innerT ks Ts b.
  Proof.
    induction ks as [| k ks ih]; intros Ts avs b hl hb; [reflexivity |].
    destruct Ts as [| T Ts], avs as [| a avs]; cbn in hl; try lia; [reflexivity |].
    cbn [inner innerT]. rewrite ih by (try lia; exact hb).
    rewrite (@mstar_cube_pos F zero one add mul sub div opp inv Hf m T a b Hm hb). reflexivity.
  Qed.

  Definition phiT (T : list F -> F) (b : list F) : F := peval phi (T b).

  Lemma innerT_sum : forall ks Ts t, length ks = length Ts ->
    fsum (map (fun b => eqp b t * innerT ks Ts b) (cube m)) = dot (map (fun T => mle m (phiT T) t) Ts) ks.
  Proof.
    induction ks as [| k ks ih]; intros Ts t hl; destruct Ts as [| T Ts]; cbn in hl; try lia.
    + cbn. apply (@fsum_map_zero_ext F zero one add mul sub div opp inv Hf). intros; field.
    + cbn [innerT map LogDer.dot].
      rewrite (@fsum_map_ext F zero add _ _ (fun b => k * (eqp b t * phiT T b) + eqp b t * innerT ks Ts b))
        by (intros; unfold phiT; field).
      rewrite (@fsum_map_add F zero one add mul sub div opp inv Hf),
              (@fsum_map_mul_l F zero one add mul sub div opp inv Hf),
              (@mle_weighted F zero one add mul sub div opp inv Hf), (ih Ts t) by lia. field.
  Qed.

  Definition GtrueZ (a0 : F) (cs : list (list F)) : F := tsum (gmask a0 cs) [] m.

  Theorem Z_claim_diff : forall ks Ts avs t rho a0 cs G,
    length ks = length Ts -> length avs = length Ts ->
    tsum (gZ ks Ts avs t rho a0 cs) [] m - rho * G
    = dot (coefs m (map phiT Ts) [GtrueZ a0 cs - G] t) (ks ++ [rho]).
  Proof.
    intros ks Ts avs t rho a0 cs G hk ha.
    unfold EqBatch.coefs. rewrite map_map.
    rewrite (@dot_app F zero one add mul sub div opp inv Hf) by (rewrite length_map; lia).
    rewrite <-(innerT_sum ks Ts t hk).
    unfold Sumcheck.tsum at 1. cbn [app].
    rewrite (@fsum_map_ext F zero add _ (fun b => gZ ks Ts avs t rho a0 cs b)
               (fun b => eqp b t * innerT ks Ts b + rho * gmask a0 cs b)).
    2:{ intros b hb. unfold gZ. rewrite (inner_cube ks Ts avs b ha hb). reflexivity. }
    rewrite (@fsum_map_add F zero one add mul sub div opp inv Hf),
            (@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
    unfold GtrueZ, Sumcheck.tsum. cbn [app LogDer.dot].
    change (fun b : list F => gmask a0 cs b) with (gmask a0 cs). field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Soundness *)

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.

  Variable Ts : list (list F -> F).
  Local Notation n := (length Ts).

  Variable P : Type.
  Variable OP : list P.
  Hypothesis HOP : NoDup OP.
  Hypothesis decP : forall x y : P, {x = y} + {x <> y}.

  (* the prover *)
  Variable avs : P -> list F.
  Variables a0 GG : P -> F.
  Variable cs : P -> list (list F).
  Variable strat : P -> list F * list F -> list F -> list F.
  Variable zs : P -> list F * list F -> list F -> list F.

  Hypothesis Havs : forall p, length (avs p) = n.
  Hypothesis Hcs : forall p, length (cs p) = m.
  Hypothesis Hdeg : forall p i, (i < m)%nat -> (length (nth i (cs p) []) <= degZ i)%nat.
  Hypothesis Hmsg : forall p c4 pre, (length (strat p c4 pre) <= S (degZ (length pre)))%nat.

  (* the challenge (t, k_1 .. k_n ++ [rho]) *)
  Definition ksOf (c4 : list F * list F) : list F := firstn n (snd c4).
  Definition rhoOf (c4 : list F * list F) : F := nth n (snd c4) zero.

  Definition gZf (p : P) (c4 : list F * list F) : list F -> F :=
    gZ (ksOf c4) Ts (avs p) (fst c4) (rhoOf c4) (a0 p) (cs p).

  Definition claimZ (p : P) (c4 : list F * list F) : F := rhoOf c4 * GG p.

  Definition AccZ (p : P) (c4 : list F * list F) (rz : list F) : Prop :=
    exists cl,
      sc_run (strat p c4) [] rz (claimZ p c4) = Some cl /\
      zs p c4 rz = evalsOf Ts (avs p) rz /\
      cl = eqp rz (fst c4) * innerZ (ksOf c4) (zs p c4 rz) + rhoOf c4 * gmask (a0 p) (cs p) rz.

  Lemma AccZ_final : forall p c4 rz, AccZ p c4 rz ->
    sc_run (strat p c4) [] rz (claimZ p c4) = Some (gZf p c4 rz).
  Proof.
    intros p c4 rz (cl & hrun & ez & ecl).
    rewrite hrun. f_equal. rewrite ecl, ez, (innerZ_evals _ _ _ _ (Havs p)). reflexivity.
  Qed.

  Definition C4Z : list (list F * list F) := list_prod (all_lists lf m) (all_lists lf (n + 1)).
  Definition RZZ : list (list F) := all_lists lf m.

  Definition boundZ : nat :=
    ((m + 1) * length lf ^ (m + (n + 1) - 1) * length RZZ
     + dsum degZ 0 m * length lf ^ (m - 1) * length C4Z)%nat.

  Lemma firstn_nth_app : forall (l : list F) (k : nat), length l = (k + 1)%nat ->
    l = firstn k l ++ [nth k l zero].
  Proof.
    induction l as [| x l ih]; intros k hl; [cbn in hl; lia |].
    destruct k as [| k]; cbn in hl.
    + destruct l; [reflexivity | cbn in hl; lia].
    + cbn [firstn nth app]. f_equal. apply ih. lia.
  Qed.

  Theorem soundZ :
    (exists T, In T Ts /\ exists b, In b (cube m) /\ peval phi (T b) <> zero) ->
    card_le (list_prod OP (list_prod C4Z RZZ))
            (fun w => AccZ (fst w) (fst (snd w)) (snd (snd w)))
            (boundZ * length OP).
  Proof.
    intros (T & hT & b & hb & hne).
    assert (ldec : forall x y : list F, {x = y} + {x <> y}) by (apply list_eq_dec; exact Fdec).
    assert (pdec : forall x y : list F * list F, {x = y} + {x <> y}) by (decide equality).
    assert (hC4 : NoDup C4Z) by (apply NoDup_list_prod; apply all_lists_NoDup; exact Hnd).
    assert (hRZ : NoDup RZZ) by (apply all_lists_NoDup; exact Hnd).
    assert (hTne : exists T', In T' (map phiT Ts) /\ exists b0, In b0 (cube m) /\ T' b0 <> zero).
    { exists (phiT T). split; [apply in_map; exact hT | exists b; split; [exact hb | exact hne]]. }
    apply (card_le_prod_fiber decP OP (list_prod C4Z RZZ)
             (fun w => AccZ (fst w) (fst (snd w)) (snd (snd w))) boundZ HOP).
    intros p _. cbn [fst snd].
    set (E6 := fun c4 => claimZ p c4 = tsum (gZf p c4) [] m).
    assert (h6 : card_le C4Z E6 ((m + 1) * length lf ^ (m + (n + 1) - 1))).
    { pose proof (@eq_batch_card F zero one add mul sub div opp inv Fdec Hf lf Hnd m
                    (map phiT Ts) [GtrueZ (a0 p) (cs p) - GG p] (or_introl hTne)) as h.
      rewrite length_map in h. cbn [length] in h.
      eapply card_le_mono; [ | apply le_n | exact h].
      intros [t kl] hin e. cbn [fst snd]. unfold C4Z in hin. apply in_prod_iff in hin. destruct hin as [_ hk].
      apply all_lists_In in hk. destruct hk as [hk _].
      rewrite (firstn_nth_app kl n hk).
      assert (hfl : length (firstn n kl) = n) by (rewrite length_firstn; lia).
      rewrite <-(Z_claim_diff (firstn n kl) Ts (avs p) t (nth n kl zero) (a0 p) (cs p) (GG p) hfl (Havs p)).
      unfold E6, gZf, claimZ, ksOf, rhoOf in e. cbn [fst snd] in e. rewrite <-e. field. }
    pose proof (card_le_prod_cyl ldec C4Z RZZ E6 _ hRZ h6) as hE6.
    assert (h7 : card_le (list_prod C4Z RZZ) (fun w => ~ E6 (fst w) /\ AccZ p (fst w) (snd w))
                   (dsum degZ 0 m * length lf ^ (m - 1) * length C4Z)).
    { apply (card_le_prod_fiber pdec C4Z RZZ (fun w => ~ E6 (fst w) /\ AccZ p (fst w) (snd w)) _ hC4).
      intros c4 _. cbn [fst snd].
      destruct (Fdec (claimZ p c4) (tsum (gZf p c4) [] m)) as [e | e].
      + apply (card_le_mono _ _ (fun _ => False) _ 0); [| lia | apply card_le_false; tauto].
        intros rz _ [hn _]. apply hn. exact e.
      + pose proof (@sc_sound F zero one add mul sub div opp inv Fdec Hf lf Hnd (gZf p c4) m degZ
                      (strat p c4) (Hmsg p c4)
                      (certZ (ksOf c4) Ts (avs p) (fst c4) (rhoOf c4) (a0 p) (cs p) (Hcs p) (Hdeg p))
                      m [] (claimZ p c4) eq_refl e) as h.
        eapply card_le_mono; [ | apply le_n | exact h].
        intros rz _ [_ hacc]. cbn [app length]. apply AccZ_final. exact hacc. }
    pose proof (card_le_or _ _ _ _ _ hE6 h7) as hor.
    eapply card_le_mono; [ | | exact hor].
    + intros [c4 rz] _ hacc. cbn [fst snd] in *.
      destruct (Fdec (claimZ p c4) (tsum (gZf p c4) [] m)) as [e | e]; [left; exact e | right; split; assumption].
    + unfold boundZ. lia.
  Qed.

End ZeroTest.
