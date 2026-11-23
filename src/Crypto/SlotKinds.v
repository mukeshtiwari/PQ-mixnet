(* The two kinds of slot of the implementation (fp_core.py, _slots_compile)
   and the batching identity for them: the hypothesis Hbatch of open_sound.

   A term is (slot, row, coef, lv). The slot has a kind:
     tensor   many rows share the fixed slot vector Lt slot; lv is unused;
     func     the slot lives on one row frow slot, and lv is a functional
              on that row.
   The term contributes  coef * <P row, Lt slot>  resp.  coef * <P row, lv>
   to its claim; gtval is the value of a claim.

   For a batching challenge kappa the verifier compiles, per slot,
     tensor:  rows cbk = all (row, kappa_i * coef) of the slot,  vector Lt;
     func:    rows cbk = [(frow, 1)],  vector Lk = sum kappa_i * coef * lv.

   Theorem batch_mixed: summed over all slots, vsum P (cbk kappa v) (Lk kappa v)
   is <kappa, values of the claims>. So the opening of the batched slots
   proves the kappa-combination of the claims, for both kinds.

   The implementation merges repeated rows of a tensor slot by adding
   their weights; here they stay as separate entries, which gives the same
   combination. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon Opening.
Import ListNotations.

Section SlotKinds.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation vsum := (@vsum F zero add mul).

  Record gterm : Type := mk_gterm {
    tslot : nat;
    trow : nat;
    tcoef : F;
    tlv : list F
  }.

  Variable P : nat -> list F.          (* decoded rows *)
  Variable kind : nat -> bool.         (* true: func slot *)
  Variable Lt : nat -> list F.         (* vector of a tensor slot *)
  Variable frow : nat -> nat.          (* the row of a func slot *)

  (* the vector a term is paired with *)
  Definition Lof (t : gterm) : list F := if kind (tslot t) then tlv t else Lt (tslot t).

  Fixpoint gtval (cl : list gterm) : F :=
    match cl with
    | [] => zero
    | t :: cl' => tcoef t * dot (P (trow t)) (Lof t) + gtval cl'
    end.

  (* contribution of one claim, scaled by k0, to slot v *)
  Fixpoint contrib (k0 : F) (cl : list gterm) (v : nat) : F :=
    match cl with
    | [] => zero
    | t :: cl' =>
        (if Nat.eqb (tslot t) v then k0 * tcoef t * dot (P (trow t)) (Lof t) else zero) + contrib k0 cl' v
    end.

  Fixpoint slotval (kp : list F) (cls : list (list gterm)) (v : nat) : F :=
    match kp, cls with
    | k0 :: kp', cl :: cls' => contrib k0 cl v + slotval kp' cls' v
    | _, _ => zero
    end.

  Lemma contrib_sum : forall (vs : list nat) k0 cl, NoDup vs ->
    (forall t, In t cl -> In (tslot t) vs) ->
    fsum (map (contrib k0 cl) vs) = k0 * gtval cl.
  Proof.
    intros vs k0 cl hnd; induction cl as [| t cl ih]; intro hin.
    + cbn [contrib gtval]. rewrite (@fsum_map_zero_ext F zero one add mul sub div opp inv Hf) by (intros; reflexivity). field.
    + rewrite (@fsum_map_ext F zero add _ (contrib k0 (t :: cl))
                 (fun v => (if Nat.eq_dec (tslot t) v then one else zero) * (k0 * tcoef t * dot (P (trow t)) (Lof t))
                           + contrib k0 cl v)).
      - rewrite (@fsum_map_add F zero one add mul sub div opp inv Hf).
        rewrite (@fsum_indicator F zero one add mul sub div opp inv Hf nat Nat.eq_dec
                   (fun _ => k0 * tcoef t * dot (P (trow t)) (Lof t)) (tslot t) vs hnd (hin t (or_introl eq_refl))).
        change (fun v => contrib k0 cl v) with (contrib k0 cl).
        rewrite (ih (fun t' ht' => hin t' (or_intror ht'))). cbn [gtval]. field.
      - intros v _. cbn [contrib].
        destruct (Nat.eq_dec (tslot t) v) as [e | e].
        * rewrite (proj2 (Nat.eqb_eq _ _) e). field.
        * rewrite (proj2 (Nat.eqb_neq _ _) e). field.
  Qed.

  Theorem slotval_sum : forall (vs : list nat), NoDup vs ->
    forall (cls : list (list gterm)) (kp : list F), length kp = length cls ->
    (forall cl, In cl cls -> forall t, In t cl -> In (tslot t) vs) ->
    fsum (map (slotval kp cls) vs) = dot kp (map gtval cls).
  Proof.
    intros vs hnd; induction cls as [| cl cls ih]; intros kp hl hin; destruct kp as [| k0 kp]; cbn in hl; try lia.
    + cbn [slotval map]. rewrite (@fsum_map_zero_ext F zero one add mul sub div opp inv Hf) by (intros; reflexivity).
      reflexivity.
    + rewrite (@fsum_map_ext F zero add _ (slotval (k0 :: kp) (cl :: cls))
                 (fun v => contrib k0 cl v + slotval kp cls v)) by (intros; reflexivity).
      rewrite (@fsum_map_add F zero one add mul sub div opp inv Hf).
      change (fun v => contrib k0 cl v) with (contrib k0 cl).
      change (fun v => slotval kp cls v) with (slotval kp cls).
      rewrite (contrib_sum vs k0 cl hnd (hin cl (or_introl eq_refl))).
      rewrite (ih kp ltac:(lia) (fun cl' h' => hin cl' (or_intror h'))). cbn. field.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* What the verifier compiles *)

  (* tensor slot: the rows of slot v with their batched weights *)
  Fixpoint gsel (k0 : F) (cl : list gterm) (v : nat) : list (nat * F) :=
    match cl with
    | [] => []
    | t :: cl' => if Nat.eqb (tslot t) v then (trow t, k0 * tcoef t) :: gsel k0 cl' v else gsel k0 cl' v
    end.

  Fixpoint gbatch (kp : list F) (cls : list (list gterm)) (v : nat) : list (nat * F) :=
    match kp, cls with
    | k0 :: kp', cl :: cls' => gsel k0 cl v ++ gbatch kp' cls' v
    | _, _ => []
    end.

  (* func slot: the batched functional *)
  Fixpoint lsel (k0 : F) (cl : list gterm) (v : nat) : list F :=
    match cl with
    | [] => []
    | t :: cl' => if Nat.eqb (tslot t) v then padd (pscale (k0 * tcoef t) (tlv t)) (lsel k0 cl' v) else lsel k0 cl' v
    end.

  Fixpoint lsum (kp : list F) (cls : list (list gterm)) (v : nat) : list F :=
    match kp, cls with
    | k0 :: kp', cl :: cls' => padd (lsel k0 cl v) (lsum kp' cls' v)
    | _, _ => []
    end.

  Definition cbk (kp : list F) (cls : list (list gterm)) (v : nat) : list (nat * F) :=
    if kind v then [(frow v, one)] else gbatch kp cls v.

  Definition Lk (kp : list F) (cls : list (list gterm)) (v : nat) : list F :=
    if kind v then lsum kp cls v else Lt v.

  Lemma gsel_contrib : forall k0 cl v, kind v = false ->
    vsum P (gsel k0 cl v) (Lt v) = contrib k0 cl v.
  Proof.
    intros k0 cl v hk; induction cl as [| t cl ih]; cbn [gsel contrib]; [reflexivity |].
    destruct (Nat.eqb (tslot t) v) eqn:e.
    + apply Nat.eqb_eq in e. cbn [Opening.vsum fst snd]. rewrite ih.
      unfold Lof. rewrite e, hk. field.
    + rewrite ih. field.
  Qed.

  Lemma lsel_contrib : forall k0 cl v, kind v = true ->
    (forall t, In t cl -> tslot t = v -> trow t = frow v) ->
    dot (P (frow v)) (lsel k0 cl v) = contrib k0 cl v.
  Proof.
    intros k0 cl v hk; induction cl as [| t cl ih]; intro hrow; cbn [lsel contrib].
    + rewrite (@dot_nil_r F zero add mul). reflexivity.
    + specialize (ih (fun t' ht' => hrow t' (or_intror ht'))).
      destruct (Nat.eqb (tslot t) v) eqn:e.
      - apply Nat.eqb_eq in e.
        rewrite (@dot_padd_r F zero one add mul sub div opp inv Hf), (@dot_pscale_r F zero one add mul sub div opp inv Hf), ih.
        rewrite (hrow t (or_introl eq_refl) e). unfold Lof. rewrite e, hk. field.
      - rewrite ih. field.
  Qed.

  Theorem slot_compiled : forall (cls : list (list gterm)) (kp : list F) (v : nat),
    (forall cl, In cl cls -> forall t, In t cl -> kind (tslot t) = true -> trow t = frow (tslot t)) ->
    vsum P (cbk kp cls v) (Lk kp cls v) = slotval kp cls v.
  Proof.
    intros cls kp v hrow. unfold cbk, Lk. destruct (kind v) eqn:hk.
    + (* func *)
      cbn [Opening.vsum fst snd].
      transitivity (dot (P (frow v)) (lsum kp cls v)); [field |].
      revert kp; induction cls as [| cl cls ih]; intro kp; destruct kp as [| k0 kp]; cbn [lsum slotval];
        try (apply (@dot_nil_r F zero add mul)).
      rewrite (@dot_padd_r F zero one add mul sub div opp inv Hf).
      rewrite (ih (fun cl' h' => hrow cl' (or_intror h')) kp).
      rewrite (lsel_contrib k0 cl v hk); [reflexivity |].
      intros t ht e. rewrite <-e. apply (hrow cl (or_introl eq_refl) t ht). rewrite e. exact hk.
    + (* tensor *)
      clear hrow. revert kp; induction cls as [| cl cls ih]; intro kp; destruct kp as [| k0 kp]; cbn [gbatch slotval];
        try reflexivity.
      rewrite (@vsum_app F zero one add mul sub div opp inv Hf), ih, (gsel_contrib k0 cl v hk). reflexivity.
  Qed.

  (* The hypothesis Hbatch of open_sound for the two kinds of slot. *)
  Theorem batch_mixed : forall (vs : list nat) (cls : list (list gterm)) (kp : list F),
    NoDup vs -> length kp = length cls ->
    (forall cl, In cl cls -> forall t, In t cl -> In (tslot t) vs) ->
    (forall cl, In cl cls -> forall t, In t cl -> kind (tslot t) = true -> trow t = frow (tslot t)) ->
    fsum (map (fun v => vsum P (cbk kp cls v) (Lk kp cls v)) vs) = dot kp (map gtval cls).
  Proof.
    intros vs cls kp hnd hl hin hrow.
    rewrite <-(slotval_sum vs hnd cls kp hl hin).
    apply (@fsum_map_ext F zero add). intros v _. apply slot_compiled. exact hrow.
  Qed.

End SlotKinds.
