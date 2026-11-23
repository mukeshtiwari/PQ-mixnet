(* The row layout of the shuffle proof and the nine claims of its opening
   (mix_proof.py: MixParams, mix_derive), with the layout identity.

   P is the family of decoded rows. Rows of the big matrix keep their
   index; rows of the small matrix are shifted by SO.

     big matrix     W_k in rows k * rw + t                 (k = 0, 1, 2)
     small matrix   sigma in rows 0 .. rs - 1
                    u as two tables in rows c1 .. and c1 + rs ..
                    uhat as two tables in rows c1 + 2 rs .. and c1 + 3 rs ..
                    the mask table in row c1 + 4 rs,   c1 = rs + 6
     mask table     entries 0..6: a_u, a_uhat, a_sigma, a_h, a_w1, a_w2, a_w3
                    then the masks of sumchecks A, B, C at offA, offB, offC

   Slots: 1 and 2 are tensor slots of the big matrix (points (ry, r) and
   rz), 3 is the tensor slot of the small matrix (point r), 4 is the func
   slot on the mask-table row.

   The tables that the soundness theorem speaks about are read off the
   decoded rows: W1T, W2T, W3T, sgT, uT = u0 + tg * u1, uhT, and the mask
   coefficients and sumcheck masks from the mask-table row.

   Theorem layout_identity: the values of the nine claims on the decoded
   rows (gtval) are the nine ideal values of MixSound.v (tvI): the masked
   evaluations of u, uhat, sigma at r, the summand of sumcheck B at ry,
   the masked evaluations of W1, W2, W3 at rz, and the masks of sumchecks
   A and C at r and rz. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Sumcheck SumcheckMask MaskedExt CubeIndex Opening MixSummands LayoutLemmas SlotKinds RowLayout.
Import ListNotations.

Section MixLayout.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Notation dot := (@dot F zero add mul).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation gB := (@gB F zero one add mul sub).
  Local Notation gterm := (@gterm F).
  Local Notation tabt := (@tabt F zero one add mul sub).
  Local Notation lovec := (@lovec F zero one add mul sub).
  Local Notation gfunv := (@gfunv F zero mul).
  Local Notation funcv := (@funcv F one mul).
  Local Notation unitv := (@unitv F zero one).
  Local Notation ment := (@ment F zero add mul).
  Local Notation maskA0 := (@maskA0 F zero add mul).
  Local Notation maskCs := (@maskCs F zero add mul).

  Variable P : nat -> list F.          (* decoded rows *)
  Variable tg invN : F.                (* t, and 1/N *)
  Variables n1 ell lo1 lo2 SO : nat.
  Local Notation m := (n1 + ell)%nat.
  Variables dA dB dC : list nat.       (* round degrees of the three sumchecks *)

  Definition rw : nat := (2 ^ hiE m lo1)%nat.
  Definition rs : nat := (2 ^ hiE ell lo2)%nat.

  (* rows *)
  Definition rW (k : nat) : nat := (k * rw)%nat.
  Definition rSg : nat := SO.
  Definition rU0 : nat := (SO + (rs + 6))%nat.
  Definition rU1 : nat := (SO + (rs + 6) + rs)%nat.
  Definition rUh0 : nat := (SO + (rs + 6) + 2 * rs)%nat.
  Definition rUh1 : nat := (SO + (rs + 6) + 3 * rs)%nat.
  Definition rM : nat := (SO + (rs + 6) + 4 * rs)%nat.

  (* offsets in the mask table *)
  Definition offA : nat := 7.
  Definition offB : nat := (offA + 1 + dsumL dA)%nat.
  Definition offC : nat := (offB + 1 + dsumL dB)%nat.

  (* slot kinds *)
  Definition kindM (v : nat) : bool := Nat.eqb v 4.
  Definition frowM (v : nat) : nat := rM.

  (* the tables and masks read off the decoded rows *)
  Local Notation rdtab := (@rdtab F zero one Fdec P).
  Definition W1T : list F -> F := rdtab (rW 0) m lo1.
  Definition W2T : list F -> F := rdtab (rW 1) m lo1.
  Definition W3T : list F -> F := rdtab (rW 2) m lo1.
  Definition sgT : list F -> F := rdtab rSg ell lo2.
  Definition uT (b : list F) : F := rdtab rU0 ell lo2 b + tg * rdtab rU1 ell lo2 b.
  Definition uhT (b : list F) : F := rdtab rUh0 ell lo2 b + tg * rdtab rUh1 ell lo2 b.

  Definition Pm : list F := P rM.
  Definition auT : F := ment tg Pm 0.
  Definition auhT : F := ment tg Pm 1.
  Definition asgT : F := ment tg Pm 2.
  Definition ahT : F := ment tg Pm 3.
  Definition aw1T : F := ment tg Pm 4.
  Definition aw2T : F := ment tg Pm 5.
  Definition aw3T : F := ment tg Pm 6.
  Definition a0AT : F := maskA0 tg Pm offA.
  Definition csAT : list (list F) := maskCs tg Pm offA dA.
  Definition a0BT : F := maskA0 tg Pm offB.
  Definition csBT : list (list F) := maskCs tg Pm offB dB.
  Definition a0CT : F := maskA0 tg Pm offC.
  Definition csCT : list (list F) := maskCs tg Pm offC dC.

  (* ------------------------------------------------------------------ *)
  (* the challenges that the claims depend on *)
  Variables r ry rz : list F.
  Variable rhoB : F.
  Variables rp1 rp2 rp3 : list F -> F.     (* the three blocks of rho', as tables *)

  Hypothesis Hr : length r = ell.
  Hypothesis Hry : length ry = n1.
  Hypothesis Hrz : length rz = m.
  Hypothesis HdA : length dA = ell.
  Hypothesis HdB : length dB = n1.
  Hypothesis HdC : length dC = m.

  Definition LtM (v : nat) : list F :=
    if Nat.eqb v 1 then lovec m lo1 (ry ++ r)
    else if Nat.eqb v 2 then lovec m lo1 rz
    else lovec ell lo2 r.

  Definition gt4 (coef : F) (lv : list F) : gterm := mk_gterm 4 rM coef lv.

  Definition cl1 : list gterm :=
    tabt 3 rU0 one ell lo2 r ++ tabt 3 rU1 tg ell lo2 r ++ [gt4 (Zp r) (unitv tg 0)].
  Definition cl2 : list gterm :=
    tabt 3 rUh0 one ell lo2 r ++ tabt 3 rUh1 tg ell lo2 r ++ [gt4 (Zp r) (unitv tg 1)].
  Definition cl3 : list gterm :=
    tabt 3 rSg one ell lo2 r ++ [gt4 (Zp r) (unitv tg 2)].
  Definition cl4 : list gterm :=
    tabt 1 (rW 0) (mle n1 rp1 ry) m lo1 (ry ++ r) ++ tabt 1 (rW 1) (mle n1 rp2 ry) m lo1 (ry ++ r)
    ++ tabt 1 (rW 2) (mle n1 rp3 ry) m lo1 (ry ++ r)
    ++ [gt4 (Zp r * invN) (unitv tg 3); gt4 rhoB (gfunv tg offB (funcv dB ry))].
  Definition cl5 : list gterm := tabt 2 (rW 0) one m lo1 rz ++ [gt4 (Zp rz) (unitv tg 4)].
  Definition cl6 : list gterm := tabt 2 (rW 1) one m lo1 rz ++ [gt4 (Zp rz) (unitv tg 5)].
  Definition cl7 : list gterm := tabt 2 (rW 2) one m lo1 rz ++ [gt4 (Zp rz) (unitv tg 6)].
  Definition cl8 : list gterm := [gt4 one (gfunv tg offA (funcv dA r))].
  Definition cl9 : list gterm := [gt4 one (gfunv tg offC (funcv dC rz))].

  Definition claims9 : list (list gterm) := [cl1; cl2; cl3; cl4; cl5; cl6; cl7; cl8; cl9].

  (* where the terms of the nine claims live *)
  Lemma claims9_terms : forall cl t, In cl claims9 -> In t cl ->
    (tslot t = 1%nat /\ exists k j, (k < 3)%nat /\ (j < rw)%nat /\ trow t = (k * rw + j)%nat)
    \/ (tslot t = 2%nat /\ exists k j, (k < 3)%nat /\ (j < rw)%nat /\ trow t = (k * rw + j)%nat)
    \/ (tslot t = 3%nat /\ exists j, (j < rs)%nat /\
          (trow t = (SO + j)%nat \/ exists a, (a < 4)%nat /\ trow t = (SO + (rs + 6) + a * rs + j)%nat))
    \/ (tslot t = 4%nat /\ trow t = rM).
  Proof.
    intros cl t hcl ht.
    assert (h1 : forall k coef x, (k < 3)%nat -> In t (tabt 1 (rW k) coef m lo1 x) ->
              tslot t = 1%nat /\ exists k j, (k < 3)%nat /\ (j < rw)%nat /\ trow t = (k * rw + j)%nat).
    { intros k coef x hk h. destruct (@tabt_terms F zero one add mul sub _ _ _ _ _ _ _ h) as (e & j & hj & er).
      split; [exact e | exists k, j; split; [exact hk | split; [exact hj | exact er]]]. }
    assert (h2 : forall k coef x, (k < 3)%nat -> In t (tabt 2 (rW k) coef m lo1 x) ->
              tslot t = 2%nat /\ exists k j, (k < 3)%nat /\ (j < rw)%nat /\ trow t = (k * rw + j)%nat).
    { intros k coef x hk h. destruct (@tabt_terms F zero one add mul sub _ _ _ _ _ _ _ h) as (e & j & hj & er).
      split; [exact e | exists k, j; split; [exact hk | split; [exact hj | exact er]]]. }
    assert (h3s : forall coef, In t (tabt 3 rSg coef ell lo2 r) ->
              tslot t = 3%nat /\ exists j, (j < rs)%nat /\
                (trow t = (SO + j)%nat \/ exists a, (a < 4)%nat /\ trow t = (SO + (rs + 6) + a * rs + j)%nat)).
    { intros coef h. destruct (@tabt_terms F zero one add mul sub _ _ _ _ _ _ _ h) as (e & j & hj & er).
      split; [exact e | exists j; split; [exact hj | left; exact er]]. }
    assert (h3 : forall a start coef, (a < 4)%nat -> start = (SO + (rs + 6) + a * rs)%nat ->
              In t (tabt 3 start coef ell lo2 r) ->
              tslot t = 3%nat /\ exists j, (j < rs)%nat /\
                (trow t = (SO + j)%nat \/ exists a, (a < 4)%nat /\ trow t = (SO + (rs + 6) + a * rs + j)%nat)).
    { intros a start coef ha es h. destruct (@tabt_terms F zero one add mul sub _ _ _ _ _ _ _ h) as (e & j & hj & er).
      split; [exact e | exists j; split; [exact hj | right; exists a; split; [exact ha | rewrite er, es; reflexivity]]]. }
    assert (h4 : forall coef lv, t = gt4 coef lv -> tslot t = 4%nat /\ trow t = rM).
    { intros coef lv e. subst t. split; reflexivity. }
    unfold claims9 in hcl. cbn [In] in hcl.
    destruct hcl as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]]].
    + unfold cl1 in ht. apply in_app_or in ht. destruct ht as [ht | ht].
      - right; right; left. apply (h3 0%nat rU0 one); [lia | unfold rU0; lia | exact ht].
      - apply in_app_or in ht. destruct ht as [ht | ht].
        * right; right; left. apply (h3 1%nat rU1 tg); [lia | unfold rU1; lia | exact ht].
        * right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl2 in ht. apply in_app_or in ht. destruct ht as [ht | ht].
      - right; right; left. apply (h3 2%nat rUh0 one); [lia | unfold rUh0; lia | exact ht].
      - apply in_app_or in ht. destruct ht as [ht | ht].
        * right; right; left. apply (h3 3%nat rUh1 tg); [lia | unfold rUh1; lia | exact ht].
        * right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl3 in ht. apply in_app_or in ht. destruct ht as [ht | ht].
      - right; right; left. exact (h3s _ ht).
      - right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl4 in ht. apply in_app_or in ht. destruct ht as [ht | ht]; [left; exact (h1 0%nat _ _ ltac:(lia) ht) |].
      apply in_app_or in ht. destruct ht as [ht | ht]; [left; exact (h1 1%nat _ _ ltac:(lia) ht) |].
      apply in_app_or in ht. destruct ht as [ht | ht]; [left; exact (h1 2%nat _ _ ltac:(lia) ht) |].
      right; right; right. destruct ht as [<- | [<- | []]]; apply (h4 _ _ eq_refl).
    + unfold cl5 in ht. apply in_app_or in ht. destruct ht as [ht | ht].
      - right; left. exact (h2 0%nat _ _ ltac:(lia) ht).
      - right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl6 in ht. apply in_app_or in ht. destruct ht as [ht | ht].
      - right; left. exact (h2 1%nat _ _ ltac:(lia) ht).
      - right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl7 in ht. apply in_app_or in ht. destruct ht as [ht | ht].
      - right; left. exact (h2 2%nat _ _ ltac:(lia) ht).
      - right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl8 in ht. right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
    + unfold cl9 in ht. right; right; right. destruct ht as [<- | []]. apply (h4 _ _ eq_refl).
  Qed.

  Local Notation gtval := (@gtval F zero add mul P kindM LtM).

  (* value of a term on the mask-table row *)
  Lemma gt4_val : forall coef lv, gtval [gt4 coef lv] = coef * dot Pm lv.
  Proof. intros. cbn. unfold Pm. field. Qed.

  Lemma tab3 : forall start coef, gtval (tabt 3 start coef ell lo2 r) = coef * mle ell (rdtab start ell lo2) r.
  Proof.
    intros start coef.
    apply (@tensor_claim F zero one add mul sub div opp inv Hf P kindM LtM 3 start coef ell lo2 r);
      [reflexivity | reflexivity | exact Hr |].
    intros y t hy ht. apply (@rdtab_spec F zero one add mul sub div opp inv Fdec Hf); assumption.
  Qed.

  Lemma tab1 : forall start coef,
    gtval (tabt 1 start coef m lo1 (ry ++ r)) = coef * mle m (rdtab start m lo1) (ry ++ r).
  Proof.
    intros start coef.
    apply (@tensor_claim F zero one add mul sub div opp inv Hf P kindM LtM 1 start coef m lo1 (ry ++ r));
      [reflexivity | reflexivity | rewrite length_app; lia |].
    intros y t hy ht. apply (@rdtab_spec F zero one add mul sub div opp inv Fdec Hf); assumption.
  Qed.

  Lemma tab2 : forall start coef, gtval (tabt 2 start coef m lo1 rz) = coef * mle m (rdtab start m lo1) rz.
  Proof.
    intros start coef.
    apply (@tensor_claim F zero one add mul sub div opp inv Hf P kindM LtM 2 start coef m lo1 rz);
      [reflexivity | reflexivity | exact Hrz |].
    intros y t hy ht. apply (@rdtab_spec F zero one add mul sub div opp inv Fdec Hf); assumption.
  Qed.

  Lemma mle_two : forall (T0 T1 : list F -> F) (x : list F),
    mle ell (fun b => T0 b + tg * T1 b) x = mle ell T0 x + tg * mle ell T1 x.
  Proof.
    intros T0 T1 x.
    rewrite (@mle_add F zero one add mul sub div opp inv Hf ell T0 (fun b => tg * T1 b) x).
    rewrite (@mle_scale F zero one add mul sub div opp inv Hf). reflexivity.
  Qed.

  Theorem layout_identity :
    map gtval claims9 =
    [ mstar ell uT auT r; mstar ell uhT auhT r; mstar ell sgT asgT r;
      gB n1 ell rp1 rp2 rp3 W1T W2T W3T r (ahT * Zp r * invN) rhoB a0BT csBT ry;
      mstar m W1T aw1T rz; mstar m W2T aw2T rz; mstar m W3T aw3T rz;
      gmask a0AT csAT r; gmask a0CT csCT rz ].
  Proof.
    unfold claims9. cbn [map].
    assert (e1 : gtval cl1 = mstar ell uT auT r).
    { unfold cl1. rewrite !(@gtval_app F zero one add mul sub div opp inv Hf), !tab3, gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf).
      unfold MaskedExt.mstar, uT, auT. rewrite mle_two. field. }
    assert (e2 : gtval cl2 = mstar ell uhT auhT r).
    { unfold cl2. rewrite !(@gtval_app F zero one add mul sub div opp inv Hf), !tab3, gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf).
      unfold MaskedExt.mstar, uhT, auhT. rewrite mle_two. field. }
    assert (e3 : gtval cl3 = mstar ell sgT asgT r).
    { unfold cl3. rewrite (@gtval_app F zero one add mul sub div opp inv Hf), tab3, gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf).
      unfold MaskedExt.mstar, sgT, asgT. field. }
    assert (e4 : gtval cl4 = gB n1 ell rp1 rp2 rp3 W1T W2T W3T r (ahT * Zp r * invN) rhoB a0BT csBT ry).
    { unfold cl4. rewrite !(@gtval_app F zero one add mul sub div opp inv Hf), !tab1.
      change [gt4 (Zp r * invN) (unitv tg 3); gt4 rhoB (gfunv tg offB (funcv dB ry))]
        with ([gt4 (Zp r * invN) (unitv tg 3)] ++ [gt4 rhoB (gfunv tg offB (funcv dB ry))]).
      rewrite (@gtval_app F zero one add mul sub div opp inv Hf), !gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf).
      rewrite <-(@mask_row_gmask F zero one add mul sub div opp inv Hf tg Pm offB dB ry ltac:(lia)).
      unfold MixSummands.gB, W1T, W2T, W3T, ahT, a0BT, csBT. field. }
    assert (e5 : gtval cl5 = mstar m W1T aw1T rz).
    { unfold cl5. rewrite (@gtval_app F zero one add mul sub div opp inv Hf), tab2, gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf). unfold MaskedExt.mstar, W1T, aw1T. field. }
    assert (e6 : gtval cl6 = mstar m W2T aw2T rz).
    { unfold cl6. rewrite (@gtval_app F zero one add mul sub div opp inv Hf), tab2, gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf). unfold MaskedExt.mstar, W2T, aw2T. field. }
    assert (e7 : gtval cl7 = mstar m W3T aw3T rz).
    { unfold cl7. rewrite (@gtval_app F zero one add mul sub div opp inv Hf), tab2, gt4_val.
      rewrite (@dot_unitv F zero one add mul sub div opp inv Hf). unfold MaskedExt.mstar, W3T, aw3T. field. }
    assert (e8 : gtval cl8 = gmask a0AT csAT r).
    { unfold cl8. rewrite gt4_val.
      rewrite <-(@mask_row_gmask F zero one add mul sub div opp inv Hf tg Pm offA dA r ltac:(lia)).
      unfold a0AT, csAT. field. }
    assert (e9 : gtval cl9 = gmask a0CT csCT rz).
    { unfold cl9. rewrite gt4_val.
      rewrite <-(@mask_row_gmask F zero one add mul sub div opp inv Hf tg Pm offC dC rz ltac:(lia)).
      unfold a0CT, csCT. field. }
    rewrite e1, e2, e3, e4, e5, e6, e7, e8, e9. reflexivity.
  Qed.

End MixLayout.
