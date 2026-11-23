(* The sums of the three summands over their cubes (paper, Figure 1, the
   three displayed claims, and the remark "Sumcheck B").

   Each theorem writes "true sum minus claimed sum" in the form that the
   counting lemmas of EqBatch.v expect.

   - A_claim_diff: for sumcheck A,
       sum gA - (k1 + k2 + rhoA * G)
         = k1 * mle (u*h - 1) tc + k2 * mle (uhat*hhat - 1) tc
           + k3 * sum (u - uhat) + rhoA * (G' - G),
     G' being the true sum of the committed mask;
   - C_claim_diff: for sumcheck C,
       sum gC - rhoC * G = sum_k kc_k * mle (w_k^3 - w_k) tz + rhoC * (G' - G);
   - B_identity: for sumcheck B, with the table
       htab bb = zp bb + sum_y sum_k rp_k y * W_k (y ++ bb) + beta * idr bb - alpha
     (h_i = z_i + beta i - alpha, and z_i = zpub_i + <rho', w_i>),
       sum gB = (hstar r - mle zp r - beta * idr r + alpha) + rhoB * G'
     where hstar is the masked extension of htab. So the claim of B,
     H - mle zp r - beta * idr r + alpha + rhoB * G, differs from the true
     sum by (hstar r - H) + rhoB * (G' - G). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Sumcheck SumcheckMask PolyFun MaskedExt CubeIndex EqBatch MixSummands.
Import ListNotations.

Section MixIdentities.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation fsum := (@fsum F zero add).
  Local Notation dot := (@dot F zero add mul).
  Local Notation nF := (@nF F zero one add).
  Local Notation cube := (@cube F zero one).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation tsum := (@tsum F zero one add).
  Local Notation idr := (@idr F zero one add mul).
  Local Notation coefs := (@coefs F zero one add mul sub).
  Local Notation cube3 := (@cube3 F mul sub).

  Lemma fsum_const : forall {A : Type} (c : F) (l : list A),
    fsum (map (fun _ => c) l) = nF (length l) * c.
  Proof. intros A c; induction l as [| a l ih]; cbn; [field | rewrite ih; field]. Qed.

  Lemma fsum_scale : forall {A : Type} (c : F) (g : A -> F) (l : list A),
    fsum (map (fun a => c * g a) l) = c * fsum (map g l).
  Proof. intros. apply (@fsum_map_mul_l F zero one add mul sub div opp inv Hf). Qed.

  Lemma fsum_add : forall {A : Type} (g h : A -> F) (l : list A),
    fsum (map (fun a => g a + h a) l) = fsum (map g l) + fsum (map h l).
  Proof. intros. apply (@fsum_map_add F zero one add mul sub div opp inv Hf). Qed.

  Lemma fsum_ext : forall {A : Type} (g h : A -> F) (l : list A),
    (forall a, In a l -> g a = h a) -> fsum (map g l) = fsum (map h l).
  Proof. intros. apply (@fsum_map_ext F zero add); assumption. Qed.

  (* ------------------------------------------------------------------ *)
  Section A.
    Variable ell : nat.
    Hypothesis Hell : (1 <= ell)%nat.
    Variables u uh sg h zh : list F -> F.
    Variables au auh asg ah : F.
    Variables alpha beta : F.
    Variable tc : list F.
    Variables k1 k2 k3 rhoA : F.
    Variable a0A : F.
    Variable csA : list (list F).
    Hypothesis Htc : length tc = ell.

    Local Notation gA := (@gA F zero one add mul sub ell u uh sg h zh au auh asg ah alpha beta tc k1 k2 k3 rhoA a0A csA).

    (* the table hhat *)
    Definition hhtab (b : list F) : F := zh b + beta * sg b - alpha.

    Definition TA1 (b : list F) : F := u b * h b - one.
    Definition TA2 (b : list F) : F := uh b * hhtab b - one.
    Definition SA : F := fsum (map (fun b => u b - uh b) (cube ell)).
    Definition GtrueA : F := tsum (gmask a0A csA) [] ell.

    Lemma gA_cube : forall b, In b (cube ell) ->
      gA b = k1 * (eqp b tc * (u b * h b)) + k2 * (eqp b tc * (uh b * hhtab b))
             + k3 * (u b - uh b) + rhoA * gmask a0A csA b.
    Proof.
      intros b hb. unfold MixSummands.gA, MixSummands.ustar, MixSummands.uhstar, MixSummands.hstar,
        MixSummands.hhstar, MixSummands.sgstar, hhtab.
      rewrite !(@mstar_cube_pos F zero one add mul sub div opp inv Hf ell _ _ b Hell hb).
      rewrite (@mle_cube F zero one add mul sub div opp inv Hf ell zh b hb). field.
    Qed.

    Theorem tsum_gA :
      tsum gA [] ell =
      k1 * mle ell (fun b => u b * h b) tc + k2 * mle ell (fun b => uh b * hhtab b) tc
      + k3 * SA + rhoA * GtrueA.
    Proof.
      unfold Sumcheck.tsum at 1. cbn [app].
      rewrite (fsum_ext (fun b => gA b) _ _ gA_cube).
      rewrite !fsum_add, !fsum_scale.
      rewrite !(@mle_weighted F zero one add mul sub div opp inv Hf).
      reflexivity.
    Qed.

    Theorem A_claim_diff : forall G : F,
      tsum gA [] ell - (k1 + k2 + rhoA * G) = dot (coefs ell [TA1; TA2] [SA; GtrueA - G] tc) [k1; k2; k3; rhoA].
    Proof.
      intro G. rewrite tsum_gA. unfold EqBatch.coefs, TA1, TA2. cbn [map app LogDer.dot].
      rewrite !(@mle_sub F zero one add mul sub div opp inv Hf).
      rewrite !(@mle_const F zero one add mul sub div opp inv Hf ell one tc Htc). field.
    Qed.
  End A.

  (* ------------------------------------------------------------------ *)
  Section C.
    Variable m : nat.
    Hypothesis Hm : (1 <= m)%nat.
    Variables W1 W2 W3 : list F -> F.
    Variables aw1 aw2 aw3 : F.
    Variable tz : list F.
    Variables kc1 kc2 kc3 rhoC : F.
    Variable a0C : F.
    Variable csC : list (list F).

    Local Notation gC := (@gC F zero one add mul sub m W1 W2 W3 aw1 aw2 aw3 tz kc1 kc2 kc3 rhoC a0C csC).

    Definition TC1 (b : list F) : F := cube3 (W1 b).
    Definition TC2 (b : list F) : F := cube3 (W2 b).
    Definition TC3 (b : list F) : F := cube3 (W3 b).
    Definition GtrueC : F := tsum (gmask a0C csC) [] m.

    Lemma gC_cube : forall b, In b (cube m) ->
      gC b = kc1 * (eqp b tz * TC1 b) + kc2 * (eqp b tz * TC2 b) + kc3 * (eqp b tz * TC3 b)
             + rhoC * gmask a0C csC b.
    Proof.
      intros b hb. unfold MixSummands.gC, MixSummands.wstar1, MixSummands.wstar2, MixSummands.wstar3, TC1, TC2, TC3.
      rewrite !(@mstar_cube_pos F zero one add mul sub div opp inv Hf m _ _ b Hm hb). field.
    Qed.

    Theorem C_claim_diff : forall G : F,
      tsum gC [] m - rhoC * G = dot (coefs m [TC1; TC2; TC3] [GtrueC - G] tz) [kc1; kc2; kc3; rhoC].
    Proof.
      intro G. unfold Sumcheck.tsum at 1. cbn [app].
      rewrite (fsum_ext (fun b => gC b) _ _ gC_cube).
      rewrite !fsum_add, !fsum_scale.
      rewrite !(@mle_weighted F zero one add mul sub div opp inv Hf).
      unfold EqBatch.coefs. cbn [map app LogDer.dot]. unfold GtrueC, Sumcheck.tsum. cbn [app].
      change (fun b : list F => gmask a0C csC b) with (gmask a0C csC). field.
    Qed.
  End C.

  (* ------------------------------------------------------------------ *)
  Section B.
    Variables n1 ell : nat.
    Variables rp1 rp2 rp3 : list F -> F.
    Variables W1 W2 W3 : list F -> F.
    Variable zp : list F -> F.
    Variables alpha beta : F.
    Variable r : list F.
    Variables ah cB rhoB : F.
    Variable a0B : F.
    Variable csB : list (list F).
    Hypothesis Hr : length r = ell.
    Hypothesis HcB : nF (2 ^ n1) * cB = ah * Zp r.

    Local Notation gB := (@gB F zero one add mul sub n1 ell rp1 rp2 rp3 W1 W2 W3 r cB rhoB a0B csB).

    (* <rho', w_bb>: the effect of the re-randomiser of ballot bb on its projection *)
    Definition lintab (bb : list F) : F :=
      fsum (map (fun y => rp1 y * W1 (y ++ bb) + rp2 y * W2 (y ++ bb) + rp3 y * W3 (y ++ bb)) (cube n1)).

    (* h_bb = z_bb + beta * bb - alpha *)
    Definition htab (bb : list F) : F := zp bb + lintab bb + beta * idr bb - alpha.

    Definition GtrueB : F := tsum (gmask a0B csB) [] n1.

    Lemma mle_htab : mle ell htab r = mle ell zp r + mle ell lintab r + beta * idr r - alpha.
    Proof.
      unfold htab.
      rewrite (@mle_sub F zero one add mul sub div opp inv Hf).
      rewrite !(@mle_add F zero one add mul sub div opp inv Hf).
      rewrite (@mle_scale F zero one add mul sub div opp inv Hf).
      rewrite (@mle_idr F zero one add mul sub div opp inv Hf ell r Hr).
      rewrite (@mle_const F zero one add mul sub div opp inv Hf ell alpha r Hr). reflexivity.
    Qed.

    Lemma mle_lintab :
      mle ell lintab r =
      fsum (map (fun y => rp1 y * mle (n1 + ell) W1 (y ++ r) + rp2 y * mle (n1 + ell) W2 (y ++ r)
                          + rp3 y * mle (n1 + ell) W3 (y ++ r)) (cube n1)).
    Proof.
      unfold lintab.
      rewrite (@mle_fsum F zero one add mul sub div opp inv Hf _ ell
                 (fun y bb => rp1 y * W1 (y ++ bb) + rp2 y * W2 (y ++ bb) + rp3 y * W3 (y ++ bb)) (cube n1) r Hr).
      apply fsum_ext. intros y hy.
      rewrite !(@mle_add F zero one add mul sub div opp inv Hf).
      rewrite !(@mle_scale F zero one add mul sub div opp inv Hf).
      rewrite !(@mle_prefix_cube F zero one add mul sub div opp inv Hf n1 ell _ y r hy). reflexivity.
    Qed.

    Theorem B_identity :
      tsum gB [] n1 = (mstar ell htab ah r - mle ell zp r - beta * idr r + alpha) + rhoB * GtrueB.
    Proof.
      unfold MaskedExt.mstar. rewrite mle_htab, mle_lintab, <-HcB.
      unfold Sumcheck.tsum at 1. cbn [app].
      rewrite (fsum_ext _ (fun y => (rp1 y * mle (n1 + ell) W1 (y ++ r) + rp2 y * mle (n1 + ell) W2 (y ++ r)
                                     + rp3 y * mle (n1 + ell) W3 (y ++ r)) + cB + rhoB * gmask a0B csB y)).
      + rewrite !fsum_add, fsum_scale, fsum_const.
        assert (hcl : length (cube n1) = (2 ^ n1)%nat) by (unfold Mle.cube; rewrite all_lists_length; reflexivity).
        rewrite hcl.
        unfold GtrueB, Sumcheck.tsum. cbn [app].
        change (fun b : list F => gmask a0B csB b) with (gmask a0B csB). field.
      + intros y hy. unfold MixSummands.gB.
        rewrite !(@mle_cube F zero one add mul sub div opp inv Hf n1 _ y hy). reflexivity.
    Qed.

    (* The claim of sumcheck B against its true sum. *)
    Corollary B_claim_diff : forall H G : F,
      tsum gB [] n1 - (H - mle ell zp r - beta * idr r + alpha + rhoB * G)
      = (mstar ell htab ah r - H) + rhoB * (GtrueB - G).
    Proof. intros H G. rewrite B_identity. field. Qed.
  End B.

End MixIdentities.
