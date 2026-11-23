(* The row layout of the decryption proof and the kd + 6 claims of its
   opening (dec_proof.py: DecParams, dec_derive), with the layout identity.

   P is the family of decoded rows. Rows of the big matrix keep their
   index; rows of the small matrix are shifted by SO.

     big matrix     digit table d in rows d * rw + t      (d < kd)
     small matrix   row 0: the key share s,  row 1: its noise e,
                    row 2: the mask table
     mask table     entries 0 .. kd-1: a_d;  kd: a_s;  kd+1: a_e;
                    then the masks of the two sumchecks at offG, offT

   Slots: 1 and 2 are tensor slots of the big matrix (points ptD =
   theta1 ++ theta and rz); 3, 4, 5 are func slots on the rows of s, e
   and the mask table.

   The claims:
     clD      <s, w_s> + p * sum_d base^d * digit_d~(ptD)       (value VD)
     clK      <s, w_a> + p * <e, eq(theta2)>                    (value VK)
     clZ d    masked evaluation of digit table d at rz
     clS, clE masked evaluations of s and e at rt
     clGm, clTm   the masks of the two sumchecks at rz and rt
   where w_s = sum_i eq(theta, i) * nadj (u_i) eq(theta1) and
   w_a = nadj a eq(theta2) are the adjoint vectors (tshift in
   dec_proof.py computes the same vector from the combination
   sum_i eq(theta, i) u_i; here the sum is taken after the adjoint).

   Theorems:
     claimD, claimK   public side minus the value of the claim on the
                      decoded rows is the multilinear extension of the
                      defect table of (D), resp. (K), at the challenge
                      (uses nmul_adjoint);
     layout_identityD the values of the claims on the decoded rows are
                      the ideal values tvD of DecSound.v. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Sumcheck SumcheckMask MaskedExt CubeIndex Opening MixBridge LayoutLemmas SlotKinds RowLayout ZeroTest DecSound.
Import ListNotations.

Section DecLayout.

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
  Local Notation nF := (@nF F zero one add).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation mle := (@mle F zero one add mul sub).
  Local Notation eqp := (@eqp F one add mul sub).
  Local Notation pt := (@pt F zero one).
  Local Notation mstar := (@mstar F zero one add mul sub).
  Local Notation Zp := (@Zp F one mul sub).
  Local Notation gmask := (@gmask F zero add mul).
  Local Notation nmul := (@nmul F zero add mul opp).
  Local Notation nadj := (@nadj F add mul opp).
  Local Notation gterm := (@gterm F).
  Local Notation tabt := (@tabt F zero one add mul sub).
  Local Notation lovec := (@lovec F zero one add mul sub).
  Local Notation eqvec := (@eqvec F zero one add mul sub).
  Local Notation gfunv := (@gfunv F zero mul).
  Local Notation funcv := (@funcv F one mul).
  Local Notation unitv := (@unitv F zero one).
  Local Notation ment := (@ment F zero add mul).
  Local Notation maskA0 := (@maskA0 F zero add mul).
  Local Notation maskCs := (@maskCs F zero add mul).
  Local Notation bidx := (@bidx F one Fdec).
  Local Notation evalsOf := (@evalsOf F zero one add mul sub).
  Local Notation Esum := (@Esum F zero one add mul).

  (* ------------------------------------------------------------------ *)
  (* small tools *)

  Lemma nth_map_seqF : forall (f : nat -> F) (n i : nat), (i < n)%nat -> nth i (map f (seq 0 n)) zero = f i.
  Proof.
    intros f n i hi.
    rewrite (nth_indep _ zero (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
    rewrite (map_nth f (seq 0 n) 0%nat i), seq_nth by exact hi. reflexivity.
  Qed.

  Lemma dot_trunc : forall (v p : list F) (n : nat), (length v <= n)%nat ->
    dot v p = dot v (map (fun y => nth y p zero) (seq 0 n)).
  Proof.
    induction v as [| x v ih]; intros p n hl; [reflexivity |].
    destruct n as [| n]; [cbn in hl; lia |].
    cbn [seq map]. rewrite <-seq_shift, map_map.
    destruct p as [| p0 p].
    + cbn [LogDer.dot].
      rewrite (map_ext (fun y => nth (S y) [] zero) (fun y => nth y (@nil F) zero)) by (intros [| y]; reflexivity).
      rewrite <-(ih [] n) by (cbn in hl; lia). rewrite (@dot_nil_r F zero add mul). cbn [nth]. field.
    + cbn [LogDer.dot nth]. rewrite <-(ih p n) by (cbn in hl; lia). reflexivity.
  Qed.

  Lemma firstn_pt_app : forall k x (l : list F), firstn k (pt k x ++ l) = pt k x.
  Proof.
    intros k x l. rewrite firstn_app, (@pt_length F zero one), Nat.sub_diag. cbn [firstn]. rewrite app_nil_r.
    apply firstn_all2. rewrite (@pt_length F zero one). lia.
  Qed.

  Lemma skipn_pt_app : forall k x (l : list F), skipn k (pt k x ++ l) = l.
  Proof.
    intros k x l. rewrite skipn_app, (@pt_length F zero one), Nat.sub_diag. cbn [skipn].
    rewrite (skipn_all2 (n := k)) by (rewrite (@pt_length F zero one); lia). reflexivity.
  Qed.

  (* linear combinations of vectors *)
  Fixpoint lincomb (e : nat -> F) (g : nat -> list F) (l : list nat) : list F :=
    match l with
    | [] => []
    | i :: l' => padd (pscale (e i) (g i)) (lincomb e g l')
    end.

  Lemma dot_lincomb : forall e g l (r : list F),
    dot (lincomb e g l) r = fsum (map (fun i => e i * dot (g i) r) l).
  Proof.
    intros e g; induction l as [| i l ih]; intro r; [reflexivity |].
    cbn [lincomb map LogDer.fsum].
    rewrite (@dot_padd_l F zero one add mul sub div opp inv Hf), (@dot_pscale_l F zero one add mul sub div opp inv Hf), ih.
    reflexivity.
  Qed.

  Lemma lincomb_length : forall e g l n, (forall i, (length (g i) <= n)%nat) -> (length (lincomb e g l) <= n)%nat.
  Proof.
    intros e g l n hg; induction l as [| i l ih]; cbn [lincomb]; [cbn; lia |].
    rewrite (@length_padd F add), (@length_pscale F mul). specialize (hg i). lia.
  Qed.

  Lemma nadj_length_le : forall (u rho : list F), (length (nadj u rho) <= length rho)%nat.
  Proof.
    intros u rho. destruct u as [| u0 u]; [cbn; lia |].
    rewrite (@nadj_length F add mul opp (u0 :: u) rho ltac:(discriminate)). lia.
  Qed.

  (* ------------------------------------------------------------------ *)

  Variable P : nat -> list F.          (* decoded rows *)
  Variable tg : F.
  Variables n1 ell lo1 SO kd base : nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Variables (a b : list F) (pp offB : F).
  Variables us ts : nat -> list F.
  Variables dG dT : list nat.          (* round degrees of the two sumchecks *)

  Definition rwD : nat := (2 ^ hiE m lo1)%nat.
  Definition rS : nat := SO.
  Definition rE : nat := (SO + 1)%nat.
  Definition rMd : nat := (SO + 2)%nat.

  Definition offG : nat := (kd + 2)%nat.
  Definition offT : nat := (offG + 1 + dsumL dG)%nat.

  Definition kindD (v : nat) : bool := Nat.leb 3 v.
  Definition frowD (v : nat) : nat := if Nat.eqb v 3 then rS else if Nat.eqb v 4 then rE else rMd.

  (* the tables and masks read off the decoded rows *)
  Local Notation rdtab := (@rdtab F zero one Fdec P).
  Definition digT (d : nat) : list F -> F := rdtab (d * rwD)%nat m lo1.
  Definition dtsT : list (list F -> F) := map digT (seq 0 kd).
  Definition rowT (r0 : nat) (bq : list F) : F := nth (bidx bq) (P r0) zero.
  Definition stabT : list F -> F := rowT rS.
  Definition etabT : list F -> F := rowT rE.
  Definition PmD : list F := P rMd.
  Definition avG : list F := map (ment tg PmD) (seq 0 kd).
  Definition avT : list F := [ment tg PmD kd; ment tg PmD (kd + 1)%nat].
  Definition a0GT : F := maskA0 tg PmD offG.
  Definition csGT : list (list F) := maskCs tg PmD offG dG.
  Definition a0TT : F := maskA0 tg PmD offT.
  Definition csTT : list (list F) := maskCs tg PmD offT dT.

  Local Notation sKv := (@sK F zero one n1 stabT).
  Local Notation eKv := (@eK F zero one n1 etabT).

  (* the public tables and the defect tables *)
  Definition TsT (bq : list F) : F := nth (bidx (firstn n1 bq)) (ts (bidx (skipn n1 bq))) zero.
  Definition UsT (bq : list F) : F := nth (bidx (firstn n1 bq)) (nmul (us (bidx (skipn n1 bq))) sKv) zero.
  Definition DtabT (bq : list F) : F := TsT bq - UsT bq - pp * (Esum base dtsT 0 bq - offB).
  Definition KtabT (bq : list F) : F := @Kcoef F zero one add mul sub opp a b pp n1 stabT etabT (bidx bq).

  Lemma HD_T : forall i x, (i < tau)%nat -> (x < N)%nat ->
    DtabT (pt n1 x ++ pt ell i) = @Dcoef F zero one add mul sub opp pp offB n1 ell base us ts dtsT stabT i x.
  Proof.
    intros i x hi hx. unfold DtabT, TsT, UsT, DecSound.Dcoef, DecSound.Ecoef.
    rewrite firstn_pt_app, skipn_pt_app.
    rewrite (@bidx_pt F zero one add mul sub div opp inv Fdec Hf n1 x hx),
            (@bidx_pt F zero one add mul sub div opp inv Fdec Hf ell i hi). reflexivity.
  Qed.

  Lemma HK_T : forall x, (x < N)%nat ->
    KtabT (pt n1 x) = @Kcoef F zero one add mul sub opp a b pp n1 stabT etabT x.
  Proof.
    intros x hx. unfold KtabT. rewrite (@bidx_pt F zero one add mul sub div opp inv Fdec Hf n1 x hx). reflexivity.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* rows as vectors *)

  Lemma eqvec_length : forall k (x : list F), length (eqvec k x) = (2 ^ k)%nat.
  Proof. intros k x. unfold RowLayout.eqvec. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma rowT_pt : forall r0 x, (x < N)%nat -> rowT r0 (pt n1 x) = nth x (P r0) zero.
  Proof.
    intros r0 x hx. unfold rowT. rewrite (@bidx_pt F zero one add mul sub div opp inv Fdec Hf n1 x hx). reflexivity.
  Qed.

  Lemma rows_K : forall r0, map (fun x => rowT r0 (pt n1 x)) (seq 0 N) = map (fun y => nth y (P r0) zero) (seq 0 N).
  Proof. intro r0. apply map_ext_in. intros x hx. apply in_seq in hx. apply rowT_pt. lia. Qed.

  (* a functional of length at most N sees the row through the table *)
  Lemma dot_row : forall r0 (v : list F), (length v <= N)%nat ->
    dot (P r0) v = dot v (map (fun x => rowT r0 (pt n1 x)) (seq 0 N)).
  Proof.
    intros r0 v hl. rewrite (@dot_sym F zero one add mul sub div opp inv Hf), rows_K. apply dot_trunc. exact hl.
  Qed.

  (* the row paired with eq(x) is the extension of its table *)
  Lemma row_mle : forall r0 (x : list F), dot (P r0) (eqvec n1 x) = mle n1 (rowT r0) x.
  Proof.
    intros r0 x. unfold RowLayout.eqvec.
    rewrite (@dot_seq0 F zero one add mul sub div opp inv Hf), (@mle_seq F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros y hy. apply in_seq in hy. rewrite rowT_pt by lia. reflexivity.
  Qed.

  (* the adjoint: <nadj u eq(x), s> = sum_y (u * s)_y eq(y, x) *)
  Lemma adj_sum : forall (u x : list F) (sv : list F), length sv = N ->
    dot (nadj u (eqvec n1 x)) sv
    = fsum (map (fun y => nth y (nmul u sv) zero * eqp (pt n1 y) x) (seq 0 N)).
  Proof.
    intros u x sv hl.
    rewrite <-(@nmul_adjoint F zero one add mul sub div opp inv Hf u (eqvec n1 x) sv)
      by (rewrite eqvec_length; symmetry; exact hl).
    rewrite (@dot_sym F zero one add mul sub div opp inv Hf). unfold RowLayout.eqvec.
    apply (@dot_seq0 F zero one add mul sub div opp inv Hf).
  Qed.

  Lemma sK_length : length sKv = N.
  Proof. unfold DecSound.sK. rewrite length_map, length_seq. reflexivity. Qed.

  (* ------------------------------------------------------------------ *)
  (* the challenges that the claims depend on *)
  Variables ptD th2 rz rt : list F.
  Hypothesis HptD : length ptD = m.
  Hypothesis Hth2 : length th2 = n1.
  Hypothesis Hrz : length rz = m.
  Hypothesis Hrt : length rt = n1.
  Hypothesis HdG : length dG = m.
  Hypothesis HdT : length dT = n1.

  Definition LtD (v : nat) : list F := if Nat.eqb v 1 then lovec m lo1 ptD else lovec m lo1 rz.

  Definition gS (coef : F) (lv : list F) : gterm := mk_gterm 3 rS coef lv.
  Definition gE (coef : F) (lv : list F) : gterm := mk_gterm 4 rE coef lv.
  Definition gM (coef : F) (lv : list F) : gterm := mk_gterm 5 rMd coef lv.

  (* the adjoint vectors *)
  Definition wsv : list F :=
    lincomb (fun i => eqp (pt ell i) (skipn n1 ptD)) (fun i => nadj (us i) (eqvec n1 (firstn n1 ptD))) (seq 0 tau).
  Definition wav : list F := nadj a (eqvec n1 th2).

  Definition digD (s k : nat) : list gterm :=
    concat (map (fun d => tabt 1 (d * rwD)%nat (pp * nF (base ^ d)) m lo1 ptD) (seq s k)).

  Definition clD : list gterm := gS one wsv :: digD 0 kd.
  Definition clK : list gterm := [gS one wav; gE pp (eqvec n1 th2)].
  Definition clZ (d : nat) : list gterm := tabt 2 (d * rwD)%nat one m lo1 rz ++ [gM (Zp rz) (unitv tg d)].
  Definition clS : list gterm := [gS one (eqvec n1 rt); gM (Zp rt) (unitv tg kd)].
  Definition clE : list gterm := [gE one (eqvec n1 rt); gM (Zp rt) (unitv tg (kd + 1)%nat)].
  Definition clGm : list gterm := [gM one (gfunv tg offG (funcv dG rz))].
  Definition clTm : list gterm := [gM one (gfunv tg offT (funcv dT rt))].

  Definition claimsD : list (list gterm) := clD :: clK :: map clZ (seq 0 kd) ++ [clS; clE; clGm; clTm].

  Lemma claimsD_length : length claimsD = (kd + 6)%nat.
  Proof. unfold claimsD. cbn [length]. rewrite length_app, length_map, length_seq. cbn [length]. lia. Qed.

  (* the public sides of the two compressed claims *)
  Definition VDv : F := mle m TsT ptD + pp * offB.
  Definition VKv : F := dot b (eqvec n1 th2).

  (* where the terms of the claims live *)
  Definition term_ok (t : gterm) : Prop :=
    (tslot t = 1%nat /\ exists d j, (d < kd)%nat /\ (j < rwD)%nat /\ trow t = (d * rwD + j)%nat)
    \/ (tslot t = 2%nat /\ exists d j, (d < kd)%nat /\ (j < rwD)%nat /\ trow t = (d * rwD + j)%nat)
    \/ (tslot t = 3%nat /\ trow t = rS)
    \/ (tslot t = 4%nat /\ trow t = rE)
    \/ (tslot t = 5%nat /\ trow t = rMd).

  Lemma claimsD_terms : forall cl t, In cl claimsD -> In t cl -> term_ok t.
  Proof.
    intros cl t hcl ht.
    assert (hS : forall c lv, term_ok (gS c lv)) by (intros; right; right; left; split; reflexivity).
    assert (hE : forall c lv, term_ok (gE c lv)) by (intros; right; right; right; left; split; reflexivity).
    assert (hM : forall c lv, term_ok (gM c lv)) by (intros; right; right; right; right; split; reflexivity).
    unfold claimsD in hcl. cbn [In] in hcl. destruct hcl as [<- | [<- | hcl]].
    + unfold clD in ht. destruct ht as [<- | ht]; [apply hS |].
      unfold digD in ht. apply in_concat in ht. destruct ht as (l & hl & ht).
      apply in_map_iff in hl. destruct hl as (d & <- & hd). apply in_seq in hd.
      destruct (@tabt_terms F zero one add mul sub _ _ _ _ _ _ _ ht) as (e & j & hj & er).
      left. split; [exact e | exists d, j; split; [lia | split; [exact hj | exact er]]].
    + unfold clK in ht. destruct ht as [<- | [<- | []]]; [apply hS | apply hE].
    + apply in_app_or in hcl. destruct hcl as [hcl | hcl].
      - apply in_map_iff in hcl. destruct hcl as (d & <- & hd). apply in_seq in hd.
        unfold clZ in ht. apply in_app_or in ht. destruct ht as [ht | [<- | []]]; [| apply hM].
        destruct (@tabt_terms F zero one add mul sub _ _ _ _ _ _ _ ht) as (e & j & hj & er).
        right; left. split; [exact e | exists d, j; split; [lia | split; [exact hj | exact er]]].
      - cbn [In] in hcl. destruct hcl as [<- | [<- | [<- | [<- | []]]]].
        * unfold clS in ht. destruct ht as [<- | [<- | []]]; [apply hS | apply hM].
        * unfold clE in ht. destruct ht as [<- | [<- | []]]; [apply hE | apply hM].
        * unfold clGm in ht. destruct ht as [<- | []]. apply hM.
        * unfold clTm in ht. destruct ht as [<- | []]. apply hM.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* values of the claims on the decoded rows *)

  Local Notation gtval := (@gtval F zero add mul P kindD LtD).

  Lemma gS_val : forall c lv cl, gtval (gS c lv :: cl) = c * dot (P rS) lv + gtval cl.
  Proof. reflexivity. Qed.
  Lemma gE_val : forall c lv cl, gtval (gE c lv :: cl) = c * dot (P rE) lv + gtval cl.
  Proof. reflexivity. Qed.
  Lemma gM_val : forall c lv cl, gtval (gM c lv :: cl) = c * dot PmD lv + gtval cl.
  Proof. reflexivity. Qed.

  Lemma tab1D : forall start coef,
    gtval (tabt 1 start coef m lo1 ptD) = coef * mle m (rdtab start m lo1) ptD.
  Proof.
    intros start coef.
    apply (@tensor_claim F zero one add mul sub div opp inv Hf P kindD LtD 1 start coef m lo1 ptD);
      [reflexivity | reflexivity | exact HptD |].
    intros y t hy ht. apply (@rdtab_spec F zero one add mul sub div opp inv Fdec Hf); assumption.
  Qed.

  Lemma tab2D : forall start coef,
    gtval (tabt 2 start coef m lo1 rz) = coef * mle m (rdtab start m lo1) rz.
  Proof.
    intros start coef.
    apply (@tensor_claim F zero one add mul sub div opp inv Hf P kindD LtD 2 start coef m lo1 rz);
      [reflexivity | reflexivity | exact Hrz |].
    intros y t hy ht. apply (@rdtab_spec F zero one add mul sub div opp inv Fdec Hf); assumption.
  Qed.

  Lemma Esum_cons_mle : forall (T : list F -> F) ds s (x : list F),
    mle m (Esum base (T :: ds) s) x = nF (base ^ s) * mle m T x + mle m (Esum base ds (S s)) x.
  Proof.
    intros T ds s x.
    change (Esum base (T :: ds) s) with (fun bq => nF (base ^ s) * T bq + Esum base ds (S s) bq).
    rewrite (@mle_add F zero one add mul sub div opp inv Hf m (fun bq => nF (base ^ s) * T bq) (Esum base ds (S s)) x).
    rewrite (@mle_scale F zero one add mul sub div opp inv Hf). reflexivity.
  Qed.

  Lemma dig_val : forall k s, gtval (digD s k) = pp * mle m (Esum base (map digT (seq s k)) s) ptD.
  Proof.
    induction k as [| k ih]; intro s.
    + unfold digD. cbn [seq map concat SlotKinds.gtval].
      change (Esum base [] s) with (fun _ : list F => zero).
      rewrite (@mle_const F zero one add mul sub div opp inv Hf m zero ptD HptD). field.
    + unfold digD. cbn [seq map concat]. fold (digD (S s) k).
      rewrite (@gtval_app F zero one add mul sub div opp inv Hf), tab1D, ih, Esum_cons_mle.
      unfold digT. field.
  Qed.

  (* sum_(x,i) eq((x,i), ptD) (u_i * s)_x  is  <s, w_s> *)
  Lemma us_val : mle m UsT ptD = dot (P rS) wsv.
  Proof.
    set (x1 := firstn n1 ptD). set (x2 := skipn n1 ptD).
    assert (hx1 : length x1 = n1) by (unfold x1; rewrite length_firstn; lia).
    rewrite (dot_row rS wsv).
    2:{ unfold wsv. apply lincomb_length. intro i.
        eapply Nat.le_trans; [apply nadj_length_le | rewrite eqvec_length; apply le_n]. }
    fold stabT. change (map (fun x => stabT (pt n1 x)) (seq 0 N)) with sKv.
    unfold wsv. fold x1 x2. rewrite dot_lincomb.
    transitivity (mle m UsT (x1 ++ x2)); [unfold x1, x2; rewrite firstn_skipn; reflexivity |].
    rewrite (@mle_concat F zero one add mul sub div opp inv Hf n1 ell UsT x1 x2 hx1).
    rewrite (@mle_seq F zero one add mul sub div opp inv Hf).
    transitivity (fsum (map (fun x => fsum (map (fun i =>
                     eqp (pt ell i) x2 * (nth x (nmul (us i) sKv) zero * eqp (pt n1 x) x1)) (seq 0 tau))) (seq 0 N))).
    { apply (@fsum_map_ext F zero add). intros x hx. apply in_seq in hx.
      rewrite (@mle_seq F zero one add mul sub div opp inv Hf).
      transitivity (eqp (pt n1 x) x1 * fsum (map (fun i => UsT (pt n1 x ++ pt ell i) * eqp (pt ell i) x2) (seq 0 tau)));
        [field |].
      rewrite <-(@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
      apply (@fsum_map_ext F zero add). intros i hi. apply in_seq in hi.
      unfold UsT. rewrite firstn_pt_app, skipn_pt_app.
      rewrite (@bidx_pt F zero one add mul sub div opp inv Fdec Hf n1 x ltac:(lia)),
              (@bidx_pt F zero one add mul sub div opp inv Fdec Hf ell i ltac:(lia)). field. }
    rewrite (@fsum_swap F zero one add mul sub div opp inv Hf).
    apply (@fsum_map_ext F zero add). intros i _.
    rewrite (@fsum_map_mul_l F zero one add mul sub div opp inv Hf).
    rewrite (adj_sum (us i) x1 sKv sK_length). reflexivity.
  Qed.

  (* Public side minus the value of claim D is the extension of the
     defect table of (D) at ptD. *)
  Theorem claimD : VDv - gtval clD = mle m DtabT ptD.
  Proof.
    unfold clD. rewrite gS_val, dig_val. fold dtsT. rewrite <-us_val.
    unfold DtabT, VDv.
    rewrite (@mle_sub F zero one add mul sub div opp inv Hf m (fun bq => TsT bq - UsT bq)
               (fun bq => pp * (Esum base dtsT 0 bq - offB)) ptD).
    rewrite (@mle_sub F zero one add mul sub div opp inv Hf m TsT UsT ptD).
    rewrite (@mle_scale F zero one add mul sub div opp inv Hf m pp (fun bq => Esum base dtsT 0 bq - offB) ptD).
    rewrite (@mle_sub F zero one add mul sub div opp inv Hf m (Esum base dtsT 0) (fun _ => offB) ptD).
    rewrite (@mle_const F zero one add mul sub div opp inv Hf m offB ptD HptD). field.
  Qed.

  (* The same for (K) at theta2. *)
  Theorem claimK : VKv - gtval clK = mle n1 KtabT th2.
  Proof.
    unfold clK. rewrite gS_val, gE_val. cbn [SlotKinds.gtval].
    rewrite (dot_row rS wav) by (unfold wav; eapply Nat.le_trans; [apply nadj_length_le | rewrite eqvec_length; apply le_n]).
    fold stabT. change (map (fun x => stabT (pt n1 x)) (seq 0 N)) with sKv.
    unfold wav. rewrite (adj_sum a th2 sKv sK_length).
    unfold VKv, RowLayout.eqvec.
    rewrite !(@dot_seq0 F zero one add mul sub div opp inv Hf).
    rewrite (@mle_seq F zero one add mul sub div opp inv Hf).
    transitivity (fsum (map (fun x => nth x b zero * eqp (pt n1 x) th2
                                      - nth x (nmul a sKv) zero * eqp (pt n1 x) th2
                                      - pp * (nth x (P rE) zero * eqp (pt n1 x) th2)) (seq 0 N))).
    + rewrite !(@fsum_map_sub F zero one add mul sub div opp inv Hf),
              (@fsum_map_mul_l F zero one add mul sub div opp inv Hf). field.
    + apply (@fsum_map_ext F zero add). intros x hx. apply in_seq in hx.
      rewrite HK_T by lia. unfold DecSound.Kcoef, DecSound.eK.
      rewrite nth_map_seqF by lia. unfold etabT. rewrite rowT_pt by lia. field.
  Qed.

  Lemma clZ_val : forall d, gtval (clZ d) = mstar m (digT d) (ment tg PmD d) rz.
  Proof.
    intro d. unfold clZ. rewrite (@gtval_app F zero one add mul sub div opp inv Hf), tab2D, gM_val.
    rewrite (@dot_unitv F zero one add mul sub div opp inv Hf). cbn [SlotKinds.gtval].
    unfold MaskedExt.mstar, digT. field.
  Qed.

  Lemma evG : forall k s,
    map gtval (map clZ (seq s k)) = evalsOf m (map digT (seq s k)) (map (ment tg PmD) (seq s k)) rz.
  Proof.
    induction k as [| k ih]; intro s; [reflexivity |].
    cbn [seq map ZeroTest.evalsOf]. rewrite clZ_val, ih. reflexivity.
  Qed.

  Theorem layout_identityD :
    map gtval claimsD =
    [gtval clD; gtval clK] ++ evalsOf m dtsT avG rz ++ evalsOf n1 [stabT; etabT] avT rt
    ++ [gmask a0GT csGT rz; gmask a0TT csTT rt].
  Proof.
    unfold claimsD. cbn [map app]. rewrite map_app, evG. fold dtsT avG.
    assert (eS : gtval clS = mstar n1 stabT (ment tg PmD kd) rt).
    { unfold clS. rewrite gS_val, gM_val, row_mle, (@dot_unitv F zero one add mul sub div opp inv Hf).
      cbn [SlotKinds.gtval]. unfold MaskedExt.mstar, stabT. field. }
    assert (eE : gtval clE = mstar n1 etabT (ment tg PmD (kd + 1)%nat) rt).
    { unfold clE. rewrite gE_val, gM_val, row_mle, (@dot_unitv F zero one add mul sub div opp inv Hf).
      cbn [SlotKinds.gtval]. unfold MaskedExt.mstar, etabT. field. }
    assert (eG : gtval clGm = gmask a0GT csGT rz).
    { unfold clGm. rewrite gM_val.
      rewrite <-(@mask_row_gmask F zero one add mul sub div opp inv Hf tg PmD offG dG rz ltac:(lia)).
      cbn [SlotKinds.gtval]. unfold a0GT, csGT. field. }
    assert (eT : gtval clTm = gmask a0TT csTT rt).
    { unfold clTm. rewrite gM_val.
      rewrite <-(@mask_row_gmask F zero one add mul sub div opp inv Hf tg PmD offT dT rt ltac:(lia)).
      cbn [SlotKinds.gtval]. unfold a0TT, csTT. field. }
    cbn [map]. rewrite eS, eE, eG, eT. unfold avT. cbn [ZeroTest.evalsOf app]. reflexivity.
  Qed.

End DecLayout.
