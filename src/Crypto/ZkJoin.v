(* Zero knowledge, joining the pieces (paper, Theorem 5.3).

   1. zk_join: composition of two simulations in which the second part of
      the prover's randomness is mapped to free values by a bijection that
      may depend on the first part (the joint map is triangular). The
      simulator of the second part may use the free values of the first.
      This is how the sumcheck layer and the opening compose: the mask table
      is randomness of the layer and, at the same time, data of a committed
      row.

   2. The opening of both matrices at once, over a subfield (Section
      Open2). Data rows and their pads have entries in a field K (Z_q in
      the implementation), embedded in F by a ring morphism emb; the masked
      vectors, their masks and the shifts have entries in F. There is one
      value mu for all masked vectors of both matrices, as in
      pcs_open_verify.

      Honest prover, on coins (pads_B, pads_S, masks_B, masks_S):
        mu      = sum over all masked vectors of <mask, L>
        zs      = mask + shift                      (both matrices)
        ys      = the entries of the data rows in the opened columns (in K)
        mrows   = the masks encoded at the opened columns (in F).
      Simulator, on coins (ys_B, ys_S, zs_B, zs_S):
        mu      = sum <zs, L> - cv
        mrows   = enc(zs) at J minus the shift at J, computed from ys.
      Hypotheses Hmu and HshB, HshS are the verifier's check equations for
      true claims.

      open2_zk: the lists of honest and of simulated transcripts over all
      coins are permutations of each other.

      A mask over F is two rows over K in the implementation, and both are
      opened; their entries are the coordinates of the F-entries shown
      here, a fixed bijection, which does not change the statement. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks ZkSumcheck ZkOpen ZkTranscript ZkOpenTranscript.
Import ListNotations.

(* ---------------------------------------------------------------------- *)
(* 1. composition *)

Lemma in_prod_split : forall {A B : Type} (la : list A) (lb : list B) p, In p (list_prod la lb) <-> In (fst p) la /\ In (snd p) lb.
Proof. intros A B la lb [x y]. apply in_prod_iff. Qed.

Theorem zk_join : forall {R1 V1 T1 R2 V2 T2 : Type}
  (f1 : R1 -> V1) (hon1 : R1 -> T1) (sim1 : V1 -> T1) (R1l : list R1) (V1l : list V1)
  (f2 : R1 -> R2 -> V2) (hon2 : R1 -> R2 -> T2) (sim2 : V1 -> V2 -> T2) (R2l : list R2) (V2l : list V2),
  NoDup R1l -> NoDup V1l -> NoDup R2l -> NoDup V2l ->
  (forall x, In x R1l -> In (f1 x) V1l) ->
  (forall x x', In x R1l -> In x' R1l -> f1 x = f1 x' -> x = x') ->
  (forall v, In v V1l -> exists x, In x R1l /\ f1 x = v) ->
  (forall x, In x R1l -> hon1 x = sim1 (f1 x)) ->
  (forall x y, In x R1l -> In y R2l -> In (f2 x y) V2l) ->
  (forall x y y', In x R1l -> In y R2l -> In y' R2l -> f2 x y = f2 x y' -> y = y') ->
  (forall x w, In x R1l -> In w V2l -> exists y, In y R2l /\ f2 x y = w) ->
  (forall x y, In x R1l -> In y R2l -> hon2 x y = sim2 (f1 x) (f2 x y)) ->
  Permutation (map (fun p => (hon1 (fst p), hon2 (fst p) (snd p))) (list_prod R1l R2l))
              (map (fun v => (sim1 (fst v), sim2 (fst v) (snd v))) (list_prod V1l V2l)).
Proof.
  intros R1 V1 T1 R2 V2 T2 f1 hon1 sim1 R1l V1l f2 hon2 sim2 R2l V2l n1 m1 n2 m2 i1 j1 s1 e1 i2 j2 s2 e2.
  apply (zk_perm (fun p => (f1 (fst p), f2 (fst p) (snd p)))); try (apply NoDup_list_prod; assumption).
  + intros [x y] h. apply in_prod_iff in h. destruct h as [hx hy]. apply in_prod_iff. cbn. split; auto.
  + intros [x y] [x' y'] h h' e. apply in_prod_iff in h, h'. cbn in e. injection e as ex ey.
    assert (x = x') by (apply j1; tauto). subst x'. f_equal. apply (j2 x); tauto.
  + intros [v w] h. apply in_prod_iff in h. destruct h as [hv hw].
    destruct (s1 v hv) as (x & hx & <-). destruct (s2 x w hx hw) as (y & hy & <-).
    exists (x, y). split; [apply in_prod_iff; tauto | reflexivity].
  + intros [x y] h. apply in_prod_iff in h. cbn. rewrite e1, e2 by tauto. reflexivity.
Qed.

(* a bijective re-encoding of the transcripts keeps the permutation *)
Lemma zk_post : forall {T U : Type} (g : T -> U) (l l' : list T), Permutation l l' -> Permutation (map g l) (map g l').
Proof. intros. apply Permutation_map. assumption. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. the opening of two matrices over a subfield *)

Section Open2.

  Context
    {K : Type} {kzero kone : K} {kadd kmul ksub kdiv : K -> K -> K} {kopp kinv : K -> K}
    {Kdec : forall x y : K, {x = y} + {x <> y}}
    {HK : @field K (@eq K) kzero kone kopp kadd ksub kmul kinv kdiv}.
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field fieldF : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation padd := (@padd F add).
  Local Notation vsub := (@vsub F sub).
  Local Notation lensK := (@lens K).
  Local Notation lensF := (@lens F).
  Local Notation openedK := (@opened K kzero kone kadd kmul).
  Local Notation pwK := (@pw K kone kmul).

  Variable emb : K -> F.

  Variable lK : list K.
  Hypothesis HndK : NoDup lK.
  Hypothesis HallK : forall x, In x lK.
  Variable lF : list F.
  Hypothesis HndF : NoDup lF.
  Hypothesis HallF : forall x, In x lF.

  (* the two matrices: evaluation points, code length, opened columns *)
  Variables omB omS : K.
  Variables nB nS : nat.
  Hypothesis HnodesB : forall i j, (i < nB)%nat -> (j < nB)%nat -> pwK omB i = pwK omB j -> i = j.
  Hypothesis HnodesS : forall i j, (i < nS)%nat -> (j < nS)%nat -> pwK omS i = pwK omS j -> i = j.
  Hypothesis HomB : omB <> kzero.
  Hypothesis HomS : omS <> kzero.
  Variables JB JS : list nat.
  Hypothesis HJBnd : NoDup JB.
  Hypothesis HJSnd : NoDup JS.
  Hypothesis HJB : forall j, In j JB -> (j < nB)%nat.
  Hypothesis HJS : forall j, In j JS -> (j < nS)%nat.

  (* a vector over F encoded at the opened columns, with the evaluation point mapped into F *)
  Local Notation encB := (@encJ F zero one add mul (emb omB) JB).
  Local Notation encS := (@encJ F zero one add mul (emb omS) JS).

  Variables datasB datasS : list (list K).
  Variables kkB nmB kkS nmS : nat.
  Variable tfunB tfunS : list (list K) -> list (list F).
  Hypothesis HtlenB : forall p, length (tfunB p) = nmB.
  Hypothesis HtlenS : forall p, length (tfunS p) = nmS.
  Hypothesis HtkB : forall p, Forall (fun t => (length t <= kkB)%nat) (tfunB p).
  Hypothesis HtkS : forall p, Forall (fun t => (length t <= kkS)%nat) (tfunS p).

  Variables LsB LsS : list (list F).
  Variable cv : F.
  Variables shJB shJS : list (list K) -> list (list F).

  Definition shapedP (datas : list (list K)) (J : list nat) (p : list (list K)) : Prop :=
    length p = length datas /\ lensK (length J) p.
  Definition shapedM (kk nm : nat) (ms : list (list F)) : Prop := length ms = nm /\ lensF kk ms.

  Hypothesis Hmu : forall pB pS, shapedP datasB JB pB -> shapedP datasS JS pS ->
    fsum (zipw dot (tfunB pB) LsB) + fsum (zipw dot (tfunS pS) LsS) = cv.
  Hypothesis HshB : forall pB, shapedP datasB JB pB ->
    map encB (tfunB pB) = shJB (zipw (fun d p => openedK omB d p JB) datasB pB).
  Hypothesis HshS : forall pS, shapedP datasS JS pS ->
    map encS (tfunS pS) = shJS (zipw (fun d p => openedK omS d p JS) datasS pS).

  (* coins and views have the same shape: (K-lists, K-lists, F-lists, F-lists) *)
  Definition o2 : Type := (list (list K) * list (list K) * (list (list F) * list (list F)))%type.

  Definition shaped_o2 (x : o2) : Prop :=
    shapedP datasB JB (fst (fst x)) /\ shapedP datasS JS (snd (fst x))
    /\ shapedM kkB nmB (fst (snd x)) /\ shapedM kkS nmS (snd (snd x)).

  Definition oview2 (x : o2) : o2 :=
    let '(pB, pS, (mB, mS)) := x in
    (zipw (fun d p => openedK omB d p JB) datasB pB, zipw (fun d p => openedK omS d p JS) datasS pS,
     (zipw padd mB (tfunB pB), zipw padd mS (tfunS pS))).

  Definition otr2 : Type :=
    (F * (list (list F) * list (list F)) * (list (list K) * list (list K)) * (list (list F) * list (list F)))%type.

  Definition honO2 (x : o2) : otr2 :=
    let '(pB, pS, (mB, mS)) := x in
    (fsum (zipw dot mB LsB) + fsum (zipw dot mS LsS),
     (zipw padd mB (tfunB pB), zipw padd mS (tfunS pS)),
     (zipw (fun d p => openedK omB d p JB) datasB pB, zipw (fun d p => openedK omS d p JS) datasS pS),
     (map encB mB, map encS mS)).

  Definition simO2 (v : o2) : otr2 :=
    let '(yB, yS, (zB, zS)) := v in
    (fsum (zipw dot zB LsB) + fsum (zipw dot zS LsS) - cv,
     (zB, zS), (yB, yS),
     (zipw vsub (map encB zB) (shJB yB), zipw vsub (map encS zS) (shJS yS))).

  Theorem open2_honest_sim : forall x, shaped_o2 x -> honO2 x = simO2 (oview2 x).
  Proof.
    intros [[pB pS] [mB mS]] ((h1 & h2) & (h3 & h4) & (h5 & h6) & (h7 & h8)). cbn [fst snd] in *.
    unfold honO2, simO2, oview2.
    assert (lB : length mB = length (tfunB pB)) by (rewrite HtlenB; exact h5).
    assert (lS : length mS = length (tfunS pS)) by (rewrite HtlenS; exact h7).
    rewrite (mu_split mB (tfunB pB) LsB lB), (mu_split mS (tfunS pS) LsS lS).
    rewrite <-(HshB pB (conj h1 h2)), <-(HshS pS (conj h3 h4)).
    rewrite (masks_open (emb omB) JB mB (tfunB pB) lB), (masks_open (emb omS) JS mS (tfunS pS) lS).
    pose proof (Hmu pB pS (conj h1 h2) (conj h3 h4)) as e.
    f_equal. f_equal. f_equal. rewrite <-e. field.
  Qed.

  Lemma padd_lens2 : forall kk (ms ts : list (list F)), lensF kk ms -> Forall (fun t => (length t <= kk)%nat) ts ->
    lensF kk (zipw padd ms ts).
  Proof.
    intros kk; induction ms as [| m0 ms ih]; intros ts hm ht; destruct ts as [| t ts]; cbn [zipw]; try constructor.
    + inversion hm; inversion ht; subst. rewrite (@length_padd F add). lia.
    + inversion hm; inversion ht; subst. apply ih; assumption.
  Qed.

  (* bijection *)
  Lemma oview2_shaped : forall x, shaped_o2 x -> shaped_o2 (oview2 x).
  Proof.
    intros [[pB pS] [mB mS]] ((h1 & h2) & (h3 & h4) & (h5 & h6) & (h7 & h8)). cbn [fst snd] in *.
    unfold shaped_o2, oview2, shapedP, shapedM. cbn [fst snd]. repeat split.
    + rewrite zipw_length by lia. reflexivity.
    + apply zipw_Forall. intros d p. unfold ReedSolomon.opened. apply length_map.
    + rewrite zipw_length by lia. reflexivity.
    + apply zipw_Forall. intros d p. unfold ReedSolomon.opened. apply length_map.
    + rewrite zipw_length by (rewrite HtlenB; exact h5). exact h5.
    + apply padd_lens2; [exact h6 | apply HtkB].
    + rewrite zipw_length by (rewrite HtlenS; exact h7). exact h7.
    + apply padd_lens2; [exact h8 | apply HtkS].
  Qed.

  Theorem oview2_inj : forall x x', shaped_o2 x -> shaped_o2 x' -> oview2 x = oview2 x' -> x = x'.
  Proof.
    intros [[pB pS] [mB mS]] [[pB' pS'] [mB' mS']]
      ((h1 & h2) & (h3 & h4) & (h5 & h6) & (h7 & h8)) ((h1' & h2') & (h3' & h4') & (h5' & h6') & (h7' & h8')) e.
    cbn [fst snd] in *. unfold oview2 in e. injection e as eyB eyS ezB ezS.
    assert (pB = pB') by (exact (@rows_inj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK omB nB HnodesB HomB JB HJBnd HJB
                                   datasB pB pB' h1 h1' h2 h2' eyB)).
    assert (pS = pS') by (exact (@rows_inj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK omS nS HnodesS HomS JS HJSnd HJS
                                   datasS pS pS' h3 h3' h4 h4' eyS)).
    subst pB' pS'. f_equal. f_equal.
    + apply (@masks_inj F zero one add mul sub div opp inv Hf (tfunB pB) mB mB' kkB); try assumption; rewrite HtlenB; assumption.
    + apply (@masks_inj F zero one add mul sub div opp inv Hf (tfunS pS) mS mS' kkS); try assumption; rewrite HtlenS; assumption.
  Qed.

  Theorem oview2_surj : forall v, shaped_o2 v -> exists x, shaped_o2 x /\ oview2 x = v.
  Proof.
    intros [[yB yS] [zB zS]] ((h1 & h2) & (h3 & h4) & (h5 & h6) & (h7 & h8)). cbn [fst snd] in *.
    destruct (@rows_surj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK lK HndK HallK omB nB HnodesB HomB JB HJBnd HJB
                datasB yB h1 h2) as (pB & a1 & a2 & a3).
    destruct (@rows_surj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK lK HndK HallK omS nS HnodesS HomS JS HJSnd HJS
                datasS yS h3 h4) as (pS & b1 & b2 & b3).
    destruct (@masks_surj F zero one add mul sub div opp inv Hf (tfunB pB) zB kkB ltac:(rewrite HtlenB; exact h5) h6 (HtkB pB))
      as (mB & c1 & c2 & c3).
    destruct (@masks_surj F zero one add mul sub div opp inv Hf (tfunS pS) zS kkS ltac:(rewrite HtlenS; exact h7) h8 (HtkS pS))
      as (mS & d1 & d2 & d3).
    exists (pB, pS, (mB, mS)). split.
    + unfold shaped_o2, shapedP, shapedM. cbn [fst snd]. rewrite HtlenB in c1. rewrite HtlenS in d1. tauto.
    + unfold oview2. rewrite a3, b3, c3, d3. reflexivity.
  Qed.

  (* all coins of the right shape *)
  Definition O2L : list o2 :=
    list_prod (list_prod (@all_shaped K lK (repeat (length JB) (length datasB))) (@all_shaped K lK (repeat (length JS) (length datasS))))
              (list_prod (@all_shaped F lF (repeat kkB nmB)) (@all_shaped F lF (repeat kkS nmS))).

  Lemma O2L_In : forall x, In x O2L <-> shaped_o2 x.
  Proof.
    intros [[pB pS] [mB mS]]. unfold O2L, shaped_o2, shapedP, shapedM. cbn [fst snd].
    split.
    - intro h. apply in_prod_iff in h. destruct h as [h1 h2]. apply in_prod_iff in h1, h2. destruct h1 as [a b], h2 as [c d].
      apply (@all_shaped_In K lK HallK) in a, b. apply (@all_shaped_In F lF HallF) in c, d.
      apply shaped_repeat in a, b, c, d. tauto.
    - intros ((a1 & a2) & (b1 & b2) & (c1 & c2) & (d1 & d2)). apply in_prod_iff. split; apply in_prod_iff; split.
      + apply (@all_shaped_In K lK HallK), shaped_repeat. tauto.
      + apply (@all_shaped_In K lK HallK), shaped_repeat. tauto.
      + apply (@all_shaped_In F lF HallF), shaped_repeat. tauto.
      + apply (@all_shaped_In F lF HallF), shaped_repeat. tauto.
  Qed.

  Lemma O2L_NoDup : NoDup O2L.
  Proof.
    unfold O2L. repeat apply NoDup_list_prod; first [apply (@all_shaped_NoDup K lK HndK) | apply (@all_shaped_NoDup F lF HndF)].
  Qed.

  (* Theorem 5.3 for the opening of both matrices *)
  Theorem open2_zk : Permutation (map honO2 O2L) (map simO2 O2L).
  Proof.
    apply (zk_perm oview2 honO2 simO2 O2L O2L O2L_NoDup O2L_NoDup).
    + intros x hx. apply O2L_In. apply oview2_shaped. apply O2L_In. exact hx.
    + intros x x' hx hx' e. apply O2L_In in hx. apply O2L_In in hx'. exact (oview2_inj x x' hx hx' e).
    + intros v hv. apply O2L_In in hv. destruct (oview2_surj v hv) as (x & hx & e).
      exists x. split; [apply O2L_In; exact hx | exact e].
    + intros x hx. apply open2_honest_sim. apply O2L_In. exact hx.
  Qed.

End Open2.

(* ---------------------------------------------------------------------- *)
(* 3. the opening of pcs_open_verify: per matrix, slot vectors and one proximity vector *)

(* As Open2, with one more masked vector per matrix: the proximity vector. Its shift is a function of
   the pads plus a function G of the masks of the slot vectors of the same matrix (the proximity
   combination includes the rows that hold those masks). The map stays a bijection (triangular: the
   proximity mask is solved last), and the simulator recomputes G at the opened columns from the
   slot masks it has already computed there (hypotheses HGB, HGS). *)

Section OpenMix.

  Context
    {K : Type} {kzero kone : K} {kadd kmul ksub kdiv : K -> K -> K} {kopp kinv : K -> K}
    {Kdec : forall x y : K, {x = y} + {x <> y}}
    {HK : @field K (@eq K) kzero kone kopp kadd ksub kmul kinv kdiv}.
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field fieldF3 : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation padd := (@padd F add).
  Local Notation vadd := (@vadd F add).
  Local Notation vsub := (@vsub F sub).
  Local Notation lensK := (@lens K).
  Local Notation lensF := (@lens F).
  Local Notation openedK := (@opened K kzero kone kadd kmul).
  Local Notation pwK := (@pw K kone kmul).

  Variable emb : K -> F.
  Variable lK : list K.
  Hypothesis HndK : NoDup lK.
  Hypothesis HallK : forall x, In x lK.
  Variable lF : list F.
  Hypothesis HndF : NoDup lF.
  Hypothesis HallF : forall x, In x lF.

  Variables omB omS : K.
  Variables nB nS : nat.
  Hypothesis HnodesB : forall i j, (i < nB)%nat -> (j < nB)%nat -> pwK omB i = pwK omB j -> i = j.
  Hypothesis HnodesS : forall i j, (i < nS)%nat -> (j < nS)%nat -> pwK omS i = pwK omS j -> i = j.
  Hypothesis HomB : omB <> kzero.
  Hypothesis HomS : omS <> kzero.
  Variables JB JS : list nat.
  Hypothesis HJBnd : NoDup JB.
  Hypothesis HJSnd : NoDup JS.
  Hypothesis HJB : forall j, In j JB -> (j < nB)%nat.
  Hypothesis HJS : forall j, In j JS -> (j < nS)%nat.

  Local Notation encB := (@encJ F zero one add mul (emb omB) JB).
  Local Notation encS := (@encJ F zero one add mul (emb omS) JS).

  Variables datasB datasS : list (list K).
  Variables kkB nmB kpB kkS nmS kpS : nat.
  Variables tfunB tfunS : list (list K) -> list (list F).        (* shifts of the slot vectors *)
  Variables tpB tpS : list (list K) -> list F.                   (* shift of the proximity vector, data part *)
  Variables GB GS : list (list F) -> list F.                     (* its part from the slot masks *)
  Hypothesis HtlenB : forall p, length (tfunB p) = nmB.
  Hypothesis HtlenS : forall p, length (tfunS p) = nmS.
  Hypothesis HtkB : forall p, shapedP datasB JB p -> Forall (fun t => (length t <= kkB)%nat) (tfunB p).
  Hypothesis HtkS : forall p, shapedP datasS JS p -> Forall (fun t => (length t <= kkS)%nat) (tfunS p).
  Hypothesis HtpB : forall p, shapedP datasB JB p -> (length (tpB p) <= kpB)%nat.
  Hypothesis HtpS : forall p, shapedP datasS JS p -> (length (tpS p) <= kpS)%nat.
  Hypothesis HGlB : forall ms, shapedM kkB nmB ms -> (length (GB ms) <= kpB)%nat.
  Hypothesis HGlS : forall ms, shapedM kkS nmS ms -> (length (GS ms) <= kpS)%nat.

  Variables LsB LsS : list (list F).
  Variable cv : F.
  Variables shJB shJS : list (list K) -> list (list F).
  Variables shpB shpS : list (list K) -> list F.
  Variables GhB GhS : list (list F) -> list F.

  Local Notation ysOf := (fun om J datas p => zipw (fun d q => openedK om d q J) datas p).

  Hypothesis Hmu : forall pB pS, shapedP datasB JB pB -> shapedP datasS JS pS ->
    fsum (zipw dot (tfunB pB) LsB) + fsum (zipw dot (tfunS pS) LsS) = cv.
  Hypothesis HshB : forall pB, shapedP datasB JB pB -> map encB (tfunB pB) = shJB (ysOf omB JB datasB pB).
  Hypothesis HshS : forall pS, shapedP datasS JS pS -> map encS (tfunS pS) = shJS (ysOf omS JS datasS pS).
  Hypothesis HspB : forall pB, shapedP datasB JB pB -> encB (tpB pB) = shpB (ysOf omB JB datasB pB).
  Hypothesis HspS : forall pS, shapedP datasS JS pS -> encS (tpS pS) = shpS (ysOf omS JS datasS pS).
  Hypothesis HGB : forall ms, shapedM kkB nmB ms -> encB (GB ms) = GhB (map encB ms).
  Hypothesis HGS : forall ms, shapedM kkS nmS ms -> encS (GS ms) = GhS (map encS ms).

  Definition o3 : Type := (list (list K) * list (list K) * ((list (list F) * list F) * (list (list F) * list F)))%type.

  Definition shaped_o3 (x : o3) : Prop :=
    let '(pB, pS, ((mB, qB), (mS, qS))) := x in
    shapedP datasB JB pB /\ shapedP datasS JS pS /\ shapedM kkB nmB mB /\ length qB = kpB
    /\ shapedM kkS nmS mS /\ length qS = kpS.

  Definition oview3 (x : o3) : o3 :=
    let '(pB, pS, ((mB, qB), (mS, qS))) := x in
    (ysOf omB JB datasB pB, ysOf omS JS datasS pS,
     ((zipw padd mB (tfunB pB), padd qB (padd (tpB pB) (GB mB))),
      (zipw padd mS (tfunS pS), padd qS (padd (tpS pS) (GS mS))))).

  Definition otr3 : Type :=
    (F * ((list (list F) * list F) * (list (list F) * list F)) * (list (list K) * list (list K))
       * ((list (list F) * list F) * (list (list F) * list F)))%type.

  Definition honO3 (x : o3) : otr3 :=
    let '(pB, pS, ((mB, qB), (mS, qS))) := x in
    (fsum (zipw dot mB LsB) + fsum (zipw dot mS LsS),
     ((zipw padd mB (tfunB pB), padd qB (padd (tpB pB) (GB mB))),
      (zipw padd mS (tfunS pS), padd qS (padd (tpS pS) (GS mS)))),
     (ysOf omB JB datasB pB, ysOf omS JS datasS pS),
     ((map encB mB, encB qB), (map encS mS, encS qS))).

  Definition simO3 (v : o3) : otr3 :=
    let '(yB, yS, ((zB, zqB), (zS, zqS))) := v in
    let mrB := zipw vsub (map encB zB) (shJB yB) in
    let mrS := zipw vsub (map encS zS) (shJS yS) in
    (fsum (zipw dot zB LsB) + fsum (zipw dot zS LsS) - cv,
     ((zB, zqB), (zS, zqS)), (yB, yS),
     ((mrB, vsub (encB zqB) (vadd (shpB yB) (GhB mrB))),
      (mrS, vsub (encS zqS) (vadd (shpS yS) (GhS mrS))))).

  Lemma vadd_length_eq : forall x y : list F, length x = length y -> length (vadd x y) = length x.
  Proof.
    induction x as [| a x ih]; intros y h; destruct y as [| b y]; cbn in h; try lia; [reflexivity |].
    cbn. rewrite ih by lia. reflexivity.
  Qed.

  Theorem open3_honest_sim : forall x, shaped_o3 x -> honO3 x = simO3 (oview3 x).
  Proof.
    intros [[pB pS] [[mB qB] [mS qS]]] ((h1 & h2) & (h3 & h4) & (h5 & h6) & h7 & (h8 & h9) & h10).
    unfold honO3, simO3, oview3. cbv zeta.
    assert (lB : length mB = length (tfunB pB)) by (rewrite HtlenB; exact h5).
    assert (lS : length mS = length (tfunS pS)) by (rewrite HtlenS; exact h8).
    rewrite (mu_split mB (tfunB pB) LsB lB), (mu_split mS (tfunS pS) LsS lS).
    rewrite <-(HshB pB (conj h1 h2)), <-(HshS pS (conj h3 h4)).
    rewrite (masks_open (emb omB) JB mB (tfunB pB) lB), (masks_open (emb omS) JS mS (tfunS pS) lS).
    rewrite <-(HspB pB (conj h1 h2)), <-(HspS pS (conj h3 h4)), <-(HGB mB (conj h5 h6)), <-(HGS mS (conj h8 h9)).
    rewrite !encJ_padd.
    rewrite (vsub_vadd (encB qB)) by (rewrite !encJ_length; rewrite vadd_length_eq by (rewrite !encJ_length; reflexivity);
                                      rewrite encJ_length; reflexivity).
    rewrite (vsub_vadd (encS qS)) by (rewrite !encJ_length; rewrite vadd_length_eq by (rewrite !encJ_length; reflexivity);
                                      rewrite encJ_length; reflexivity).
    pose proof (Hmu pB pS (conj h1 h2) (conj h3 h4)) as e.
    f_equal. f_equal. f_equal. rewrite <-e. field.
  Qed.

  Lemma oview3_shaped : forall x, shaped_o3 x -> shaped_o3 (oview3 x).
  Proof.
    intros [[pB pS] [[mB qB] [mS qS]]] ((h1 & h2) & (h3 & h4) & (h5 & h6) & h7 & (h8 & h9) & h10).
    unfold shaped_o3, oview3, shapedP, shapedM. repeat split.
    + rewrite zipw_length by lia. reflexivity.
    + apply zipw_Forall. intros d p. unfold ReedSolomon.opened. apply length_map.
    + rewrite zipw_length by lia. reflexivity.
    + apply zipw_Forall. intros d p. unfold ReedSolomon.opened. apply length_map.
    + rewrite zipw_length by (rewrite HtlenB; exact h5). exact h5.
    + apply padd_lens2; [exact h6 | apply HtkB; split; assumption].
    + rewrite !(@length_padd F add). pose proof (HtpB pB (conj h1 h2)). pose proof (HGlB mB (conj h5 h6)). lia.
    + rewrite zipw_length by (rewrite HtlenS; exact h8). exact h8.
    + apply padd_lens2; [exact h9 | apply HtkS; split; assumption].
    + rewrite !(@length_padd F add). pose proof (HtpS pS (conj h3 h4)). pose proof (HGlS mS (conj h8 h9)). lia.
  Qed.

  Theorem oview3_inj : forall x x', shaped_o3 x -> shaped_o3 x' -> oview3 x = oview3 x' -> x = x'.
  Proof.
    intros [[pB pS] [[mB qB] [mS qS]]] [[pB' pS'] [[mB' qB'] [mS' qS']]]
      ((h1 & h2) & (h3 & h4) & (h5 & h6) & h7 & (h8 & h9) & h10)
      ((h1' & h2') & (h3' & h4') & (h5' & h6') & h7' & (h8' & h9') & h10') e.
    unfold oview3 in e. injection e as eyB eyS ezB eqB ezS eqS.
    assert (pB = pB') by (exact (@rows_inj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK omB nB HnodesB HomB JB HJBnd HJB
                                   datasB pB pB' h1 h1' h2 h2' eyB)).
    assert (pS = pS') by (exact (@rows_inj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK omS nS HnodesS HomS JS HJSnd HJS
                                   datasS pS pS' h3 h3' h4 h4' eyS)).
    subst pB' pS'.
    assert (mB = mB') by (apply (@masks_inj F zero one add mul sub div opp inv Hf (tfunB pB) mB mB' kkB); try assumption;
                          rewrite HtlenB; assumption).
    assert (mS = mS') by (apply (@masks_inj F zero one add mul sub div opp inv Hf (tfunS pS) mS mS' kkS); try assumption;
                          rewrite HtlenS; assumption).
    subst mB' mS'.
    assert (qB = qB') by (apply (@shift_list_inj F zero one add mul sub div opp inv Hf (padd (tpB pB) (GB mB)) qB qB'); [lia | exact eqB]).
    assert (qS = qS') by (apply (@shift_list_inj F zero one add mul sub div opp inv Hf (padd (tpS pS) (GS mS)) qS qS'); [lia | exact eqS]).
    subst. reflexivity.
  Qed.

  Theorem oview3_surj : forall v, shaped_o3 v -> exists x, shaped_o3 x /\ oview3 x = v.
  Proof.
    intros [[yB yS] [[zB zqB] [zS zqS]]] ((h1 & h2) & (h3 & h4) & (h5 & h6) & h7 & (h8 & h9) & h10).
    destruct (@rows_surj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK lK HndK HallK omB nB HnodesB HomB JB HJBnd HJB
                datasB yB h1 h2) as (pB & a1 & a2 & a3).
    destruct (@rows_surj K kzero kone kadd kmul ksub kdiv kopp kinv Kdec HK lK HndK HallK omS nS HnodesS HomS JS HJSnd HJS
                datasS yS h3 h4) as (pS & b1 & b2 & b3).
    destruct (@masks_surj F zero one add mul sub div opp inv Hf (tfunB pB) zB kkB ltac:(rewrite HtlenB; exact h5) h6
                (HtkB pB (conj a1 a2))) as (mB & c1 & c2 & c3).
    destruct (@masks_surj F zero one add mul sub div opp inv Hf (tfunS pS) zS kkS ltac:(rewrite HtlenS; exact h8) h9
                (HtkS pS (conj b1 b2))) as (mS & d1 & d2 & d3).
    rewrite HtlenB in c1. rewrite HtlenS in d1.
    destruct (@shift_list_surj F zero one add mul sub div opp inv Hf (padd (tpB pB) (GB mB)) zqB
                ltac:(rewrite (@length_padd F add); pose proof (HtpB pB (conj a1 a2)); pose proof (HGlB mB (conj c1 c2)); lia))
      as (qB & e1 & e2).
    destruct (@shift_list_surj F zero one add mul sub div opp inv Hf (padd (tpS pS) (GS mS)) zqS
                ltac:(rewrite (@length_padd F add); pose proof (HtpS pS (conj b1 b2)); pose proof (HGlS mS (conj d1 d2)); lia))
      as (qS & f1 & f2).
    exists (pB, pS, ((mB, qB), (mS, qS))). split.
    + unfold shaped_o3, shapedP, shapedM. repeat split; try assumption; lia.
    + unfold oview3. rewrite a3, b3, c3, d3, e2, f2. reflexivity.
  Qed.

  Definition O3L : list o3 :=
    list_prod (list_prod (@all_shaped K lK (repeat (length JB) (length datasB))) (@all_shaped K lK (repeat (length JS) (length datasS))))
              (list_prod (list_prod (@all_shaped F lF (repeat kkB nmB)) (all_lists lF kpB))
                         (list_prod (@all_shaped F lF (repeat kkS nmS)) (all_lists lF kpS))).

  Lemma O3L_In : forall x, In x O3L <-> shaped_o3 x.
  Proof.
    intros [[pB pS] [[mB qB] [mS qS]]]. unfold O3L, shaped_o3, shapedP, shapedM. split.
    - intro h. apply in_prod_iff in h. destruct h as [h1 h2]. apply in_prod_iff in h1, h2.
      destruct h1 as [a b], h2 as [c d]. apply in_prod_iff in c, d. destruct c as [c1 c2], d as [d1 d2].
      apply (@all_shaped_In K lK HallK) in a, b. apply (@all_shaped_In F lF HallF) in c1, d1.
      apply all_lists_In in c2, d2. apply shaped_repeat in a, b, c1, d1. tauto.
    - intros ((a1 & a2) & (b1 & b2) & (c1 & c2) & c3 & (d1 & d2) & d3). apply in_prod_iff.
      split; apply in_prod_iff; split; try (apply in_prod_iff; split).
      + apply (@all_shaped_In K lK HallK), shaped_repeat. tauto.
      + apply (@all_shaped_In K lK HallK), shaped_repeat. tauto.
      + apply (@all_shaped_In F lF HallF), shaped_repeat. tauto.
      + apply all_lists_In. split; [exact c3 | apply Forall_forall; intros; apply HallF].
      + apply (@all_shaped_In F lF HallF), shaped_repeat. tauto.
      + apply all_lists_In. split; [exact d3 | apply Forall_forall; intros; apply HallF].
  Qed.

  Lemma O3L_NoDup : NoDup O3L.
  Proof.
    unfold O3L. repeat apply NoDup_list_prod;
      first [apply (@all_shaped_NoDup K lK HndK) | apply (@all_shaped_NoDup F lF HndF) | apply all_lists_NoDup; exact HndF].
  Qed.

  (* Theorem 5.3 for the opening of pcs_open_verify *)
  Theorem open3_zk : Permutation (map honO3 O3L) (map simO3 O3L).
  Proof.
    apply (zk_perm oview3 honO3 simO3 O3L O3L O3L_NoDup O3L_NoDup).
    + intros x hx. apply O3L_In. apply oview3_shaped. apply O3L_In. exact hx.
    + intros x x' hx hx' e. apply O3L_In in hx. apply O3L_In in hx'. exact (oview3_inj x x' hx hx' e).
    + intros v hv. apply O3L_In in hv. destruct (oview3_surj v hv) as (x & hx & e).
      exists x. split; [apply O3L_In; exact hx | exact e].
    + intros x hx. apply open3_honest_sim. apply O3L_In. exact hx.
  Qed.

  (* the pieces of open3_zk, for the composition with the layer (zk_join) *)
  Theorem open3_parts : NoDup O3L
    /\ (forall x, In x O3L -> In (oview3 x) O3L)
    /\ (forall x x', In x O3L -> In x' O3L -> oview3 x = oview3 x' -> x = x')
    /\ (forall v, In v O3L -> exists x, In x O3L /\ oview3 x = v)
    /\ (forall x, In x O3L -> honO3 x = simO3 (oview3 x)).
  Proof.
    split; [exact O3L_NoDup |]. split; [| split; [| split]].
    + intros x hx. apply O3L_In. apply oview3_shaped. apply O3L_In. exact hx.
    + intros x x' hx hx' e. apply O3L_In in hx. apply O3L_In in hx'. exact (oview3_inj x x' hx hx' e).
    + intros v hv. apply O3L_In in hv. destruct (oview3_surj v hv) as (x & hx & e).
      exists x. split; [apply O3L_In; exact hx | exact e].
    + intros x hx. apply open3_honest_sim. apply O3L_In. exact hx.
  Qed.

End OpenMix.
