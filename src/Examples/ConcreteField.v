(* The concrete field of the implementation (fp_core.py):

     q  = 2^78 + 100663297 = 302231454903657394339841      (prime)
     Zq = Z/qZ
     Fq2 = Zq[t]/(t^2 - 3) = GF(q^2)

   - Q_prime: q is prime, by a Pocklington certificate checked by
     computation (CoqPrime). q - 1 = 2^25 * 5 * 7 * 11 * 1187 * 19709623201.
   - Zq is the field Zpfield.Zp of Utility/Zpstar.v at q.
   - three_nonres: 3 is not a square in Zq (Euler's criterion:
     3^((q-1)/2) = -1 mod q, by computation, and Fermat's little theorem).
   - Section QuadExt: for any field K with decidable equality and any
     non-square nr, K x K with (a,b)(c,d) = (ac + nr bd, ad + bc) is a field
     (ext_field). The formulas are those of fmul and finv in fp_core.py.
   - Fq2 with its field instance Fq2_field: the hypothesis Hf of every
     theorem of this development can be discharged for the real field. *)

From Stdlib Require Import Utf8 ZArith Zpow_facts Znumtheory List Lia setoid_ring.Field Morphisms.
From Coqprime Require Import PocklingtonCertificat.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Utility Require Import Fermat Zpstar.
From Crypto Require Import LogDer Counting.
Import ListNotations.

(* ---------------------------------------------------------------------- *)
(* q is prime *)

Definition Q : Z := 302231454903657394339841.

Lemma Q_value : Q = (2 ^ 78 + 100663297)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma Q_prime : prime Q.
Proof.
  apply (Pocklington_refl
           (Pock_certif 302231454903657394339841 6
              ((1187, 1) :: (11, 1) :: (7, 1) :: (5, 1) :: (2, 25) :: nil)%positive 1)
           (Pock_certif 1187 2 ((593, 1) :: (2, 1) :: nil)%positive 1
            :: Pock_certif 593 3 ((2, 4) :: nil)%positive 4
            :: Pock_certif 11 2 ((2, 1) :: nil)%positive 1
            :: Pock_certif 7 3 ((2, 1) :: nil)%positive 1
            :: Pock_certif 5 2 ((2, 2) :: nil)%positive 1
            :: Proof_certif 2 prime_2 :: nil)).
  vm_cast_no_check (eq_refl true).
Qed.

(* ---------------------------------------------------------------------- *)
(* Zq *)

Definition Zq : Type := @Zpfield.Zp Q.
Definition qzero : Zq := @Zpfield.zero Q Q_prime.
Definition qone : Zq := @Zpfield.one Q Q_prime.
Definition qadd : Zq -> Zq -> Zq := @Zpfield.zp_add Q.
Definition qsub : Zq -> Zq -> Zq := @Zpfield.zp_sub Q.
Definition qmul : Zq -> Zq -> Zq := @Zpfield.zp_mul Q.
Definition qopp : Zq -> Zq := @Zpfield.zp_opp Q Q_prime.
Definition qinv : Zq -> Zq := @Zpfield.zp_inv Q.
Definition qdiv : Zq -> Zq -> Zq := @Zpfield.zp_div Q.

Definition Zq_field : @field Zq (@eq Zq) qzero qone qopp qadd qsub qmul qinv qdiv :=
  @Zpfield.zp_field Q Q_prime.

Definition Zq_dec : forall x y : Zq, {x = y} + {x <> y} := @Zpfield.zp_dec Q.

Definition qthree : Zq := @Zpfield.mk_zp Q 3 eq_refl.

(* 3 is not a square mod q *)
Theorem three_nonres : forall x : Zq, qmul x x <> qthree.
Proof.
  intros [vx Hvx] e.
  apply (f_equal (@Zpfield.v Q)) in e. cbn [qmul Zpfield.zp_mul Zpfield.v qthree] in e.
  assert (hq : (0 < Q)%Z) by (vm_compute; reflexivity).
  pose proof (Z.mod_pos_bound vx Q hq) as hb. rewrite Hvx in hb.
  assert (hx : (vx <> 0)%Z).
  { intro h0. subst vx. vm_compute in e. discriminate. }
  assert (hne : (Q <> 0)%Z) by (intro h; vm_compute in h; discriminate).
  assert (hr : (0 < vx < Q)%Z) by lia.
  clear hb hx Hvx.
  pose proof (fermat_little_ZZ vx Q Q_prime hr) as hf.
  rewrite (Zpow_mod_correct vx (Q - 1) Q hne) in hf.
  assert (hh : (Q - 1 = 2 * 151115727451828697169920)%Z) by (vm_compute; reflexivity).
  rewrite hh in hf.
  rewrite (Z.pow_mul_r vx 2 151115727451828697169920) in hf;
    [| vm_compute; discriminate | vm_compute; discriminate].
  rewrite (Z.pow_2_r vx) in hf.
  rewrite (Zpower_mod (vx * vx) 151115727451828697169920 Q hq) in hf.
  rewrite e in hf.
  rewrite <-(Zpow_mod_correct 3 151115727451828697169920 Q hne) in hf.
  vm_compute in hf. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* Quadratic extension of a field by a non-square *)

Section QuadExt.

  Context
    {K : Type} {zero one : K} {add mul sub div : K -> K -> K} {opp inv : K -> K}
    {Kdec : forall x y : K, {x = y} + {x <> y}}
    {Hk : @field K (@eq K) zero one opp add sub mul inv div}.

  Add Field fieldK : (@field_theory_for_stdlib_tactic K eq zero one opp add mul sub inv div Hk).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.

  Variable nr : K.
  Hypothesis Hnr : forall x : K, x * x <> nr.

  Definition E : Type := (K * K)%type.
  Definition ezero : E := (zero, zero).
  Definition eone : E := (one, zero).
  Definition egen : E := (zero, one).              (* t, with t * t = nr *)
  Definition eadd (x y : E) : E := (fst x + fst y, snd x + snd y).
  Definition esub (x y : E) : E := (fst x - fst y, snd x - snd y).
  Definition eopp (x : E) : E := (opp (fst x), opp (snd x)).
  Definition emul (x y : E) : E :=
    (fst x * fst y + nr * snd x * snd y, fst x * snd y + snd x * fst y).
  Definition enorm (x : E) : K := fst x * fst x - nr * snd x * snd x.
  Definition einv (x : E) : E := (fst x * inv (enorm x), opp (snd x) * inv (enorm x)).
  Definition ediv (x y : E) : E := emul x (einv y).

  Definition E_dec : forall x y : E, {x = y} + {x <> y}.
  Proof. intros x y. decide equality; apply Kdec. Defined.

  Lemma enorm_nonzero : forall x : E, x <> ezero -> enorm x <> zero.
  Proof.
    intros [a b] hne e. unfold enorm in e. cbn [fst snd] in e.
    destruct (Kdec b zero) as [hb | hb].
    + subst b. destruct (Kdec a zero) as [ha | ha]; [subst a; apply hne; reflexivity |].
      apply (@mul_nonzero K zero one add mul sub div opp inv Hk a a ha ha).
      transitivity (a * a - nr * zero * zero); [field | exact e].
    + apply (Hnr (a * inv b)).
      transitivity ((a * a - nr * b * b) * (inv b * inv b) + nr); [field; exact hb |].
      rewrite e. field. exact hb.
  Qed.

  Lemma egen_square : emul egen egen = (nr, zero).
  Proof. unfold emul, egen. cbn [fst snd]. f_equal; field. Qed.

  Ltac ext_solve :=
    repeat match goal with x : E |- _ => destruct x end;
    unfold eadd, esub, eopp, emul, ediv, einv, enorm, ezero, eone; cbn [fst snd]; f_equal; field.

  Global Instance ext_field : @field E (@eq E) ezero eone eopp eadd esub emul einv ediv.
  Proof.
    repeat constructor; repeat intro; subst; try reflexivity; try (ext_solve; fail).
    + (* left inverse *)
      match goal with H : _ <> ezero |- _ => pose proof (enorm_nonzero _ H) as hn end.
      match goal with x : E |- _ => destruct x as [a b] end.
      unfold emul, einv, enorm, eone in *. cbn [fst snd] in *. f_equal; field; exact hn.
    + (* zero <> one *)
      match goal with H : ezero = eone |- _ => injection H as h end.
      exact (@zero_neq_one K eq zero one _ h).
  Qed.

End QuadExt.

(* ---------------------------------------------------------------------- *)
(* GF(q^2) *)

Definition Fq2 : Type := @E Zq.
Definition fzero : Fq2 := @ezero Zq qzero.
Definition fone : Fq2 := @eone Zq qzero qone.
Definition ftg : Fq2 := @egen Zq qzero qone.
Definition fadd : Fq2 -> Fq2 -> Fq2 := @eadd Zq qadd.
Definition fsub : Fq2 -> Fq2 -> Fq2 := @esub Zq qsub.
Definition fopp : Fq2 -> Fq2 := @eopp Zq qopp.
Definition fmul : Fq2 -> Fq2 -> Fq2 := @emul Zq qadd qmul qthree.
Definition finv : Fq2 -> Fq2 := @einv Zq qmul qsub qopp qinv qthree.
Definition fdiv : Fq2 -> Fq2 -> Fq2 := @ediv Zq qadd qmul qsub qopp qinv qthree.

Definition Fq2_field : @field Fq2 (@eq Fq2) fzero fone fopp fadd fsub fmul finv fdiv :=
  @ext_field Zq qzero qone qadd qmul qsub qdiv qopp qinv Zq_dec Zq_field qthree three_nonres.

Definition Fq2_dec : forall x y : Fq2, {x = y} + {x <> y} := @E_dec Zq Zq_dec.

(* ---------------------------------------------------------------------- *)
(* Characteristic, and the list of all elements *)

Lemma Q_pos : (0 < Q)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma zq_eq : forall x y : Zq, @Zpfield.v Q x = @Zpfield.v Q y -> x = y.
Proof.
  intros [vx hx] [vy hy] e. cbn in e. subst vy. f_equal.
  apply Eqdep_dec.UIP_dec. apply Z.eq_dec.
Qed.

Definition zq_of (z : Z) : Zq := @Zpfield.mk_zp Q (z mod Q) (Zmod_mod z Q).

Lemma zq_bound : forall x : Zq, (0 <= @Zpfield.v Q x < Q)%Z.
Proof.
  intros [vx hx]. cbn. rewrite <-hx. apply Z.mod_pos_bound. exact Q_pos.
Qed.

Local Notation nF2 := (@nF Fq2 fzero fone fadd).

Lemma nF2_value : forall k : nat,
  @Zpfield.v Q (fst (nF2 k)) = (Z.of_nat k mod Q)%Z /\ snd (nF2 k) = qzero.
Proof.
  induction k as [| k [ih1 ih2]].
  + split; reflexivity.
  + change (nF2 (S k)) with (fadd fone (nF2 k)).
    destruct (nF2 k) as [[vx hx] y]. cbn [fst snd] in ih1, ih2. subst y. cbn [Zpfield.v] in ih1.
    split.
    - cbn [fadd eadd fone eone fst snd qadd qone Zpfield.zp_add Zpfield.one Zpfield.v].
      rewrite ih1, Zplus_mod_idemp_r. f_equal. lia.
    - apply zq_eq. reflexivity.
Qed.

(* the characteristic is q *)
Theorem Fq2_char : forall k : nat, (0 < Z.of_nat k < Q)%Z -> nF2 k <> fzero.
Proof.
  intros k hk e. destruct (nF2_value k) as [h _]. rewrite e in h.
  cbn [fzero ezero fst qzero Zpfield.zero Zpfield.v] in h.
  rewrite Z.mod_small in h by lia. lia.
Qed.

Theorem Fq2_two : fadd fone fone <> fzero.
Proof.
  intro e. apply (f_equal (fun x => @Zpfield.v Q (fst x))) in e. vm_compute in e. discriminate.
Qed.

Definition lq : list Zq := map (fun i => zq_of (Z.of_nat i)) (seq 0 (Z.to_nat Q)).

Lemma lq_all : forall x : Zq, In x lq.
Proof.
  intro x. pose proof (zq_bound x) as hb. unfold lq. apply in_map_iff.
  exists (Z.to_nat (@Zpfield.v Q x)). split.
  + apply zq_eq. cbn [zq_of Zpfield.v]. rewrite Z2Nat.id by lia. apply Z.mod_small. exact hb.
  + apply in_seq. split; [lia |]. cbn [Nat.add]. apply Z2Nat.inj_lt; lia.
Qed.

Lemma NoDup_map_on : forall {R V : Type} (f : R -> V) (l : list R), NoDup l ->
  (forall x x', In x l -> In x' l -> f x = f x' -> x = x') -> NoDup (map f l).
Proof.
  intros R V f l h; induction h as [| x l hx h ih]; intro hinj; cbn; constructor.
  + intro hin. apply in_map_iff in hin. destruct hin as (x' & e & hx').
    assert (x' = x) by (apply hinj; [right; exact hx' | left; reflexivity | exact e]). subst x'. contradiction.
  + apply ih. intros a a' ha ha'. apply hinj; right; assumption.
Qed.

Lemma lq_NoDup : NoDup lq.
Proof.
  unfold lq. apply NoDup_map_on; [apply seq_NoDup |].
  intros i j hi hj e. apply in_seq in hi. apply in_seq in hj.
  apply (f_equal (@Zpfield.v Q)) in e. cbn [zq_of Zpfield.v] in e.
  pose proof Q_pos as hq.
  assert (hi' : (0 <= Z.of_nat i < Q)%Z) by (split; [lia |]; apply Z2Nat.inj_lt; [lia | lia | rewrite Nat2Z.id; lia]).
  assert (hj' : (0 <= Z.of_nat j < Q)%Z) by (split; [lia |]; apply Z2Nat.inj_lt; [lia | lia | rewrite Nat2Z.id; lia]).
  rewrite !Z.mod_small in e by assumption. lia.
Qed.

Definition lf2 : list Fq2 := list_prod lq lq.

Lemma lf2_all : forall x : Fq2, In x lf2.
Proof. intros [x y]. apply in_prod; apply lq_all. Qed.

Lemma lf2_NoDup : NoDup lf2.
Proof. apply NoDup_list_prod; apply lq_NoDup. Qed.
