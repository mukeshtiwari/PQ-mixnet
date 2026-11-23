(* Completeness of the decryption proof: the extracted decryption verifier accepts what the extracted
   decryption prover outputs, for a valid witness and any coins (ExecDecProve.v: xdec_prove; ExecDec.v:
   xdec_verify_bytes). The structure follows the shuffle proof (ExecComplete.v):

   - step A, dparse_ser: the verifier's parser reads back what the prover's serialiser writes;
   - step C, dprove_transcript: the verifier's front end replays the prover's challenges;
   - step D, dscG, dscT, dderive: both sumchecks pass; the digit range sum is zero for any noise (digits
     are reduced mod base), the ternary sum needs ternary s, e;
   - step E, dlayout, dopen_complete: on the honest rows the claims have the derived values (the defect
     tables of (D) and (K) vanish: t = s u + p E, b = a s + p e, and the digits recombine to E + off when
     (E + off) mod q < base^kd), and the opening checks pass;
   - step B, dwf: the output has the shapes the parser and the opening need;
   - xdec_complete: the theorem. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String Permutation setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots Counting LogDer Mle Negacyclic Sumcheck SumcheckMask MaskedExt CubeIndex RowLayout SlotKinds Opening ZeroTest DecSound DecLayout NttInverse.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecMerkle ExecProveBase ExecSerial ExecFold ExecFront ExecShape ExecRows ExecDec ExecDecProve.
From Examples Require ExecBackD ExecBackO ExecNtt.
Import ListNotations.

(* ---------------------------------------------------------------------- *)
(* step A: the byte format *)

Section DParse.

  Variables n1 ell lo1 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat).

  Local Notation SO := (SOX n1 ell lo1 kd).

  Definition wf_dparts (P : dparts) : Prop :=
    List.length (proot_big P) = 32%nat /\ List.length (proot_small P) = 32%nat
    /\ List.length (pG P) = 2%nat /\ Forall reduced (pG P)
    /\ Forall2 msg_ok (pmG P) (dGX n1 ell base) /\ List.length (pzG P) = kd /\ Forall reduced (pzG P)
    /\ Forall2 msg_ok (pmT P) (dTX n1) /\ List.length (pzT P) = 2%nat /\ Forall reduced (pzT P) /\ reduced (pmu P)
    /\ msg_ok (pvS1 P) kB /\ msg_ok (pvS2 P) kB /\ msg_ok (pvSe P) kS /\ msg_ok (pvSm P) kS /\ msg_ok (pvSs P) kS
    /\ msg_ok (ppvB P) kB /\ msg_ok (ppvS P) kS
    /\ cols_ok nqB [SO] (log2n 64 nB) (pcolsB P)
    /\ cols_ok nqS [11%nat] (log2n 64 nS) (pcolsS P).

  Theorem dparse_ser : forall P, wf_dparts P ->
    xdec_parse n1 ell lo1 kd base kB nB nqB kS nS nqS (ser_dparts P) = Some P.
  Proof.
    intros [rb rs G mG zG mT zT mu v1 v2 ve vm vs pvB pvS cB cS]
      (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h18 & h19 & h20).
    cbn [proot_big proot_small pG pmG pzG pmT pzT pmu pvS1 pvS2 pvSe pvSm pvSs ppvB ppvS pcolsB pcolsS] in *.
    destruct h12, h13, h14, h15, h16, h17, h18.
    unfold xdec_parse, ser_dparts.
    cbn [proot_big proot_small pG pmG pzG pmT pzT pmu pvS1 pvS2 pvSe pvSm pvSs ppvB ppvS pcolsB pcolsS].
    rewrite take_len by exact h1. cbn [bindo fst snd].
    rewrite take_len by exact h2. cbn [bindo fst snd].
    rewrite prep_fs by assumption. cbn [bindo fst snd].
    rewrite pmsgs_ser by assumption. cbn [bindo fst snd].
    rewrite prep_fs by assumption. cbn [bindo fst snd].
    rewrite pmsgs_ser by assumption. cbn [bindo fst snd].
    rewrite prep_fs by assumption. cbn [bindo fst snd].
    rewrite pf_ser by assumption. cbn [bindo fst snd].
    do 7 (rewrite prep_fs by assumption; cbn [bindo fst snd]).
    rewrite prep_cols by exact h19. cbn [bindo fst snd].
    rewrite <-(app_nil_r (flat_map (flat_map ser_item) cS)), prep_cols by exact h20. cbn [bindo fst snd].
    reflexivity.
  Qed.

End DParse.

(* ---------------------------------------------------------------------- *)
(* step C: the transcript *)

Record dtrace : Type := mk_dtrace {
  dt_th : list xf; dt_th1 : list xf; dt_th2 : list xf; dt_tz : list xf; dt_kG : list xf; dt_rhoG : list xf;
  dt_mG : list (list xf); dt_rz : list xf; dt_finG : list xf;
  dt_tt : list xf; dt_kT : list xf; dt_rhoT : list xf; dt_mT : list (list xf); dt_rt : list xf; dt_finT : list xf;
  dt_kp : list xf; dt_cl : list xf; dt_gB : list xf; dt_gS : list xf; dt_JB : list Z; dt_JS : list Z
}.

Local Notation "x <- o ;; f" := (bindo o (fun x => f)) (at level 61, o at next level, right associativity).

Section DTranscript.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k : dcoins.

  Local Notation m := (n1 + ell)%nat.
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation bBx := (btBD lo1 kd base nB omB off E k).
  Local Notation bSx := (btSD lo2 nS omS s e k).
  Local Notation GDx := (GD n1 ell kd base k).
  Local Notation gGx := (gGD n1 ell kd base k).
  Local Notation gTx := (gTD n1 ell kd base k).

  Definition f0T (T : dtrace) : dfront :=
    front0 (dt_th T) (dt_th1 T) (dt_th2 T) (dt_tz T) (dt_kG T ++ dt_rhoG T) (dt_rz T) (dt_tt T) (dt_kT T ++ dt_rhoT T)
           (dt_rt T) (dt_kp T) xzero [] [].
  Definition f1T (T : dtrace) : dfront :=
    front0 (dt_th T) (dt_th1 T) (dt_th2 T) (dt_tz T) (dt_kG T ++ dt_rhoG T) (dt_rz T) (dt_tt T) (dt_kT T ++ dt_rhoT T)
           (dt_rt T) (dt_kp T) (nth 0 (dt_cl T) xzero) (dt_gB T) (dt_gS T).

  Definition vecT (T : dtrace) (v : nat) : list xf := vecD n1 ell lo1 kd base pplain a us bBx bSx (f1T T) v.

  Definition dparts_of (T : dtrace) : dparts :=
    mk_dparts (broot bBx) (broot bSx) GDx (dt_mG T) (firstn kd (tl (dt_finG T))) (dt_mT T) (firstn 2 (tl (dt_finT T)))
              (muD n1 ell lo1 kd base pplain a us bBx bSx (f0T T))
              (vecT T 1) (vecT T 2) (vecT T 4) (vecT T 5) (vecT T 3)
              (pvBD n1 ell lo1 kd bBx bSx (f1T T)) (pvSD n1 ell lo1 kd bBx bSx (f1T T))
              (map (fun j => [bitem bBx j]) (map Z.to_nat (dt_JB T)))
              (map (fun j => [bitem bSx j]) (map Z.to_nat (dt_JS T))).

  (* the record the verifier's front end builds (ExecDec.v: xdec_front, last line) *)
  Definition dfmk (P : dparts) (T : dtrace) : dfront :=
    let JB := map Z.to_nat (dt_JB T) in
    let JS := map Z.to_nat (dt_JS T) in
    let colB := map (fun bs => flat_map (fun it => fst (fst it)) bs) (pcolsB P) in
    let colS := map (fun bs => flat_map (fun it => fst (fst it)) bs) (pcolsS P) in
    let Xe i j := if Nat.ltb i SO then bx (nth i (nth (idx_of JB j 0) colB []) 0%Z)
                  else bx (nth (i - SO) (nth (idx_of JS j 0) colS []) 0%Z) in
    let ub v := match v with 1 => pvS1 P | 2 => pvS2 P | 3 => pvSs P | 4 => pvSe P | _ => pvSm P end in
    mk_dfront (dt_th T) (dt_th1 T) (dt_th2 T) (dt_tz T) (dt_kG T ++ dt_rhoG T) (dt_rz T) (dt_tt T) (dt_kT T ++ dt_rhoT T)
              (dt_rt T) (nth 0 (pG P) xzero) (nth 1 (pG P) xzero) (pmG P) (pzG P) (pmT P) (pzT P) (dt_kp T)
              (nth 0 (dt_cl T) xzero) (firstn (kd * rw + 4) (dt_gB T)) (firstn 9 (dt_gS T)) JB JS (pmu P) ub
              (ppvB P) (ppvS P) Xe.

  (* the verifier's checks of the shapes of the components, before the transcript *)
  Definition dshape_front (P : dparts) : bool :=
    let allf := pG P ++ List.concat (pmG P) ++ pzG P ++ List.concat (pmT P) ++ pzT P ++ [pmu P] ++ pvS1 P ++ pvS2 P
                ++ pvSs P ++ pvSe P ++ pvSm P ++ ppvB P ++ ppvS P in
    forallb xred allf && Nat.eqb (List.length (pG P)) 2 && Nat.eqb (List.length (pzG P)) kd
    && Nat.eqb (List.length (pzT P)) 2
    && (if list_eq_dec Nat.eq_dec (map (@List.length xf) (pmG P)) (dGX n1 ell base) then true else false)
    && (if list_eq_dec Nat.eq_dec (map (@List.length xf) (pmT P)) (dTX n1) then true else false).

  Definition ddrawn (T : dtrace) : Prop :=
    let dF (nm : string) (n : nat) (x : list xf) := exists c c', get_F c (sb nm) n = Some (x, c') in
    let dI (nm : string) (n : nat) (bd : Z) (x : list Z) := exists c c', get_I c (sb nm) n bd = Some (x, c') in
    dF "theta"%string ell (dt_th T) /\ dF "theta1"%string n1 (dt_th1 T) /\ dF "theta2"%string n1 (dt_th2 T)
    /\ dF "tz"%string m (dt_tz T) /\ dF "kG"%string kd (dt_kG T) /\ dF "rhoG"%string 1%nat (dt_rhoG T)
    /\ dF "tt"%string n1 (dt_tt T) /\ dF "kT"%string 2%nat (dt_kT T) /\ dF "rhoT"%string 1%nat (dt_rhoT T)
    /\ dF "pcs.kappa"%string (kd + 6)%nat (dt_kp T) /\ dF "pcs.c"%string 1%nat (dt_cl T)
    /\ dF "pcs.gamma.big"%string (kd * rw + 6)%nat (dt_gB T) /\ dF "pcs.gamma.small"%string 11%nat (dt_gS T)
    /\ dI "pcs.J.big"%string nqB (Z.of_nat nB) (dt_JB T) /\ dI "pcs.J.small"%string nqS (Z.of_nat nS) (dt_JS T).

  Definition dptrans (P : dparts) (T : dtrace) : Prop :=
    P = dparts_of T /\ ddrawn T
    /\ xnz (nth 0 (dt_rhoG T) xzero) = true /\ xnz (nth 0 (dt_rhoT T) xzero) = true
    /\ (exists c0 c1, sc_loop (fun c nm => get_F c nm 1) "G" (tmaskG kd k) (termsG kd base (dt_kG T)) (fst gGx) (snd gGx)
                        (nth 0 (dt_rhoG T) xzero) (dGX n1 ell base) 0 (tablesG kd base off E (dt_tz T)) [] c0
                      = Some (dt_mG T, dt_rz T, dt_finG T, c1))
    /\ (exists c0 c1, sc_loop (fun c nm => get_F c nm 1) "T" (tmaskT kd k) (termsT (dt_kT T)) (fst gTx) (snd gTx)
                        (nth 0 (dt_rhoT T) xzero) (dTX n1) 0 (tablesT s e (dt_tt T)) [] c0
                      = Some (dt_mT T, dt_rt T, dt_finT T, c1))
    /\ (dshape_front P = true ->
        xdec_front n1 ell lo1 kd base nB nqB nS nqS tag a b us ts (proot_big P) (proot_small P) (pG P) (pmG P) (pzG P)
                   (pmT P) (pzT P) (pmu P) (pvS1 P) (pvS2 P) (pvSs P) (pvSe P) (pvSm P) (ppvB P) (ppvS P)
                   (pcolsB P) (pcolsS P)
        = if negb (merkle_ok [proot_big P] (map Z.to_nat (dt_JB T)) (pcolsB P)
                   && merkle_ok [proot_small P] (map Z.to_nat (dt_JS T)) (pcolsS P)) then None
          else Some (dfmk P T)).

  Ltac use_eq e :=
    match type of e with
    | ?g ?x ?y ?z = ?v =>
        match goal with |- context [g ?x' ?y' ?z'] => replace (g x' y' z') with v by (rewrite <-e; reflexivity) end
    | ?g ?x ?y ?z ?w = ?v =>
        match goal with |- context [g ?x' ?y' ?z' ?w'] => replace (g x' y' z' w') with v by (rewrite <-e; reflexivity) end
    end.
  Ltac stepF H f x c e :=
    match type of H with
    | context [bindo (f ?ch ?nm ?n) _] =>
        destruct (f ch nm n) as [[x c] |] eqn:e; [| rewrite bindo_none in H; discriminate H];
        rewrite bindo_some in H; cbv beta in H; rewrite ?fst_pair, ?snd_pair in H
    end.
  Ltac stepI H f x c e :=
    match type of H with
    | context [bindo (f ?ch ?nm ?n ?bd) _] =>
        destruct (f ch nm n bd) as [[x c] |] eqn:e; [| rewrite bindo_none in H; discriminate H];
        rewrite bindo_some in H; cbv beta in H; rewrite ?fst_pair, ?snd_pair in H
    end.
  Ltac stepS H m r fin c e :=
    match type of H with
    | context [bindo (xsc_proveG ?d ?nm ?t ?tm ?te ?ds ?a0 ?cs ?rho ?ch) _] =>
        destruct (xsc_proveG d nm t tm te ds a0 cs rho ch) as [[[[m r] fin] c] |] eqn:e;
          [| rewrite bindo_none in H; discriminate H];
        rewrite bindo_some in H; cbv beta iota in H; rewrite ?fst_pair, ?snd_pair in H
    end.
  Ltac stepIf H e :=
    match type of H with
    | context [if negb ?bb then None else _] => destruct bb eqn:e; cbn [negb] in H; cbv beta iota in H; [| discriminate H]
    end.

  Theorem dprove_transcript : forall P,
    xdec_prove_partsG n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS tag pplain off a b us ts s e E k get_F get_I = Some P ->
    exists T, dptrans P T.
  Proof.
    intros P H. unfold xdec_prove_partsG in H. cbv zeta in H.
    stepF H get_F th c1 e1. stepF H get_F th1 c2 e2. stepF H get_F th2 c3 e3. stepF H get_F tz c4 e4.
    stepF H get_F kG c5 e5. stepF H get_F rhoG c6 e6.
    stepIf H enG.
    stepS H mG rz finG cG eG.
    stepF H get_F ttv c7 e7. stepF H get_F kT c8 e8. stepF H get_F rhoT c9 e9.
    stepIf H enT.
    stepS H mT rt finT cT eT.
    stepF H get_F kp c10 e10. stepF H get_F cl c11 e11. stepF H get_F gBv c12 e12. stepF H get_F gSv c13 e13.
    stepI H get_I JB c14 e14. stepI H get_I JS c15 e15.
    apply (f_equal (fun o => match o with Some x => x | None => P end)) in H. cbv beta iota in H.
    exists (mk_dtrace th th1 th2 tz kG rhoG mG rz finG ttv kT rhoT mT rt finT kp cl gBv gSv JB JS).
    unfold xsc_proveG in eG, eT.
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eG) as (hG & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eT) as (hT & _).
    subst P.
    split; [reflexivity |].
    split; [unfold ddrawn; cbv zeta; repeat split; do 2 eexists; eassumption |].
    split; [exact enG |]. split; [exact enT |].
    split; [exists c6, cG; exact eG |]. split; [exists c9, cT; exact eT |].
    intro hsh. unfold xdec_front. unfold dshape_front in hsh. cbv zeta in hsh |- *.
    cbn [dparts_of proot_big proot_small pG pmG pzG pmT pzT pmu pvS1 pvS2 pvSe pvSm pvSs ppvB ppvS pcolsB pcolsS] in hsh |- *.
    rewrite hsh. cbn [negb]. unfold sc_chals, draw1.
    Ltac bs := rewrite bindo_some; cbv beta.
    use_eq e1; bs. use_eq e2; bs. use_eq e3; bs. use_eq e4; bs. use_eq e5; bs. use_eq e6; bs.
    use_eq hG; bs. use_eq e7; bs. use_eq e8; bs. use_eq e9; bs. use_eq hT; bs.
    use_eq e10; bs. use_eq e11; bs. use_eq e12; bs. use_eq e13; bs. use_eq e14; bs. use_eq e15; bs.
    reflexivity.
  Qed.

End DTranscript.

(* ---------------------------------------------------------------------- *)
(* step D, part 1: the expanded range terms *)

Add Field fieldF2dc : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation pevalF := (@PolyRoots.eval Fq2 fzero fadd fmul).
Local Notation pwF := (@Negacyclic.pw Fq2 fone fmul).
Local Notation fsumF := (@LogDer.fsum Fq2 fzero fadd).
Local Notation gmask2 := (@gmask Fq2 fzero fadd fmul).
Local Notation Zp2 := (@Zp Fq2 fone fmul fsub).

Lemma xrcoefs_length : forall k, List.length (xrcoefs k) = S k.
Proof.
  induction k as [| k ih]; [reflexivity |]. cbn [xrcoefs]. rewrite xpadd_length. unfold xpscale.
  cbn [List.length]. rewrite length_map, ih. lia.
Qed.

Lemma to_F_bx_xint : forall z, to_F (bx z) = to_F (xint z).
Proof. intro z. change (xint z) with (bx (zm z)). symmetry. apply to_F_bx_zm. Qed.

Lemma peval_rcoefs : forall k z, pevalF (map to_F (xrcoefs k)) (to_F z) = to_F (xrangep k z).
Proof.
  induction k as [| k ih]; intro z.
  - cbn. rewrite to_F_one. field.
  - cbn [xrcoefs xrangep]. rewrite to_F_padd, to_F_pscale.
    rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
            (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    cbn [map PolyRoots.eval]. rewrite ih, to_F_mul, to_F_sub, to_F_neg, to_F_zero. field.
Qed.

Lemma xrangep_root : forall k v, (v < k)%nat -> to_F (xrangep k (bx (Z.of_nat v))) = fzero.
Proof.
  induction k as [| k ih]; intros v hv; [lia |].
  cbn [xrangep]. rewrite to_F_mul, to_F_sub, to_F_bx_xint, !to_F_xint_nat.
  destruct (Nat.eq_dec v k) as [-> | hne]; [field |].
  rewrite ih by lia. field.
Qed.

Lemma fold_rep : forall (vals : list Fq2) i j c,
  fold_left (fun p i => fmul p (nth i vals fzero)) (repeat i j) c = fmul c (pwF (nth i vals fzero) j).
Proof.
  intros vals i j; induction j as [| j ih]; intro c; cbn [repeat fold_left Negacyclic.pw]; [field |].
  rewrite ih. field.
Qed.

Lemma termsG_val : forall kd base kG vals,
  termsF (map sF (termsG kd base kG)) vals
  = fmul (nth 0 vals fzero)
         (fsumF (map (fun d => fmul (to_F (nth d kG xzero)) (pevalF (map to_F (xrcoefs base)) (nth (S d) vals fzero)))
                     (seq 0 kd))).
Proof.
  intros kd base kG vals. unfold termsG, termsF. cbv zeta.
  rewrite flat_map_concat_map, !concat_map, ExecFold.fsum_concat, !map_map.
  rewrite <-(fsum_scale' (Hf := Fq2_field)).
  apply fsum_ext'. intros d _.
  rewrite !map_map. unfold termF, sF. cbn [fst snd].
  rewrite (eval_sum (Hf := Fq2_field)), length_map, xrcoefs_length.
  rewrite <-!(fsum_scale' (Hf := Fq2_field)).
  apply fsum_ext'. intros j _.
  cbn [fold_left]. rewrite fold_rep, to_F_mul, <-to_F_nth. field.
Qed.

(* ---------------------------------------------------------------------- *)
(* step D, part 2: the two sumchecks of the prover pass the verifier's round checks *)

Lemma nth_map_seq0 : forall {A : Type} (f : nat -> A) n i d, (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
Proof.
  intros A f n i d hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
  rewrite map_nth, seq_nth by exact hi. reflexivity.
Qed.

Lemma nth_map_dflt : forall {A B : Type} (f : A -> B) l n0 d0 db, f d0 = db -> nth n0 (map f l) db = f (nth n0 l d0).
Proof. intros A B f l n0 d0 db <-. apply map_nth. Qed.

Lemma dGX_len : forall n1 ell base, List.length (dGX n1 ell base) = (n1 + ell)%nat.
Proof. intros. unfold dGX. rewrite length_map, length_seq. reflexivity. Qed.
Lemma dTX_len : forall n1, List.length (dTX n1) = n1.
Proof. intros. unfold dTX. rewrite length_map, length_seq. reflexivity. Qed.
Lemma dGX_nth : forall n1 ell base i, (i < n1 + ell)%nat ->
  nth i (dGX n1 ell base) 0%nat = if Nat.eqb (S i) (n1 + ell) then (2 * base + 1)%nat else (base + 1)%nat.
Proof.
  intros n1 ell base i hi. unfold dGX. rewrite nth_map_seq0 by exact hi. reflexivity.
Qed.
Lemma dTX_nth : forall n1 i, (i < n1)%nat -> nth i (dTX n1) 0%nat = if Nat.eqb (S i) n1 then 7%nat else 4%nat.
Proof.
  intros n1 i hi. unfold dTX. rewrite nth_map_seq0 by exact hi. reflexivity.
Qed.

Lemma digit_range : forall base off d x, (1 <= base)%nat -> (0 <= digit base off d x < Z.of_nat base)%Z.
Proof. intros base off d x hb. unfold digit. apply Z.mod_pos_bound. lia. Qed.

Lemma Tdig_digit : forall base off E d i, (1 <= base)%nat ->
  exists v, (v < base)%nat /\ nth i (Tdig base off E d) 0%Z = Z.of_nat v.
Proof.
  intros base off E d i hb.
  destruct (Nat.lt_ge_cases i (List.length (Tdig base off E d))) as [hi | hi].
  - pose proof (nth_In _ 0%Z hi) as hin. set (x := nth i (Tdig base off E d) 0%Z) in *.
    unfold Tdig in hin. apply in_concat in hin.
    destruct hin as (l & hl & hx). apply in_map_iff in hl. destruct hl as (Ei & <- & _).
    apply in_map_iff in hx. destruct hx as (y & ey & _).
    destruct (digit_range base off d y hb) as [h0 h1].
    exists (Z.to_nat (digit base off d y)). split; [lia |]. rewrite <-ey. lia.
  - rewrite nth_overflow by exact hi. exists 0%nat. split; [lia | reflexivity].
Qed.

Lemma length_xfold_map : forall (tables : list (list xf)) r, List.length (map (fun t => xfold t r) tables) = List.length tables.
Proof. intros. apply length_map. Qed.

Lemma sc_loop_fin_len : forall draw name tmask terms a0 cs rho ds j tables point ch msgs pt fin ch',
  ds <> [] -> sc_loop draw name tmask terms a0 cs rho ds j tables point ch = Some (msgs, pt, fin, ch') ->
  List.length fin = Nat.min (List.length tables) (List.length tmask).
Proof.
  intros draw name tmask terms a0 cs rho. induction ds as [| d ds ih]; intros j tables point ch msgs pt fin ch' hne H;
    [contradiction |].
  cbn [sc_loop] in H.
  destruct (draw _ _) as [[rl chr] |] eqn:hg; [| discriminate].
  rewrite bindo_some in H. cbv beta in H.
  destruct ds as [| d' ds']; cbv beta iota zeta in H.
  - injection H as <- <- <- <-. unfold last_vals. rewrite length_map, length_combine. reflexivity.
  - destruct (sc_loop draw name tmask terms a0 cs rho (d' :: ds') (S j) _ _ (snd (rl, chr)))
      as [[[[ms pt0] fin0] ch0] |] eqn:hrec; [| discriminate].
    rewrite bindo_some in H. injection H as <- <- <- <-.
    rewrite (ih _ _ _ _ _ _ _ _ ltac:(discriminate) hrec), length_map. reflexivity.
Qed.

Lemma innerZ_seq : forall (phi : xf -> xf) ks zl, List.length zl = List.length ks ->
  to_F (xinnerZ phi ks zl)
  = fsumF (map (fun d => fmul (to_F (nth d ks xzero)) (to_F (phi (nth d zl xzero)))) (seq 0 (List.length ks))).
Proof.
  intros phi ks; induction ks as [| kx ks ih]; intros zl hl; [exact to_F_zero |].
  destruct zl as [| z zl]; [discriminate |]. cbn [List.length] in hl |- *.
  cbn [xinnerZ seq map LogDer.fsum nth]. rewrite to_F_add, to_F_mul, ih by lia.
  rewrite <-seq_shift, map_map. reflexivity.
Qed.

Section DSum.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k : dcoins.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation gGx := (gGD n1 ell kd base k).
  Local Notation gTx := (gTD n1 ell kd base k).
  Local Notation dG := (dGX n1 ell base).
  Local Notation dT := (dTX n1).

  Hypothesis Hn1 : (1 <= n1)%nat.
  Hypothesis Hbase : (1 <= base)%nat.
  Hypothesis Hdmax : (2 * base + 1 <= DMAX)%nat.
  Hypothesis HE : List.length E = tau /\ Forall (fun l => List.length l = N) E.
  Hypothesis Hs : List.length s = N.
  Hypothesis He : List.length e = N.
  Hypothesis Hmask : List.length (dmask k) = n_maskD n1 ell kd base.

  Lemma Tdig_len : forall d, List.length (Tdig base off E d) = (2 ^ m)%nat.
  Proof.
    intro d. unfold Tdig. destruct HE as [hl hf].
    rewrite (length_concat_uniform _ N), length_map, hl by
      (intros l hin; apply in_map_iff in hin; destruct hin as (Ei & <- & hEi); rewrite length_map;
       rewrite Forall_forall in hf; apply hf, hEi).
    rewrite Nat.pow_add_r. lia.
  Qed.

  Lemma a_dig_len : List.length (a_dig kd k) = kd.
  Proof. unfold a_dig. rewrite length_firstn, Hmask. unfold n_maskD. lia. Qed.

  Lemma gG_shape : List.length (snd gGx) = m
    /\ forall i, (i < m)%nat -> (List.length (nth i (snd gGx) []) <= nth i dG 0%nat)%nat.
  Proof.
    unfold gGD, mask_ofD. cbn [snd]. destruct (ExecBackD.cuts_shape dG (tl (skipn (kd + 2) (dmask k)))) as [h1 h2].
    rewrite dGX_len in h1, h2. split; [exact h1 | exact h2].
  Qed.

  Lemma gT_shape : List.length (snd gTx) = n1
    /\ forall i, (i < n1)%nat -> (List.length (nth i (snd gTx) []) <= nth i dT 0%nat)%nat.
  Proof.
    unfold gTD, mask_ofD. cbn [snd]. destruct (ExecBackD.cuts_shape dT (tl (skipn (kd + 3 + list_sum dG) (dmask k)))) as [h1 h2].
    rewrite dTX_len in h1, h2. split; [exact h1 | exact h2].
  Qed.

  (* the range sum is zero for any noise: every digit lies in [0, base) *)
  Lemma sumG_zero : forall tz kG, List.length tz = m ->
    csum (map sF (termsG kd base kG)) (tF (tablesG kd base off E tz)) (2 ^ m) = fzero.
  Proof.
    intros tz kG htz. unfold csum.
    rewrite (fsum_ext' _ (fun _ => fzero)), (fsum_const' (Hf := Fq2_field)); [field |].
    intros i _. rewrite termsG_val.
    rewrite (fsum_ext' _ (fun _ => fzero)), (fsum_const' (Hf := Fq2_field)); [field |].
    intros d hd. apply in_seq in hd.
    unfold colF, tF, tablesG.
    rewrite (nth_map_dflt (fun t : list Fq2 => nth i t fzero) _ (S d) [] fzero ltac:(destruct i; reflexivity)).
    rewrite (nth_map_dflt (map to_F) _ (S d) [] [] eq_refl). cbn [nth]. rewrite nth_map_seq0 by lia.
    rewrite (nth_map_dflt to_F _ i xzero fzero to_F_zero), (nth_map_dflt bx _ i 0%Z xzero eq_refl).
    destruct (Tdig_digit base off E d i Hbase) as (v & hv & ev). rewrite ev.
    rewrite peval_rcoefs, xrangep_root by exact hv. field.
  Qed.

  Definition ternZ (l : list Z) : Prop := Forall (fun x => zm x = 0%Z \/ zm x = 1%Z \/ zm x = (Q - 1)%Z) l.

  Lemma tern_val : forall l i, ternZ l ->
    let x := to_F (nth i (map bx (map zm l)) xzero) in fsub (fmul (fmul x x) x) x = fzero.
  Proof.
    intros l i hl x. unfold x. clear x.
    rewrite (nth_map_dflt bx _ i 0%Z xzero eq_refl).
    destruct (Nat.lt_ge_cases i (List.length l)) as [hi | hi].
    - rewrite (nth_map_dflt zm _ i 0%Z 0%Z eq_refl).
      unfold ternZ in hl. rewrite Forall_forall in hl. specialize (hl _ (nth_In l 0%Z hi)).
      destruct hl as [-> | [-> | ->]].
      + change (bx 0%Z) with (bz 0%Z). rewrite xfft_bz0. field.
      + change (bx 1%Z) with (bz 1%Z). rewrite xfft_to_F_bx1. field.
      + change (bx (Q - 1)%Z) with (bz (Q - 1)%Z). rewrite to_F_bz_Qm1. field.
    - rewrite nth_overflow by (rewrite length_map; exact hi). change (bx 0%Z) with (bz 0%Z). rewrite xfft_bz0. field.
  Qed.

  Lemma sumT_zero : forall tt kT, ternZ s -> ternZ e ->
    csum (map sF (termsT kT)) (tF (tablesT s e tt)) (2 ^ n1) = fzero.
  Proof.
    intros tt kT hs he. unfold csum.
    rewrite (fsum_ext' _ (fun _ => fzero)), (fsum_const' (Hf := Fq2_field)); [field |].
    intros i _. unfold termsT, termsF, termF, sF, colF, tF, tablesT, sZ, eZ.
    cbn [map fold_left fst snd LogDer.fsum nth].
    pose proof (tern_val s i hs) as h1. pose proof (tern_val e i he) as h2. cbv zeta in h1, h2.
    rewrite <-!to_F_nth in *. rewrite !to_F_neg.
    set (q0 := to_F (nth i (xeq_table tt) xzero)) in *.
    set (x1 := to_F (nth i (map bx (map zm s)) xzero)) in *.
    set (x2 := to_F (nth i (map bx (map zm e)) xzero)) in *.
    set (k0 := to_F (nth 0 kT xzero)). set (k1 := to_F (nth 1 kT xzero)).
    transitivity (fmul q0 (fadd (fmul k0 (fsub (fmul (fmul x1 x1) x1) x1)) (fmul k1 (fsub (fmul (fmul x2 x2) x2) x2)))); [field |].
    rewrite h1, h2. field.
  Qed.

  (* sumcheck G: the round checks pass, and the final values are the masked evaluations *)
  Theorem dscG : forall tz kG rhoG mG rz finG c0 c1,
    List.length tz = m -> List.length kG = kd -> List.length rhoG = 1%nat ->
    sc_loop (fun c nm => get_F c nm 1) "G" (tmaskG kd k) (termsG kd base kG) (fst gGx) (snd gGx)
            (nth 0 rhoG xzero) dG 0 (tablesG kd base off E tz) [] c0 = Some (mG, rz, finG, c1) ->
    exists clG,
      xsc_verify mG rz (xmul (xkk (kG ++ rhoG) kd) (nth 0 (GD n1 ell kd base k) xzero)) = Some clG
      /\ to_F clG = fadd (termsF (map sF (termsG kd base kG)) (map to_F finG))
                         (fmul (to_F (nth 0 rhoG xzero)) (gmask2 (to_F (fst gGx)) (csF (snd gGx)) (map to_F rz)))
      /\ List.length rz = m /\ Forall2 msg_ok mG dG
      /\ (forall j, (j < S kd)%nat ->
            to_F (nth j finG xzero)
            = fadd (to_F (xmle (nth j (tablesG kd base off E tz) []) rz)) (fmul (maskv (tmaskG kd k) j) (Zp2 (map to_F rz)))).
  Proof.
    intros tz kG rhoG mG rz finG c0 c1 htz hkG hrho hsc.
    destruct gG_shape as [hcsl hcsd].
    assert (hm : (1 <= m)%nat) by lia.
    assert (hclaim : to_F (xmul (xkk (kG ++ rhoG) kd) (nth 0 (GD n1 ell kd base k) xzero))
                     = fadd (csum (map sF (termsG kd base kG)) (tF (tablesG kd base off E tz)) (2 ^ List.length dG))
                            (fmul (to_F (nth 0 rhoG xzero)) (@tsum Fq2 fzero fone fadd (gmask2 (to_F (fst gGx)) (csF (snd gGx))) (map to_F []) (List.length dG)))).
    { rewrite dGX_len, sumG_zero by exact htz.
      unfold xkk. rewrite app_nth2 by lia. rewrite hkG, Nat.sub_diag.
      unfold GD. cbn [nth]. rewrite to_F_mul, to_F_mtotal.
      + rewrite hcsl. cbn [map]. field.
      + intro ec. rewrite ec in hcsl. cbn in hcsl. lia. }
    destruct (sc_loop_complete (fun c nm => get_F c nm 1) "G"%string (tmaskG kd k) (termsG kd base kG) (fst gGx) (snd gGx)
                (nth 0 rhoG xzero) dG 0 (tablesG kd base off E tz) [] c0 mG rz finG c1
                (xmul (xkk (kG ++ rhoG) kd) (nth 0 (GD n1 ell kd base k) xzero))) as ((clG & hv1 & hv2) & _ & _ & hpt & hmsg & hfin).
    - intro ec. pose proof (f_equal (@List.length nat) ec) as e'. rewrite dGX_len in e'. cbn in e'. lia.
    - discriminate.
    - rewrite hcsl, dGX_len. reflexivity.
    - intros i hi. rewrite dGX_len in hi |- *. cbn [Nat.add]. unfold round_ok. rewrite dGX_nth by exact hi.
      split; [destruct (Nat.eqb (S i) m); lia |].
      split; [rewrite <-dGX_nth by exact hi; apply hcsd; exact hi |].
      intros t ht. unfold termsG in ht. apply in_flat_map in ht. destruct ht as (d & hd & ht).
      apply in_seq in hd. apply in_map_iff in ht. destruct ht as (j & <- & hj). apply in_seq in hj. cbn [snd].
      destruct (Nat.eqb_spec (S i) m) as [_ | _].
      + cbn [map list_sum]. rewrite map_repeat.
        assert (hmd : mdeg (tmaskG kd k) (S d) = 2%nat).
        { unfold mdeg, tmaskG. cbn [nth].
          rewrite (nth_indep (map Some (a_dig kd k)) None (Some xzero)) by (rewrite length_map, a_dig_len; lia).
          rewrite map_nth. reflexivity. }
        assert (hm0 : mdeg (tmaskG kd k) 0 = 1%nat) by reflexivity.
        rewrite hmd, hm0.
        assert (hls : forall n, list_sum (repeat 2%nat n) = (2 * n)%nat)
          by (induction n as [| n ih]; [reflexivity |];
              change (list_sum (repeat 2%nat (S n))) with (2 + list_sum (repeat 2%nat n))%nat; rewrite ih; lia).
        change (list_sum (1 :: repeat 2 j)) with (1 + list_sum (repeat 2 j))%nat. rewrite hls. lia.
      + cbn [List.length]. rewrite repeat_length. lia.
    - reflexivity.
    - rewrite dGX_len. unfold tablesG. constructor.
      + rewrite xeq_table_length, htz. reflexivity.
      + apply Forall_map, Forall_forall. intros d _. rewrite length_map. apply Tdig_len.
    - unfold tablesG, tmaskG. cbn [List.length]. rewrite !length_map, length_seq, a_dig_len. reflexivity.
    - exact hclaim.
    - exact hsc.
    - exists clG. rewrite skipn_O in hv1. split; [exact hv1 |]. split; [exact hv2 |].
      rewrite dGX_len in hpt. split; [exact hpt |]. split; [exact hmsg |].
      intros j hj. rewrite (hfin j) by (unfold tablesG; cbn [List.length]; rewrite length_map, length_seq; lia).
      rewrite skipn_O. reflexivity.
  Qed.

  Theorem dscT : forall tt kT rhoT mT rt finT c0 c1,
    ternZ s -> ternZ e ->
    List.length tt = n1 -> List.length kT = 2%nat -> List.length rhoT = 1%nat ->
    sc_loop (fun c nm => get_F c nm 1) "T" (tmaskT kd k) (termsT kT) (fst gTx) (snd gTx)
            (nth 0 rhoT xzero) dT 0 (tablesT s e tt) [] c0 = Some (mT, rt, finT, c1) ->
    exists clT,
      xsc_verify mT rt (xmul (xkk (kT ++ rhoT) 2) (nth 1 (GD n1 ell kd base k) xzero)) = Some clT
      /\ to_F clT = fadd (termsF (map sF (termsT kT)) (map to_F finT))
                         (fmul (to_F (nth 0 rhoT xzero)) (gmask2 (to_F (fst gTx)) (csF (snd gTx)) (map to_F rt)))
      /\ List.length rt = n1 /\ Forall2 msg_ok mT dT
      /\ (forall j, (j < 3)%nat ->
            to_F (nth j finT xzero)
            = fadd (to_F (xmle (nth j (tablesT s e tt) []) rt)) (fmul (maskv (tmaskT kd k) j) (Zp2 (map to_F rt)))).
  Proof.
    intros tt kT rhoT mT rt finT c0 c1 hts hte htt hkT hrho hsc.
    destruct gT_shape as [hcsl hcsd].
    assert (hclaim : to_F (xmul (xkk (kT ++ rhoT) 2) (nth 1 (GD n1 ell kd base k) xzero))
                     = fadd (csum (map sF (termsT kT)) (tF (tablesT s e tt)) (2 ^ List.length dT))
                            (fmul (to_F (nth 0 rhoT xzero)) (@tsum Fq2 fzero fone fadd (gmask2 (to_F (fst gTx)) (csF (snd gTx))) (map to_F []) (List.length dT)))).
    { rewrite dTX_len, sumT_zero by assumption.
      unfold xkk. rewrite app_nth2 by lia. rewrite hkT. cbn [Nat.sub].
      unfold GD. cbn [nth]. rewrite to_F_mul, to_F_mtotal.
      + rewrite hcsl. cbn [map]. field.
      + intro ec. rewrite ec in hcsl. cbn in hcsl. lia. }
    destruct (sc_loop_complete (fun c nm => get_F c nm 1) "T"%string (tmaskT kd k) (termsT kT) (fst gTx) (snd gTx)
                (nth 0 rhoT xzero) dT 0 (tablesT s e tt) [] c0 mT rt finT c1
                (xmul (xkk (kT ++ rhoT) 2) (nth 1 (GD n1 ell kd base k) xzero))) as ((clT & hv1 & hv2) & _ & _ & hpt & hmsg & hfin).
    - intro ec. pose proof (f_equal (@List.length nat) ec) as e'. rewrite dTX_len in e'. cbn in e'. lia.
    - discriminate.
    - rewrite hcsl, dTX_len. reflexivity.
    - intros i hi. rewrite dTX_len in hi |- *. cbn [Nat.add]. unfold round_ok. rewrite dTX_nth by exact hi.
      split; [destruct (Nat.eqb (S i) n1); unfold DMAX; lia |].
      split; [rewrite <-dTX_nth by exact hi; apply hcsd; exact hi |].
      intros t ht. unfold termsT in ht. unfold mdeg, tmaskT.
      destruct (Nat.eqb (S i) n1); cbn in ht; destruct ht as [<- | [<- | [<- | [<- | []]]]]; cbn; lia.
    - reflexivity.
    - rewrite dTX_len. unfold tablesT, sZ, eZ. repeat constructor.
      + rewrite xeq_table_length, htt. reflexivity.
      + rewrite !length_map. exact Hs.
      + rewrite !length_map. exact He.
    - reflexivity.
    - exact hclaim.
    - exact hsc.
    - exists clT. rewrite skipn_O in hv1. split; [exact hv1 |]. split; [exact hv2 |].
      rewrite dTX_len in hpt. split; [exact hpt |]. split; [exact hmsg |].
      intros j hj. rewrite (hfin j) by (cbn; lia). rewrite skipn_O. reflexivity.
  Qed.

  (* the verifier's sumcheck layer on the prover's messages: it returns the public values, the prover's
     masked evaluations, and the two sumcheck masks at their points *)
  Theorem dderive : forall th th1 th2 tz kG rhoG mG rz finG tt kT rhoT mT rt finT c0 c1 c2 c3,
    List.length b = N -> List.length ts = tau -> Forall (fun l => List.length l = N) ts ->
    ternZ s -> ternZ e ->
    List.length th = ell -> List.length th1 = n1 -> List.length th2 = n1 -> List.length tz = m ->
    List.length kG = kd -> List.length rhoG = 1%nat -> List.length tt = n1 -> List.length kT = 2%nat ->
    List.length rhoT = 1%nat ->
    xnz (nth 0 rhoG xzero) = true -> xnz (nth 0 rhoT xzero) = true ->
    sc_loop (fun c nm => get_F c nm 1) "G" (tmaskG kd k) (termsG kd base kG) (fst gGx) (snd gGx)
            (nth 0 rhoG xzero) dG 0 (tablesG kd base off E tz) [] c0 = Some (mG, rz, finG, c1) ->
    sc_loop (fun c nm => get_F c nm 1) "T" (tmaskT kd k) (termsT kT) (fst gTx) (snd gTx)
            (nth 0 rhoT xzero) dT 0 (tablesT s e tt) [] c2 = Some (mT, rt, finT, c3) ->
    exists g1 g2,
      xdec_derive n1 ell kd base (map bx b) (bx pplain) (bx off) (map (map bx) ts) th th1 th2 tz (kG ++ rhoG) rz tt
                  (kT ++ rhoT) rt (nth 0 (GD n1 ell kd base k) xzero) (nth 1 (GD n1 ell kd base k) xzero) mG mT
                  (firstn kd (tl finG)) (firstn 2 (tl finT))
      = Some ([VDx (bx pplain) (bx off) (map (map bx) ts) th th1; VKx (map bx b) th2]
              ++ firstn kd (tl finG) ++ firstn 2 (tl finT) ++ [g1; g2])
      /\ to_F g1 = gmask2 (to_F (fst gGx)) (csF (snd gGx)) (map to_F rz)
      /\ to_F g2 = gmask2 (to_F (fst gTx)) (csF (snd gTx)) (map to_F rt)
      /\ List.length rz = m /\ List.length rt = n1
      /\ (forall j, (j < S kd)%nat ->
            to_F (nth j finG xzero)
            = fadd (to_F (xmle (nth j (tablesG kd base off E tz) []) rz)) (fmul (maskv (tmaskG kd k) j) (Zp2 (map to_F rz))))
      /\ (forall j, (j < 3)%nat ->
            to_F (nth j finT xzero)
            = fadd (to_F (xmle (nth j (tablesT s e tt) []) rt)) (fmul (maskv (tmaskT kd k) j) (Zp2 (map to_F rt)))).
  Proof.
    intros th th1 th2 tz kG rhoG mG rz finG tt kT rhoT mT rt finT c0 c1 c2 c3 hb hts htl hs he
      hth hth1 hth2 htz hkG hrG htt hkT hrT hnG hnT hG hT.
    destruct (dscG tz kG rhoG mG rz finG c0 c1 htz hkG hrG hG) as (clG & eG & vG & lrz & mGok & finGv).
    destruct (dscT tt kT rhoT mT rt finT c2 c3 hs he htt hkT hrT hT) as (clT & eT & vT & lrt & mTok & finTv).
    assert (hdG : dGX n1 ell base <> [])
      by (intro ec; pose proof (f_equal (@List.length nat) ec) as e'; rewrite (dGX_len n1 ell base) in e'; cbn in e'; lia).
    assert (hdT : dTX n1 <> [])
      by (intro ec; pose proof (f_equal (@List.length nat) ec) as e'; rewrite (dTX_len n1) in e'; cbn in e'; lia).
    assert (lfG : List.length finG = S kd).
    { rewrite (sc_loop_fin_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdG hG).
      unfold tablesG, tmaskG. cbn [List.length]. rewrite !length_map, length_seq, a_dig_len. lia. }
    assert (lfT : List.length finT = 3%nat) by (rewrite (sc_loop_fin_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdT hT); reflexivity).
    assert (lzG : List.length (firstn kd (tl finG)) = kd) by (rewrite length_firstn; destruct finG; cbn in lfG |- *; lia).
    assert (lzT : List.length (firstn 2 (tl finT)) = 2%nat)
      by (destruct finT as [| f0 [| f1 [| f2 fs]]]; cbn in lfT; try lia; reflexivity).
    assert (kkG : xkk (kG ++ rhoG) kd = nth 0 rhoG xzero)
      by (unfold xkk; rewrite app_nth2 by lia; rewrite hkG, Nat.sub_diag; reflexivity).
    assert (kkT : xkk (kT ++ rhoT) 2 = nth 0 rhoT xzero) by (unfold xkk; rewrite app_nth2 by lia; rewrite hkT; reflexivity).
    assert (f0G : to_F (nth 0 finG xzero) = to_F (xeq_eval rz tz)).
    { rewrite (finGv 0%nat) by lia. cbn [nth tablesG]. unfold maskv, tmaskG. cbn [nth].
      rewrite ExecBackD.xmle_eq by lia. field. }
    assert (f0T : to_F (nth 0 finT xzero) = to_F (xeq_eval rt tt)).
    { rewrite (finTv 0%nat) by lia. cbn [nth tablesT]. unfold maskv, tmaskT. cbn [nth].
      rewrite ExecBackD.xmle_eq by lia. field. }
    assert (hfG : termsF (map sF (termsG kd base kG)) (map to_F finG)
                  = to_F (fGx kd base tz (kG ++ rhoG) rz (firstn kd (tl finG)))).
    { rewrite termsG_val. unfold fGx. rewrite to_F_mul, <-f0G, to_F_nth.
      rewrite firstn_app, hkG, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by lia.
      rewrite innerZ_seq by (rewrite lzG; symmetry; exact hkG). rewrite hkG. f_equal.
      apply fsum_ext'. intros d hd. apply in_seq in hd.
      rewrite <-peval_rcoefs. f_equal. rewrite nth_firstn.
      destruct (Nat.ltb_spec d kd) as [_ | h]; [| lia].
      destruct finG as [| f0 fs]; [cbn in lfG; lia |]. cbn [tl]. rewrite <-to_F_nth. reflexivity. }
    assert (hfT : termsF (map sF (termsT kT)) (map to_F finT) = to_F (fTx tt (kT ++ rhoT) rt (firstn 2 (tl finT)))).
    { unfold fTx. rewrite firstn_app, hkT. cbn [Nat.sub firstn].
      rewrite to_F_mul, <-f0T.
      destruct finT as [| f0 [| f1 [| f2 fs]]]; cbn in lfT; try lia.
      destruct kT as [| k0 [| k1 [| k2 ks]]]; cbn in hkT; try lia.
      cbn [tl firstn xinnerZ app].
      unfold termsT, termsF, termF, sF. cbn [map fold_left fst snd LogDer.fsum nth].
      rewrite !to_F_add, !to_F_mul, !to_F_cube3, to_F_zero, !to_F_neg. unfold MixSummands.cube3. field. }
    unfold xdec_derive.
    match goal with |- context [if ?c then _ else _] => replace c with true end.
    2:{ symmetry. unfold dshapes_ok. rewrite !length_map, lzG, lzT, hth1, hth, hth2, hts, hb, !Nat.eqb_refl.
        rewrite (ExecBackD.forallb_dmax _ _ mGok), (ExecBackD.forallb_dmax _ _ mTok).
        - rewrite kkG, kkT, hnG, hnT. cbn [andb].
          replace (forallb (fun l => Nat.eqb (List.length l) N) (map (map bx) ts)) with true; [reflexivity |].
          symmetry. apply forallb_forall. intros l hl. apply in_map_iff in hl. destruct hl as (l0 & <- & hl0).
          rewrite length_map. apply Nat.eqb_eq. rewrite Forall_forall in htl. apply htl, hl0.
        - intros d hd. unfold dTX in hd. apply in_map_iff in hd. destruct hd as (i & <- & _). destruct (Nat.eqb _ _); unfold DMAX; lia.
        - intros d hd. unfold dGX in hd. apply in_map_iff in hd. destruct hd as (i & <- & _). destruct (Nat.eqb _ _); lia. }
    unfold claimGx, claimTx. rewrite eG, eT.
    eexists. eexists. split; [reflexivity |].
    split; [| split; [| split; [exact lrz | split; [exact lrt | split; [exact finGv | exact finTv]]]]].
    - rewrite to_F_mul, to_F_sub, to_F_inv, vG, hfG, kkG. field. apply xnz_sound. exact hnG.
    - rewrite to_F_mul, to_F_sub, to_F_inv, vT, hfT, kkT. field. apply xnz_sound. exact hnT.
  Qed.

End DSum.

(* ---------------------------------------------------------------------- *)
(* the digit decomposition recombines *)

Lemma digits_rec : forall (bs : Z) k s v, (1 <= bs)%Z -> (0 <= v)%Z ->
  fold_right Z.add 0%Z (map (fun d => bs ^ Z.of_nat d * ((v / bs ^ Z.of_nat d) mod bs))%Z (seq s k))
  = (bs ^ Z.of_nat s * ((v / bs ^ Z.of_nat s) mod bs ^ Z.of_nat k))%Z.
Proof.
  intros bs k; induction k as [| k ih]; intros s v hb hv.
  - cbn. rewrite Z.mod_1_r. lia.
  - cbn [seq map fold_right]. rewrite ih by assumption.
    assert (hps : (0 < bs ^ Z.of_nat s)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (hpk : (0 < bs ^ Z.of_nat k)%Z) by (apply Z.pow_pos_nonneg; lia).
    replace (bs ^ Z.of_nat (S s))%Z with (bs ^ Z.of_nat s * bs)%Z by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
    replace (bs ^ Z.of_nat (S k))%Z with (bs * bs ^ Z.of_nat k)%Z by (rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia; lia).
    rewrite <-Z.div_div by lia.
    rewrite Z.rem_mul_r by lia. ring.
Qed.

Lemma digits_sum : forall (bs : Z) k v, (1 <= bs)%Z -> (0 <= v < bs ^ Z.of_nat k)%Z ->
  fold_right Z.add 0%Z (map (fun d => bs ^ Z.of_nat d * ((v / bs ^ Z.of_nat d) mod bs))%Z (seq 0 k)) = v.
Proof.
  intros bs k v hb hv. rewrite digits_rec by lia. change (Z.of_nat 0) with 0%Z.
  rewrite Z.pow_0_r, Z.div_1_r, Z.mul_1_l, Z.mod_small by exact hv. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* step E, part 1: the honest rows *)

Lemma red_firstn_tl : forall kk (l : list xf), Forall reduced l -> Forall reduced (firstn kk (tl l)).
Proof.
  intros kk l h. destruct l as [| x l]; [destruct kk; constructor |].
  apply Forall_inv_tail in h. cbn [tl]. rewrite <-(firstn_skipn kk l) in h. apply Forall_app in h. tauto.
Qed.

Definition drows_ok (cnt len : nat) (rows : list (list Z)) : Prop :=
  List.length rows = cnt /\ Forall (fun r => List.length r = len) rows.

Lemma drows_le : forall cnt len rows, drows_ok cnt len rows -> Forall (fun r => (List.length r <= len)%nat) rows.
Proof. intros cnt len rows [_ h]. eapply Forall_impl; [| exact h]. intros r hr. cbv beta in *. lia. Qed.

Section DOpen.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k : dcoins.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation bBx := (btBD lo1 kd base nB omB off E k).
  Local Notation bSx := (btSD lo2 nS omS s e k).

  Definition dpok : Prop :=
    kB = (C1 + nqB)%nat /\ kS = (C2 + nqS)%nat
    /\ nB = (2 ^ log2n 64 nB)%nat /\ (1 <= log2n 64 nB)%nat /\ nS = (2 ^ log2n 64 nS)%nat /\ (1 <= log2n 64 nS)%nat
    /\ (2 * n_maskD n1 ell kd base <= C2)%nat /\ (N <= C2)%nat /\ (m <= lo1 + 64)%nat /\ (1 <= base)%nat.

  Definition dcok : Prop :=
    drows_ok 6 C1 (dfB k) /\ drows_ok SO nqB (dpB k) /\ drows_ok nB 16 (dsB k)
    /\ List.length (dmask k) = n_maskD n1 ell kd base
    /\ drows_ok 8 C2 (dfS k) /\ drows_ok 11 nqS (dpS k) /\ drows_ok nS 16 (dsS k).

  Definition dwshape : Prop :=
    List.length E = tau /\ Forall (fun l => List.length l = N) E /\ List.length s = N /\ List.length e = N.

  Hypothesis Hp : dpok.
  Hypothesis Hk : dcok.
  Hypothesis Hw : dwshape.

  Lemma Tdig_len' : forall d, List.length (Tdig base off E d) = (2 ^ m)%nat.
  Proof.
    intro d. unfold Tdig. destruct Hw as (hl & hf & _).
    rewrite (length_concat_uniform _ N), length_map, hl by
      (intros l hin; apply in_map_iff in hin; destruct hin as (Ei & <- & hEi); rewrite length_map;
       rewrite Forall_forall in hf; apply hf, hEi).
    rewrite Nat.pow_add_r. lia.
  Qed.

  Lemma dig_split : forall d, List.length (split_rows C1 (Tdig base off E d)) = rw
    /\ Forall (fun r => (List.length r <= C1)%nat) (split_rows C1 (Tdig base off E d)).
  Proof. intro d. exact (split_rows_shape lo1 m _ (Tdig_len' d)). Qed.

  Lemma digrows_len : List.length (flat_map (fun d => split_rows C1 (Tdig base off E d)) (seq 0 kd)) = (kd * rw)%nat.
  Proof. rewrite (flat_map_const_length' rw) by (intro d; exact (proj1 (dig_split d))). rewrite length_seq. lia. Qed.

  Lemma msgsBD_shape : List.length (msgsBD lo1 kd base off E k) = SO
    /\ Forall (fun r => List.length r = (C1 + nqB)%nat) (msgsBD lo1 kd base off E k).
  Proof.
    destruct Hk as (hfB & hpB & _).
    unfold msgsBD.
    destruct (padrows_shape C1 (flat_map (fun d => split_rows C1 (Tdig base off E d)) (seq 0 kd) ++ dfB k) (dpB k) nqB) as [e1 e2].
    - apply Forall_app. split; [| exact (drows_le _ _ _ hfB)].
      apply Forall_forall. intros r hr. apply in_flat_map in hr. destruct hr as (d & _ & hr).
      pose proof (proj2 (dig_split d)) as hh. rewrite Forall_forall in hh. exact (hh r hr).
    - exact (proj2 hpB).
    - rewrite length_app, digrows_len. destruct hfB as [-> _]. destruct hpB as [-> _]. unfold SOX. lia.
    - split; [rewrite e1, length_app, digrows_len; destruct hfB as [-> _]; unfold SOX; lia | exact e2].
  Qed.

  Lemma msgsSD_shape : List.length (msgsSD lo2 s e k) = 11%nat
    /\ Forall (fun r => List.length r = (C2 + nqS)%nat) (msgsSD lo2 s e k).
  Proof.
    destruct Hk as (_ & _ & _ & hm & hfS & hpS & _). destruct Hw as (_ & _ & hs & he).
    destruct Hp as (_ & _ & _ & _ & _ & _ & hmr & hNC & _ & _).
    unfold msgsSD.
    destruct (padrows_shape C2 ([sZ s; eZ e; mask_rowD k] ++ dfS k) (dpS k) nqS) as [e1 e2].
    - apply Forall_app. split; [| exact (drows_le _ _ _ hfS)].
      repeat constructor; unfold sZ, eZ, mask_rowD; rewrite ?length_map; try lia.
      change (flat_map (fun x => [fst x; snd x]) (dmask k)) with (mrow (dmask k)). rewrite mrow_length, hm. exact hmr.
    - exact (proj2 hpS).
    - rewrite length_app. destruct hfS as [-> _]. destruct hpS as [-> _]. reflexivity.
    - split; [rewrite e1, length_app; destruct hfS as [-> _]; reflexivity | exact e2].
  Qed.

  Definition AMD : list (list Z) := bmsgs bBx ++ bmsgs bSx.
  Lemma AMD_eq : AMD = msgsBD lo1 kd base off E k ++ msgsSD lo2 s e k.
  Proof. reflexivity. Qed.

  (* the honest decoded rows *)
  Definition PFD (i : nat) : list Fq2 := map to_F (map bx (nth i AMD [])).

  Lemma PFD_dig : forall d t, (d < kd)%nat -> (t < rw)%nat ->
    PFD (d * rw + t) = map to_F (map bx (padrow C1 (nth t (split_rows C1 (Tdig base off E d)) []) (nth (d * rw + t) (dpB k) []))).
  Proof.
    intros d t hd ht. unfold PFD. rewrite AMD_eq.
    destruct msgsBD_shape as [hlB _].
    rewrite app_nth1 by (rewrite hlB; unfold SOX; nia).
    destruct Hk as (hfB & hpB & _). destruct hfB as [hfB _]. destruct hpB as [hpB _].
    unfold msgsBD. rewrite ExecBackO.nth_msgs.
    2: { rewrite length_app, digrows_len, hfB, hpB. unfold SOX. lia. }
    2: { rewrite length_app, digrows_len, hfB. nia. }
    f_equal. f_equal. f_equal.
    rewrite app_nth1 by (rewrite digrows_len; nia).
    rewrite flat_map_concat_map.
    rewrite (Nat.add_comm (d * rw) t), (Nat.mul_comm d rw).
    rewrite (ExecDec.nth_concat_uniform _ rw t d []).
    - rewrite nth_map_seq0 by exact hd. reflexivity.
    - intros l hl. apply in_map_iff in hl. destruct hl as (d' & <- & _). exact (proj1 (dig_split d')).
    - exact ht.
    - rewrite length_map, length_seq. exact hd.
  Qed.

  Lemma PFD_small : forall j, (j < 3)%nat ->
    PFD (SO + j) = map to_F (map bx (padrow C2 (nth j [sZ s; eZ e; mask_rowD k] []) (nth j (dpS k) []))).
  Proof.
    intros j hj. unfold PFD. rewrite AMD_eq.
    destruct msgsBD_shape as [hlB _].
    rewrite app_nth2 by (rewrite hlB; lia). rewrite hlB. replace (SO + j - SO)%nat with j by lia.
    destruct Hk as (_ & _ & _ & _ & hfS & hpS & _). destruct hfS as [hfS _]. destruct hpS as [hpS _].
    unfold msgsSD. rewrite ExecBackO.nth_msgs by (rewrite length_app, ?hfS, ?hpS; cbn; lia).
    rewrite app_nth1 by (cbn; lia). reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* tables read off the honest rows *)

  Local Notation rdt := (@rdtab Fq2 fzero fone Fq2_dec).
  Local Notation pt2 := (@pt Fq2 fzero fone).
  Local Notation nmulF := (@nmul Fq2 fzero fadd fmul fopp).

  Lemma digT_tab : forall d X, (d < kd)%nat -> (X < 2 ^ m)%nat ->
    rdt PFD (d * rw) m lo1 (pt2 m X) = to_F (bx (nth X (Tdig base off E d) 0%Z)).
  Proof.
    intros d X hd hX.
    apply (rdtab_list PFD (d * rw) m lo1 (Tdig base off E d) (fun t => nth (d * rw + t) (dpB k) [])); [apply Tdig_len' | | exact hX].
    intros t ht. exact (PFD_dig d t hd ht).
  Qed.

  Lemma row_val : forall j x, (j < 2)%nat -> (x < N)%nat ->
    nth x (PFD (SO + j)) fzero = to_F (bx (nth x (nth j [s; e] []) 0%Z)).
  Proof.
    intros j x hj hx. rewrite (PFD_small j) by lia.
    rewrite (nth_map_dflt to_F _ x xzero fzero to_F_zero), (nth_map_dflt bx _ x 0%Z xzero eq_refl).
    destruct Hw as (_ & _ & hs & he).
    destruct j as [| [| j]]; try lia; cbn [nth]; unfold sZ, eZ;
      rewrite nth_padrow by (rewrite length_map; lia);
      rewrite (nth_map_dflt zm _ x 0%Z 0%Z eq_refl), !to_F_bx_zm; reflexivity.
  Qed.

  Lemma ment_val : forall j, (j < n_maskD n1 ell kd base)%nat ->
    @ment Fq2 fzero fadd fmul ftg (PFD (SO + 2)) j = to_F (nth j (dmask k) xzero).
  Proof.
    intros j hj. rewrite (PFD_small 2) by lia. cbn [nth].
    change (mask_rowD k) with (mrow (dmask k)). apply ment_row.
    destruct Hk as (_ & _ & _ & hm & _). rewrite hm. exact hj.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the relation, over GF(q^2) *)

  Definition dvalid : Prop :=
    ternZ s /\ ternZ e
    /\ (forall i x, (i < tau)%nat -> (x < N)%nat ->
          ((nth x (nth i E []) 0 + off) mod Q < Z.of_nat base ^ Z.of_nat kd)%Z)
    /\ (forall i x, (i < tau)%nat -> (x < N)%nat ->
          to_F (bx (nth x (nth i ts []) 0%Z))
          = fadd (nth x (nmulF (map to_F (map bx (nth i us []))) (map to_F (map bx s))) fzero)
                 (fmul (to_F (bx pplain)) (to_F (bx (nth x (nth i E []) 0%Z)))))
    /\ (forall x, (x < N)%nat ->
          to_F (bx (nth x b 0%Z))
          = fadd (nth x (nmulF (map to_F (map bx a)) (map to_F (map bx s))) fzero)
                 (fmul (to_F (bx pplain)) (to_F (bx (nth x e 0%Z))))).

  Local Notation ppF := (to_F (bx pplain)).
  Local Notation offF := (to_F (bx off)).
  Local Notation usF := (fun i => map to_F (nth i (usX us) [])).
  Local Notation tsF := (fun i => map to_F (nth i (tsX ts) [])).

  Lemma cube_pt_ex : forall bq, In bq (@Mle.cube Fq2 fzero fone m) -> exists X, (X < 2 ^ m)%nat /\ bq = pt2 m X.
  Proof.
    intros bq hbq.
    pose proof (Permutation_in _ (Permutation_sym (@pt_perm Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field m)) hbq) as h.
    apply in_map_iff in h. destruct h as (X & <- & hX). apply in_seq in hX. exists X. split; [lia | reflexivity].
  Qed.

  Lemma Tdig_nth : forall d i x, (i < tau)%nat -> (x < N)%nat ->
    nth (x + N * i) (Tdig base off E d) 0%Z = digit base off d (nth x (nth i E []) 0%Z).
  Proof.
    intros d i x hi hx. destruct Hw as (hl & hf & _). unfold Tdig.
    rewrite (ExecDec.nth_concat_uniform _ N x i 0%Z).
    - rewrite (nth_map_dflt (map (digit base off d)) _ i [] [] eq_refl).
      assert (hEi : List.length (nth i E []) = N) by (rewrite Forall_forall in hf; apply hf, nth_In; lia).
      rewrite (nth_indep _ 0%Z (digit base off d 0%Z)) by (rewrite length_map, hEi; exact hx).
      apply map_nth.
    - intros l hin. apply in_map_iff in hin. destruct hin as (Ei & <- & hEi). rewrite length_map.
      rewrite Forall_forall in hf. apply hf, hEi.
    - exact hx.
    - rewrite length_map, hl. exact hi.
  Qed.

  Lemma Esum_digits : forall i x, (i < tau)%nat -> (x < N)%nat -> forall j s0, (s0 + j <= kd)%nat ->
    @Esum Fq2 fzero fone fadd fmul base (map (@digT Fq2 fzero fone Fq2_dec PFD n1 ell lo1) (seq s0 j)) s0 (pt2 m (x + N * i))
    = to_F (bx (fold_right Z.add 0%Z (map (fun d => Z.of_nat base ^ Z.of_nat d * digit base off d (nth x (nth i E []) 0%Z))%Z
                                            (seq s0 j)))).
  Proof.
    intros i x hi hx j; induction j as [| j ih]; intros s0 hj.
    - cbn. change (bx 0%Z) with (bz 0%Z). symmetry. apply xfft_bz0.
    - cbn [seq map Esum fold_right]. rewrite ih by lia.
      unfold digT. rewrite digT_tab by (lia || (rewrite Nat.pow_add_r; nia)).
      rewrite Tdig_nth by assumption.
      change (bx (Z.of_nat base ^ Z.of_nat s0 * digit base off s0 (nth x (nth i E []) 0) + _)%Z)
        with (bz (Z.of_nat base ^ Z.of_nat s0 * digit base off s0 (nth x (nth i E []) 0) + fold_right Z.add 0%Z
                (map (fun d => Z.of_nat base ^ Z.of_nat d * digit base off d (nth x (nth i E []) 0))%Z (seq (S s0) j)))%Z).
      rewrite xfft_to_F_bx_add, xfft_to_F_bx_mul, <-Nat2Z.inj_pow, to_F_bz_nat. reflexivity.
  Qed.

  Lemma sK_honest : @DecSound.sK Fq2 fzero fone n1 (@stabT Fq2 fzero fone Fq2_dec PFD SO) = map to_F (map bx s).
  Proof.
    destruct Hw as (_ & _ & hs & he).
    apply nth_ext with (d := fzero) (d' := fzero).
    - unfold DecSound.sK. rewrite !length_map, length_seq, hs. reflexivity.
    - intros x hx. unfold DecSound.sK in hx. rewrite length_map, length_seq in hx.
      unfold DecSound.sK. rewrite nth_map_seq0 by exact hx.
      unfold stabT, rS. rewrite (@rowT_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 SO x hx).
      rewrite <-(Nat.add_0_r SO), (row_val 0 x) by lia. cbn [nth].
      rewrite (nth_map_dflt to_F _ x xzero fzero to_F_zero), (nth_map_dflt bx _ x 0%Z xzero eq_refl). reflexivity.
  Qed.

  Lemma eK_honest : @DecSound.eK Fq2 fzero fone n1 (@etabT Fq2 fzero fone Fq2_dec PFD SO) = map to_F (map bx e).
  Proof.
    destruct Hw as (_ & _ & hs & he).
    apply nth_ext with (d := fzero) (d' := fzero).
    - unfold DecSound.eK. rewrite !length_map, length_seq, he. reflexivity.
    - intros x hx. unfold DecSound.eK in hx. rewrite length_map, length_seq in hx.
      unfold DecSound.eK. rewrite nth_map_seq0 by exact hx.
      unfold etabT, rE. rewrite (@rowT_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 (SO + 1) x hx).
      rewrite (row_val 1 x) by lia. cbn [nth].
      rewrite (nth_map_dflt to_F _ x xzero fzero to_F_zero), (nth_map_dflt bx _ x 0%Z xzero eq_refl). reflexivity.
  Qed.

  Lemma DtabT_zero : dvalid -> forall bq, In bq (@Mle.cube Fq2 fzero fone m) ->
    @DtabT Fq2 fzero fone fadd fmul fsub fopp Fq2_dec PFD n1 ell lo1 SO kd base ppF offF usF tsF bq = fzero.
  Proof.
    intros hv bq hbq. destruct (cube_pt_ex bq hbq) as (X & hX & ->).
    destruct hv as (_ & _ & hrange & hD & _).
    assert (hN : (0 < N)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    set (x := (X mod N)%nat). set (i := (X / N)%nat).
    assert (eX : X = (x + N * i)%nat) by (unfold x, i; rewrite Nat.add_comm, <-Nat.div_mod; lia).
    assert (hx : (x < N)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (hi : (i < tau)%nat) by (unfold i; apply Nat.Div0.div_lt_upper_bound; rewrite <-Nat.pow_add_r; exact hX).
    rewrite eX, (pt_split n1 ell x i hx).
    rewrite (@HD_T Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 ell lo1 SO kd base ppF offF usF tsF i x hi hx).
    unfold DecSound.Dcoef, DecSound.Ecoef. rewrite sK_honest.
    unfold dtsT. rewrite <-(pt_split n1 ell x i hx).
    rewrite (Esum_digits i x hi hx kd 0) by lia.
    assert (hb1 : (1 <= Z.of_nat base)%Z) by (destruct Hp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & hb); lia).
    assert (hv0 : (0 <= (nth x (nth i E []) 0 + off) mod Q)%Z) by (apply Z.mod_pos_bound; unfold Q; lia).
    unfold digit. rewrite (digits_sum (Z.of_nat base) kd) by (exact hb1 || (split; [exact hv0 | exact (hrange i x hi hx)])).
    change (bx ((nth x (nth i E []) 0 + off) mod Q)%Z) with (bx (zm (nth x (nth i E []) 0 + off)%Z)).
    rewrite to_F_bx_zm. change (bx (nth x (nth i E []) 0 + off)%Z) with (bz (nth x (nth i E []) 0 + off)%Z).
    rewrite xfft_to_F_bx_add. unfold tsX, usX.
    rewrite (nth_map_dflt (map bx) _ i [] [] eq_refl), (nth_map_dflt to_F _ x xzero fzero to_F_zero),
            (nth_map_dflt bx _ x 0%Z xzero eq_refl).
    rewrite (nth_map_dflt (map bx) us i [] [] eq_refl).
    rewrite (hD i x hi hx). change (bz off) with (bx off). change (bz (nth x (nth i E []) 0%Z)) with (bx (nth x (nth i E []) 0%Z)).
    field.
  Qed.

  Lemma KtabT_zero : dvalid -> forall bq, In bq (@Mle.cube Fq2 fzero fone n1) ->
    @KtabT Fq2 fzero fone fadd fmul fsub fopp Fq2_dec PFD n1 SO (map to_F (aDX a)) (map to_F (bDX b)) ppF bq = fzero.
  Proof.
    intros hv bq hbq.
    pose proof (Permutation_in _ (Permutation_sym (@pt_perm Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1)) hbq) as h.
    apply in_map_iff in h. destruct h as (x & <- & hx). apply in_seq in hx. cbn [Nat.add] in hx. destruct hx as [_ hx].
    destruct hv as (_ & _ & _ & _ & hK).
    rewrite (@HK_T Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 SO _ _ ppF x hx).
    unfold DecSound.Kcoef. rewrite sK_honest, eK_honest.
    unfold aDX, bDX. rewrite (nth_map_dflt to_F _ x xzero fzero to_F_zero), (nth_map_dflt bx _ x 0%Z xzero eq_refl).
    rewrite (hK x hx). rewrite (nth_map_dflt to_F (map bx e) x xzero fzero to_F_zero), (nth_map_dflt bx e x 0%Z xzero eq_refl).
    field.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the values of the claims on the honest rows *)

  Lemma evalsOf_seq : forall M (f : nat -> list Fq2 -> Fq2) (g : nat -> Fq2) r j s0,
    @ZeroTest.evalsOf Fq2 fzero fone fadd fmul fsub M (map f (seq s0 j)) (map g (seq s0 j)) r
    = map (fun d => @mstar Fq2 fzero fone fadd fmul fsub M (f d) (g d) r) (seq s0 j).
  Proof. intros M f g r j; induction j as [| j ih]; intro s0; [reflexivity |]. cbn [seq map ZeroTest.evalsOf]. rewrite ih. reflexivity. Qed.

  Lemma mle_dig : forall d (r : list xf), (d < kd)%nat -> List.length r = m ->
    @mle Fq2 fzero fone fadd fmul fsub m (@digT Fq2 fzero fone Fq2_dec PFD n1 ell lo1 d) (map to_F r)
    = to_F (xmle (map bx (Tdig base off E d)) r).
  Proof.
    intros d r hd hr. apply mle_list; [rewrite length_map; apply Tdig_len' | exact hr |].
    intros X hX. unfold digT. rewrite digT_tab by assumption.
    rewrite (nth_map_dflt bx _ X 0%Z xzero eq_refl). reflexivity.
  Qed.

  Lemma mle_row : forall j (r : list xf), (j < 2)%nat -> List.length r = n1 ->
    @mle Fq2 fzero fone fadd fmul fsub n1 (@rowT Fq2 fzero fone Fq2_dec PFD (SO + j)) (map to_F r)
    = to_F (xmle (map bx (map zm (nth j [s; e] []))) r).
  Proof.
    intros j r hj hr. destruct Hw as (_ & _ & hs & he).
    apply mle_list; [rewrite !length_map; destruct j as [| [| j]]; cbn; lia | exact hr |].
    intros x hx. rewrite (@rowT_pt Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 (SO + j) x hx).
    rewrite (row_val j x hj hx). rewrite (nth_map_dflt bx _ x 0%Z xzero eq_refl), (nth_map_dflt zm _ x 0%Z 0%Z eq_refl).
    rewrite to_F_bx_zm. reflexivity.
  Qed.

  Local Notation gtvalD := (fun ptD rz => @gtval Fq2 fzero fadd fmul PFD kindD (@LtD Fq2 fzero fone fadd fmul fsub n1 ell lo1 ptD rz)).

  Theorem dlayout : dvalid -> forall (th th1 th2 tz rz tt rt finG finT : list xf) (g1 g2 : xf),
    List.length th = ell -> List.length th1 = n1 -> List.length th2 = n1 -> List.length rz = m -> List.length rt = n1 ->
    List.length finG = S kd -> List.length finT = 3%nat ->
    List.length ts = tau -> Forall (fun l => List.length l = N) ts ->
    (forall j, (j < S kd)%nat ->
       to_F (nth j finG xzero)
       = fadd (to_F (xmle (nth j (tablesG kd base off E tz) []) rz)) (fmul (maskv (tmaskG kd k) j) (Zp2 (map to_F rz)))) ->
    (forall j, (j < 3)%nat ->
       to_F (nth j finT xzero)
       = fadd (to_F (xmle (nth j (tablesT s e tt) []) rt)) (fmul (maskv (tmaskT kd k) j) (Zp2 (map to_F rt)))) ->
    to_F g1 = gmask2 (to_F (fst (gGD n1 ell kd base k))) (csF (snd (gGD n1 ell kd base k))) (map to_F rz) ->
    to_F g2 = gmask2 (to_F (fst (gTD n1 ell kd base k))) (csF (snd (gTD n1 ell kd base k))) (map to_F rt) ->
    map (gtvalD (map to_F (th1 ++ th)) (map to_F rz))
        (@claimsD Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base (map to_F (aDX a)) ppF usF
                  (dGX n1 ell base) (dTX n1) (map to_F (th1 ++ th)) (map to_F th2) (map to_F rz) (map to_F rt))
    = map to_F ([VDx (bx pplain) (bx off) (map (map bx) ts) th th1; VKx (map bx b) th2]
                ++ firstn kd (tl finG) ++ firstn 2 (tl finT) ++ [g1; g2]).
  Proof.
    intros hv th th1 th2 tz rz tt rt finG finT g1 g2 hth hth1 hth2 hrz hrt lfG lfT hts htl hfG hfT hg1 hg2.
    assert (hpt : List.length (map to_F (th1 ++ th)) = m) by (rewrite length_map, length_app; lia).
    cbv beta.
    rewrite (@layout_identityD Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD ftg n1 ell lo1 SO kd base
               (map to_F (aDX a)) ppF usF (dGX n1 ell base) (dTX n1) (map to_F (th1 ++ th)) (map to_F th2) (map to_F rz) (map to_F rt)
               hpt ltac:(rewrite length_map; exact hth2) ltac:(rewrite length_map; exact hrz) ltac:(rewrite length_map; exact hrt)
               (dGX_len n1 ell base) (dTX_len n1)).
    cbn [map app].
    f_equal.
    - (* claim D: the defect table vanishes, so the claim has the public value VD *)
      pose proof (@claimD Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 ell lo1 SO kd base ppF offF usF tsF
                   (dGX n1 ell base) (dTX n1) (map to_F (th1 ++ th)) (map to_F th2) (map to_F rz) (map to_F rt)
                   hpt ltac:(rewrite length_map; exact hth2) ltac:(rewrite length_map; exact hrz) ltac:(rewrite length_map; exact hrt)
                   (dGX_len n1 ell base) (dTX_len n1)) as hc.
      rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub m _ (fun _ => fzero)) in hc
        by (intros bq hbq; apply DtabT_zero; assumption).
      rewrite (@CubeIndex.mle_const Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field m fzero _ hpt) in hc.
      match type of hc with fsub ?v ?g = fzero => transitivity v; [transitivity (fsub v (fsub v g)); [field | rewrite hc; field] |] end.
      symmetry.
      exact (ExecDec.VD_value n1 ell 0 (bx pplain) (bx off) (map (map bx) ts) th th1 th2 [] [] [] [] [] [] [] eq_refl hth1 hth
               ltac:(rewrite length_map; exact hts)
               ltac:(intros l hl; apply in_map_iff in hl; destruct hl as (l0 & <- & hl0); rewrite length_map;
                     rewrite Forall_forall in htl; apply htl, hl0)).
    - f_equal.
      + (* claim K *)
        pose proof (@claimK Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_dec Fq2_field PFD n1 ell lo1 SO (map to_F (aDX a)) (map to_F (bDX b)) ppF
                     (dGX n1 ell base) (dTX n1) (map to_F (th1 ++ th)) (map to_F th2) (map to_F rz) (map to_F rt)
                     hpt ltac:(rewrite length_map; exact hth2) ltac:(rewrite length_map; exact hrz) ltac:(rewrite length_map; exact hrt)
                     (dGX_len n1 ell base) (dTX_len n1)) as hc.
        rewrite (@mle_ext Fq2 fzero fone fadd fmul fsub n1 _ (fun _ => fzero)) in hc
          by (intros bq hbq; apply KtabT_zero; assumption).
        rewrite (@CubeIndex.mle_const Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n1 fzero _ ltac:(rewrite length_map; exact hth2)) in hc.
        match type of hc with fsub ?v ?g = fzero => transitivity v; [transitivity (fsub v (fsub v g)); [field | rewrite hc; field] |] end.
        unfold VDv, VKx, VKv. rewrite to_F_dot, to_F_eq_table, hth2. reflexivity.
      + rewrite !map_app. f_equal; [| f_equal].
        * (* the masked evaluations of the digit tables *)
          unfold dtsT, avG. rewrite evalsOf_seq.
          assert (lzG : List.length (firstn kd (tl finG)) = kd) by (rewrite length_firstn; destruct finG; cbn in lfG |- *; lia).
          apply nth_ext with (d := fzero) (d' := fzero); [rewrite !length_map, length_seq, lzG; reflexivity |].
          intros d hd. rewrite length_map, length_seq in hd.
          rewrite nth_map_seq0 by exact hd.
          rewrite (nth_map_dflt to_F _ d xzero fzero to_F_zero), nth_firstn.
          destruct (Nat.ltb_spec d kd) as [_ | h]; [| lia].
          destruct finG as [| f0 fs]; [cbn in lfG; lia |]. cbn [tl].
          change (nth d fs xzero) with (nth (S d) (f0 :: fs) xzero).
          rewrite (hfG (S d)) by lia.
          unfold mstar. rewrite mle_dig by (lia || exact hrz).
          unfold tablesG. cbn [nth]. rewrite nth_map_seq0 by exact hd.
          unfold maskv, tmaskG. cbn [nth].
          assert (hadl : List.length (a_dig kd k) = kd)
            by (unfold a_dig; rewrite length_firstn; destruct Hk as (_ & _ & _ & hm & _); rewrite hm; unfold n_maskD; lia).
          rewrite (nth_indep (map Some (a_dig kd k)) None (Some xzero)) by (rewrite length_map, hadl; exact hd).
          rewrite map_nth. unfold a_dig. rewrite nth_firstn. destruct (Nat.ltb_spec d kd) as [_ | h]; [| lia].
          unfold PmD, rMd. rewrite (ment_val d) by (unfold n_maskD; lia). reflexivity.
        * (* the masked evaluations of s and e *)
          destruct finT as [| f0 [| f1 [| f2 fs]]]; cbn in lfT; try lia.
          cbn [tl firstn map app ZeroTest.evalsOf]. unfold avT. cbn [ZeroTest.evalsOf].
          f_equal; [| f_equal].
          { unfold mstar, stabT, rS. rewrite <-(Nat.add_0_r SO), (mle_row 0 rt) by (lia || exact hrt).
            change f1 with (nth 1 (f0 :: f1 :: f2 :: fs) xzero). rewrite (hfT 1%nat) by lia. cbn [nth tablesT]. unfold sZ.
            unfold maskv, tmaskT. cbn [nth]. unfold PmD, rMd.
            rewrite Nat.add_0_r, (ment_val kd) by (unfold n_maskD; lia). reflexivity. }
          { unfold mstar, etabT, rE. rewrite (mle_row 1 rt) by (lia || exact hrt).
            change f2 with (nth 2 (f0 :: f1 :: f2 :: fs) xzero). rewrite (hfT 2%nat) by lia. cbn [nth tablesT]. unfold eZ.
            unfold maskv, tmaskT. cbn [nth]. unfold PmD, rMd. rewrite (ment_val (kd + 1)) by (unfold n_maskD; lia). reflexivity. }
        * (* the two sumcheck masks, read off the mask row *)
          cbn [map]. rewrite hg1, hg2.
          destruct Hk as (_ & _ & _ & hm & _).
          assert (hsum : (list_sum (dGX n1 ell base) + list_sum (dTX n1) + kd + 4 <= n_maskD n1 ell kd base)%nat)
            by (unfold n_maskD; lia).
          unfold a0GT, csGT, a0TT, csTT, maskA0, offG, offT, PmD, rMd.
          rewrite (PFD_small 2) by lia. cbn [nth].
          change (mask_rowD k) with (mrow (dmask k)).
          rewrite !maskCs_row by (rewrite hm, ?dsumL_list_sum; lia).
          rewrite !ment_row by (rewrite hm, ?dsumL_list_sum; lia).
          unfold gGD, gTD, mask_ofD. cbn [fst snd]. unfold csF.
          rewrite !nth_skipn, !Nat.add_0_r, dsumL_list_sum.
          unfold offG.
          replace (kd + 2 + 1 + list_sum (dGX n1 ell base))%nat with (kd + 3 + list_sum (dGX n1 ell base))%nat by lia.
          assert (hc1 : (kd + 3 + list_sum (dGX n1 ell base) + 1 + dsumL (dTX n1) <= List.length (dmask k))%nat).
          { rewrite hm. unfold n_maskD. rewrite (dsumL_list_sum (dTX n1)). lia. }
          rewrite (maskCs_row (2 ^ lo2) (dmask k) (nth 2 (dpS k) []) (kd + 3 + list_sum (dGX n1 ell base)) (dTX n1) hc1).
          rewrite (ment_row (2 ^ lo2) (dmask k) (nth 2 (dpS k) []) (kd + 3 + list_sum (dGX n1 ell base))) by lia.
          reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the opening: helpers *)

  Local Notation F2 := Fq2.
  Local Notation pevalF2 := (@PolyRoots.eval Fq2 fzero fadd fmul).

  Lemma combD_msum : forall cb, map to_F (combD bBx bSx cb) = @msum Fq2 fadd fmul PFD (map pairF cb).
  Proof.
    intros cb. unfold combD. induction cb as [| [i w] cb ih]; [reflexivity |].
    cbn [fold_right map Opening.msum fst snd]. rewrite to_F_padd, to_F_pscale, ih. reflexivity.
  Qed.

  (* the opened entries of the verifier's record are the codewords of the honest rows *)
  Lemma XeBD : forall T i j, In j (map Z.to_nat (dt_JB T)) -> (j < nB)%nat -> (i < SO)%nat ->
    to_F (dXe (dfmk n1 ell lo1 kd (dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T) T) i j)
    = pevalF2 (PFD i) (pwF (to_F (bx omB)) j).
  Proof.
    intros T i j hj hjn hi. destruct msgsBD_shape as [hlB _].
    unfold dfmk. cbv zeta. cbn [dXe].
    destruct (Nat.ltb_spec i SO) as [_ | h]; [| lia].
    cbn [dparts_of pcolsB]. rewrite map_map. rewrite ExecBackO.nth_idx_map by exact hj. cbn [flat_map fst bitem]. rewrite app_nil_r.
    unfold btBD. rewrite commit_col by exact hjn.
    rewrite (ExecBackO.nth_map_indep _ _ i []) by (rewrite hlB; exact hi).
    rewrite ExecNtt.zenc_F by exact hjn.
    unfold PFD. rewrite AMD_eq, app_nth1 by (rewrite hlB; exact hi). reflexivity.
  Qed.

  Lemma XeSD : forall T i j, In j (map Z.to_nat (dt_JS T)) -> (j < nS)%nat -> (SO <= i < SO + 11)%nat ->
    to_F (dXe (dfmk n1 ell lo1 kd (dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T) T) i j)
    = pevalF2 (PFD i) (pwF (to_F (bx omS)) j).
  Proof.
    intros T i j hj hjn hi. destruct msgsBD_shape as [hlB _]. destruct msgsSD_shape as [hlS _].
    unfold dfmk. cbv zeta. cbn [dXe].
    destruct (Nat.ltb_spec i SO) as [h | _]; [lia |].
    cbn [dparts_of pcolsS]. rewrite map_map. rewrite ExecBackO.nth_idx_map by exact hj. cbn [flat_map fst bitem]. rewrite app_nil_r.
    unfold btSD. rewrite commit_col by exact hjn.
    rewrite (ExecBackO.nth_map_indep _ _ (i - SO) []) by (rewrite hlS; lia).
    rewrite ExecNtt.zenc_F by exact hjn.
    unfold PFD. rewrite AMD_eq, (app_nth2 (msgsBD lo1 kd base off E k)) by (rewrite hlB; lia). rewrite hlB. reflexivity.
  Qed.

  Local Notation PT := (fun T => dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T).
  Local Notation clsF := (fun f => map (map ExecClaims.tF) (clsX n1 ell lo1 kd base pplain a us f)).
  Local Notation claimsT := (fun T => @claimsD Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base (map to_F (aDX a)) ppF usF
                                  (dGX n1 ell base) (dTX n1) (map to_F (dt_th1 T ++ dt_th T)) (map to_F (dt_th2 T))
                                  (map to_F (dt_rz T)) (map to_F (dt_rt T))).
  Local Notation LtT := (fun T => @LtD Fq2 fzero fone fadd fmul fsub n1 ell lo1 (map to_F (dt_th1 T ++ dt_th T)) (map to_F (dt_rz T))).

  Lemma clsF_T : forall T, List.length (dt_th T) = ell -> List.length (dt_th1 T) = n1 -> List.length (dt_th2 T) = n1 ->
    List.length (dt_rz T) = m -> List.length (dt_rt T) = n1 ->
    clsF (f1T T) = claimsT T.
  Proof.
    intros T h0 h1 h2 hz ht. cbv beta. unfold clsX, ptX, f1T, front0. cbn [dth dth1 dth2 drz drt].
    apply to_F_claimsD; [rewrite length_app; lia | exact h2 | exact hz | exact ht].
  Qed.

  Lemma LtX_T : forall T, List.length (dt_th T) = ell -> List.length (dt_th1 T) = n1 -> List.length (dt_rz T) = m ->
    forall v, map to_F (LtX lo1 (f1T T) v) = LtT T v.
  Proof.
    intros T h0 h1 hz v. cbv beta. unfold LtX, LtD, ptX, f1T, front0. cbn [dth dth1 drz].
    destruct (Nat.eqb v 1); rewrite to_F_lo_vec; [rewrite length_app, h1, h0, map_app | rewrite hz]; reflexivity.
  Qed.

  Theorem dbatch : forall T, List.length (dt_th T) = ell -> List.length (dt_th1 T) = n1 -> List.length (dt_th2 T) = n1 ->
    List.length (dt_rz T) = m -> List.length (dt_rt T) = n1 -> List.length (dt_kp T) = (kd + 6)%nat ->
    fsumF (map (fun v => @LogDer.dot Fq2 fzero fadd fmul (map to_F (usD n1 ell lo1 kd base pplain a us bBx bSx (f1T T) v))
                                     (map to_F (LD n1 ell lo1 kd base pplain a us (f1T T) v))) [1; 2; 3; 4; 5]%nat)
    = @LogDer.dot Fq2 fzero fadd fmul (map to_F (dt_kp T))
        (map (@gtval Fq2 fzero fadd fmul PFD kindD (LtT T)) (claimsT T)).
  Proof.
    intros T h0 h1 h2 hz ht hkp.
    transitivity (fsumF (map (fun v => @vsum Fq2 fzero fadd fmul PFD (@cbk Fq2 fone fmul kindD (frowD SO) (map to_F (dt_kp T)) (claimsT T) v)
                                         (@Lk Fq2 fadd fmul kindD (LtT T) (map to_F (dt_kp T)) (claimsT T) v)) [1; 2; 3; 4; 5]%nat)).
    { apply fsum_ext'. intros v _.
      unfold usD, LD. rewrite combD_msum, to_F_cbk, to_F_Lk.
      rewrite (@dot_msum Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
      unfold clsPD. cbn [dkp f1T front0]. rewrite (clsF_T T h0 h1 h2 hz ht).
      f_equal. apply ExecBackO.Lk_ext. intro v'. apply LtX_T; assumption. }
    apply (@batch_mixed Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field PFD kindD (LtT T) (frowD SO)
             [1; 2; 3; 4; 5]%nat (claimsT T) (map to_F (dt_kp T))).
    - repeat constructor; cbn; lia.
    - rewrite length_map, hkp, claimsD_length; [reflexivity | ..];
        rewrite ?length_map, ?length_app; first [apply dGX_len | apply dTX_len | lia].
    - intros cl hcl t hti.
      destruct (@claimsD_terms Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base (map to_F (aDX a)) ppF usF (dGX n1 ell base) (dTX n1)
                  (map to_F (dt_th1 T ++ dt_th T)) (map to_F (dt_th2 T)) (map to_F (dt_rz T)) (map to_F (dt_rt T))
                  ltac:(rewrite length_map, length_app; lia) ltac:(rewrite length_map; exact h2) ltac:(rewrite length_map; exact hz)
                  ltac:(rewrite length_map; exact ht) (dGX_len n1 ell base) (dTX_len n1) cl t hcl hti)
        as [[ev _] | [[ev _] | [[ev _] | [[ev _] | [ev _]]]]]; rewrite ev; cbn; tauto.
    - intros cl hcl t hti hkd.
      destruct (@claimsD_terms Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base (map to_F (aDX a)) ppF usF (dGX n1 ell base) (dTX n1)
                  (map to_F (dt_th1 T ++ dt_th T)) (map to_F (dt_th2 T)) (map to_F (dt_rz T)) (map to_F (dt_rt T))
                  ltac:(rewrite length_map, length_app; lia) ltac:(rewrite length_map; exact h2) ltac:(rewrite length_map; exact hz)
                  ltac:(rewrite length_map; exact ht) (dGX_len n1 ell base) (dTX_len n1) cl t hcl hti)
        as [[ev _] | [[ev _] | [[ev er] | [[ev er] | [ev er]]]]]; rewrite ev in hkd |- *; cbn in hkd; try discriminate;
        rewrite er; reflexivity.
  Qed.

  (* the codeword of a slot vector at an opened column is the combination of the opened entries *)
  Lemma dvec_ok : forall T om n J (Xe : nat -> nat -> xf) v (R : nat -> Prop),
    (forall i j, R i -> In j J -> to_F (Xe i j) = pevalF2 (PFD i) (pwF (to_F om) j)) ->
    (forall iw, In iw (mcbX n1 ell lo1 kd v) -> R (fst iw)) ->
    (forall iw, In iw (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v) -> R (fst iw)) ->
    forall j, In j J ->
    xeqb (xenc_at om n (xencv (fst om) n (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v))
                  (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v) j)
         (xxw Xe (mcbX n1 ell lo1 kd v) (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v)
              (nth 0 (dt_cl T) xzero) j) = true.
  Proof.
    intros T om n J Xe v R hX hm hc j hj.
    apply xeqb_spec; [apply xenc_at_reduced | apply xadd_reduced |].
    rewrite (to_F_enc_at om n _ _ j eq_refl). unfold ReedSolomon.rs_enc, vecT, vecD, msD, usD.
    cbn [dc dkp f1T front0].
    rewrite to_F_padd, to_F_pscale, !combD_msum.
    rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
            (@eval_pscale Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
    rewrite (ExecBackO.enc_comb Xe om J PFD (mcbX n1 ell lo1 kd v)),
            (ExecBackO.enc_comb Xe om J PFD (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v));
      try exact hj; try (intros iw hiw j' hj'; apply hX; [first [apply hm; exact hiw | apply hc; exact hiw] | exact hj']).
    unfold xxw. rewrite to_F_add, to_F_mul. reflexivity.
  Qed.

  Lemma dcb_rows : forall T, List.length (dt_th T) = ell -> List.length (dt_th1 T) = n1 -> List.length (dt_th2 T) = n1 ->
    List.length (dt_rz T) = m -> List.length (dt_rt T) = n1 ->
    forall v iw, In iw (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < SO)%nat) /\ ((v = 3 \/ v = 4 \/ v = 5)%nat -> (SO <= fst iw < SO + 11)%nat).
  Proof.
    intros T h0 h1 h2 hz ht v iw h. unfold xcbk, kindD in h.
    destruct (Nat.leb_spec 3 v) as [hv3 | hv3].
    - destruct h as [<- | []]. cbn [fst]. unfold frowD, rS, rE, rMd.
      split; [lia |]. intro hv. destruct (Nat.eqb v 3); [lia |]. destruct (Nat.eqb v 4); lia.
    - destruct (xgbatch_rows _ _ _ _ h) as (cl & t & hcl & hti & hsl & hrw).
      assert (hok : @term_ok Fq2 n1 ell lo1 SO kd (ExecClaims.tF t)).
      { apply (@claimsD_terms Fq2 fzero fone fadd fmul fsub fopp ftg n1 ell lo1 SO kd base (map to_F (aDX a)) ppF usF
                 (dGX n1 ell base) (dTX n1) (map to_F (dt_th1 T ++ dt_th T)) (map to_F (dt_th2 T)) (map to_F (dt_rz T)) (map to_F (dt_rt T))
                 ltac:(rewrite length_map, length_app; lia) ltac:(rewrite length_map; exact h2) ltac:(rewrite length_map; exact hz)
                 ltac:(rewrite length_map; exact ht) (dGX_len n1 ell base) (dTX_len n1) (map ExecClaims.tF cl)).
        + rewrite <-(clsF_T T h0 h1 h2 hz ht). cbv beta. apply in_map. exact hcl.
        + apply in_map. exact hti. }
      destruct t as [[[sl rw0] c0] lv0]. cbn in hsl, hrw, hok. rewrite hrw.
      unfold term_ok in hok. cbn [tslot trow] in hok.
      split; [| intro hv; lia].
      intro hv. destruct hok as [(_ & d & j & hd & hj & ->) | [(_ & d & j & hd & hj & ->) | [(e3 & _) | [(e3 & _) | (e3 & _)]]]];
        try lia; unfold SOX, rwX, rwD in *; nia.
  Qed.

  Lemma dmcb_rows : forall v iw, In iw (mcbX n1 ell lo1 kd v) ->
    ((v = 1 \/ v = 2)%nat -> (fst iw < SO)%nat) /\ ((v = 3 \/ v = 4 \/ v = 5)%nat -> (SO <= fst iw < SO + 11)%nat).
  Proof.
    intros v iw h. split; intro hv.
    - destruct hv as [-> | ->]; cbn in h; destruct h as [<- | [<- | []]]; cbn [fst]; unfold SOX; lia.
    - destruct hv as [-> | [-> | ->]]; cbn in h; destruct h as [<- | [<- | []]]; cbn [fst]; lia.
  Qed.

  Local Notation fD := (fun T => dfmk n1 ell lo1 kd (dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T) T).

  Theorem dopen_complete : forall T vals,
    List.length (dt_th T) = ell -> List.length (dt_th1 T) = n1 -> List.length (dt_th2 T) = n1 ->
    List.length (dt_rz T) = m -> List.length (dt_rt T) = n1 -> List.length (dt_kp T) = (kd + 6)%nat ->
    (forall j, In j (map Z.to_nat (dt_JB T)) -> (j < nB)%nat) -> (forall j, In j (map Z.to_nat (dt_JS T)) -> (j < nS)%nat) ->
    wf_dparts n1 ell lo1 kd base kB nB nqB kS nS nqS (dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T) ->
    map to_F vals = map (@gtval Fq2 fzero fadd fmul PFD kindD (LtT T)) (claimsT T) ->
    openX n1 ell lo1 kd base kB nB kS nS omB omS pplain a us (fD T) vals = true.
  Proof.
    intros T vals h0 h1 h2 hz ht hkp hJB hJS hwf hvals.
    destruct hwf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hv1 & hv2 & hve & hvm & hvs & hpB & hpS & _ & _).
    cbn [dparts_of pvS1 pvS2 pvSe pvSm pvSs ppvB ppvS] in hv1, hv2, hve, hvm, hvs, hpB, hpS.
    unfold openX, xaccO. rewrite !andb_true_iff. split; [split |].
    - (* the batched value check *)
      apply xeqb_spec; [apply xfsum_reduced | apply xadd_reduced |].
      rewrite to_F_fsum, map_map, to_F_add, to_F_mul, to_F_dot, hvals.
      transitivity (fsumF (map (fun v => fadd (@LogDer.dot Fq2 fzero fadd fmul (map to_F (msD n1 ell lo1 kd bBx bSx v))
                                                           (map to_F (LD n1 ell lo1 kd base pplain a us (f1T T) v)))
                                              (fmul (to_F (nth 0 (dt_cl T) xzero))
                                                    (@LogDer.dot Fq2 fzero fadd fmul (map to_F (usD n1 ell lo1 kd base pplain a us bBx bSx (f1T T) v))
                                                           (map to_F (LD n1 ell lo1 kd base pplain a us (f1T T) v)))))
                               [1; 2; 3; 4; 5]%nat)).
      { apply fsum_ext'. intros v hv'.
        replace (dub (fD T) v) with (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v)
          by (cbn in hv'; destruct hv' as [<- | [<- | [<- | [<- | [<- | []]]]]]; reflexivity).
        change (xLk kindD (LtX lo1 (fD T)) (dkp (fD T)) (clsX n1 ell lo1 kd base pplain a us (fD T)) v)
          with (LD n1 ell lo1 kd base pplain a us (f1T T) v).
        unfold vecT, vecD. rewrite to_F_dot, to_F_padd, to_F_pscale.
        rewrite (@dot_padd_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field),
                (@dot_pscale_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). reflexivity. }
      rewrite <-ExecFold.fsum_map_add, (@fsum_map_mul_l Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
      rewrite (dbatch T h0 h1 h2 hz ht hkp).
      assert (hmu : to_F (dmu (fD T))
                    = fsumF (map (fun v => @LogDer.dot Fq2 fzero fadd fmul (map to_F (msD n1 ell lo1 kd bBx bSx v))
                                                       (map to_F (LD n1 ell lo1 kd base pplain a us (f1T T) v))) [1; 2; 3; 4; 5]%nat)).
      { cbn [dfmk dmu dparts_of pmu]. unfold muD. rewrite to_F_fsum, map_map.
        apply fsum_ext'. intros v _. apply to_F_dot. }
      rewrite hmu. cbn [dfmk dc]. reflexivity.
    - (* the big matrix *)
      unfold xmacc. cbv zeta. rewrite !andb_true_iff. split; [split |].
      + apply Nat.leb_le. destruct hpB as [ev _]. exact (Nat.eq_le_incl _ _ ev).
      + apply forallb_forall. intros j hj. apply xeqb_spec; [apply xenc_at_reduced | apply xadd_reduced |].
        cbn [dfmk dpvB dgB dparts_of ppvB].
        rewrite (to_F_enc_at _ _ _ _ j eq_refl). unfold ReedSolomon.rs_enc, pvBD. rewrite to_F_padd, !combD_msum.
        rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
        assert (hX : forall i j', (i < SO)%nat -> In j' (map Z.to_nat (dt_JB T)) ->
                       to_F (dXe (fD T) i j') = pevalF2 (PFD i) (pwF (to_F (bx omB)) j'))
          by (intros i j' hi hj'; apply XeBD; [exact hj' | apply hJB, hj' | exact hi]).
        rewrite (ExecBackO.enc_comb (dXe (fD T)) (bx omB) (map Z.to_nat (dt_JB T)) PFD
                   [((kd * rw + 4)%nat, xone); ((kd * rw + 5)%nat, xtg)]) by
          (first [exact hj | intros iw hiw j' hj'; apply hX; [cbn in hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; unfold SOX; lia | exact hj']]).
        rewrite (ExecBackO.enc_comb (dXe (fD T)) (bx omB) (map Z.to_nat (dt_JB T)) PFD
                   (combine (rwsBX n1 ell lo1 kd) (firstn (kd * rw + 4) (dt_gB T)))) by
          (first [exact hj | intros [i w] hiw j' hj'; apply hX;
                    [apply in_combine_l in hiw; unfold rwsBX in hiw; apply in_seq in hiw; cbn [fst]; unfold SOX; lia | exact hj']]).
        unfold xpi, xmpBX. rewrite ExecBackO.xwsum_combine. cbn [xwsum fst snd dfmk dgB].
        rewrite !to_F_add, !to_F_mul, to_F_one, to_F_zero. field.
      + apply forallb_forall. intros v hv'. apply andb_true_iff. split.
        * apply Nat.leb_le. cbn in hv'. destruct hv' as [<- | [<- | []]];
            [destruct hv1 as [ev _] | destruct hv2 as [ev _]]; cbn [dfmk dub]; exact (Nat.eq_le_incl _ _ ev).
        * apply forallb_forall. intros j hj.
          replace (dub (fD T) v) with (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v)
            by (cbn in hv'; destruct hv' as [<- | [<- | []]]; reflexivity).
          change (xcbk kindD (frowD SO) (dkp (fD T)) (clsX n1 ell lo1 kd base pplain a us (fD T)) v)
            with (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v).
          cbn [dfmk dc].
          apply (dvec_ok T (bx omB) nB (map Z.to_nat (dt_JB T)) (dXe (fD T)) v (fun i => (i < SO)%nat)); [| | | exact hj].
          -- intros i j' hi hj'. apply XeBD; [exact hj' | apply hJB, hj' | exact hi].
          -- intros iw hiw. apply (dmcb_rows v iw hiw). cbn in hv'. lia.
          -- intros iw hiw. apply (dcb_rows T h0 h1 h2 hz ht v iw hiw). cbn in hv'. lia.
    - (* the small matrix *)
      unfold xmacc. cbv zeta. rewrite !andb_true_iff. split; [split |].
      + apply Nat.leb_le. destruct hpS as [ev _]. exact (Nat.eq_le_incl _ _ ev).
      + apply forallb_forall. intros j hj. apply xeqb_spec; [apply xenc_at_reduced | apply xadd_reduced |].
        cbn [dfmk dpvS dgS dparts_of ppvS].
        rewrite (to_F_enc_at _ _ _ _ j eq_refl). unfold ReedSolomon.rs_enc, pvSD. rewrite to_F_padd, !combD_msum.
        rewrite (@eval_padd Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field).
        assert (hX : forall i j', (SO <= i < SO + 11)%nat -> In j' (map Z.to_nat (dt_JS T)) ->
                       to_F (dXe (fD T) i j') = pevalF2 (PFD i) (pwF (to_F (bx omS)) j'))
          by (intros i j' hi hj'; apply XeSD; [exact hj' | apply hJS, hj' | exact hi]).
        rewrite (ExecBackO.enc_comb (dXe (fD T)) (bx omS) (map Z.to_nat (dt_JS T)) PFD
                   [((SO + 9)%nat, xone); ((SO + 10)%nat, xtg)]) by
          (first [exact hj | intros iw hiw j' hj'; apply hX; [cbn [In] in hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; lia | exact hj']]).
        rewrite (ExecBackO.enc_comb (dXe (fD T)) (bx omS) (map Z.to_nat (dt_JS T)) PFD
                   (combine (rwsSX n1 ell lo1 kd) (firstn 9 (dt_gS T)))) by
          (first [exact hj | intros [i w] hiw j' hj'; apply hX;
                    [apply in_combine_l in hiw; unfold rwsSX in hiw; apply in_map_iff in hiw; destruct hiw as (i0 & <- & hi0);
                     apply in_seq in hi0; cbn [fst]; lia | exact hj']]).
        unfold xpi, xmpSX. rewrite ExecBackO.xwsum_combine. cbn [xwsum fst snd dfmk dgS].
        rewrite !to_F_add, !to_F_mul, to_F_one, to_F_zero. field.
      + apply forallb_forall. intros v hv'. apply andb_true_iff. split.
        * apply Nat.leb_le. cbn in hv'. destruct hv' as [<- | [<- | [<- | []]]];
            [destruct hvs as [ev _] | destruct hve as [ev _] | destruct hvm as [ev _]]; cbn [dfmk dub]; exact (Nat.eq_le_incl _ _ ev).
        * apply forallb_forall. intros j hj.
          replace (dub (fD T) v) with (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v)
            by (cbn in hv'; destruct hv' as [<- | [<- | [<- | []]]]; reflexivity).
          change (xcbk kindD (frowD SO) (dkp (fD T)) (clsX n1 ell lo1 kd base pplain a us (fD T)) v)
            with (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v).
          cbn [dfmk dc].
          apply (dvec_ok T (bx omS) nS (map Z.to_nat (dt_JS T)) (dXe (fD T)) v (fun i => (SO <= i < SO + 11)%nat)); [| | | exact hj].
          -- intros i j' hi hj'. apply XeSD; [exact hj' | apply hJS, hj' | exact hi].
          -- intros iw hiw. apply (dmcb_rows v iw hiw). cbn in hv'. lia.
          -- intros iw hiw. apply (dcb_rows T h0 h1 h2 hz ht v iw hiw). cbn in hv'. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* step B: the shape of the prover's output *)

  Theorem dwf : forall T,
    List.length (dt_th T) = ell -> List.length (dt_th1 T) = n1 -> List.length (dt_th2 T) = n1 ->
    List.length (dt_rz T) = m -> List.length (dt_rt T) = n1 ->
    Forall2 msg_ok (dt_mG T) (dGX n1 ell base) -> Forall reduced (dt_finG T) -> List.length (dt_finG T) = S kd ->
    Forall2 msg_ok (dt_mT T) (dTX n1) -> Forall reduced (dt_finT T) -> List.length (dt_finT T) = 3%nat ->
    (exists c c', get_I c (sb "pcs.J.big") nqB (Z.of_nat nB) = Some (dt_JB T, c')) ->
    (exists c c', get_I c (sb "pcs.J.small") nqS (Z.of_nat nS) = Some (dt_JS T, c')) ->
    wf_dparts n1 ell lo1 kd base kB nB nqB kS nS nqS (dparts_of n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T).
  Proof.
    intros T h0 h1 h2 hz ht mGok finGok lfG mTok finTok lfT hJB hJS.
    pose proof Hp as hp'. destruct hp' as (hkB & hkS & hnB & h1B & hnS & h1S & hmr & hNC & _ & _).
    pose proof Hk as hk'. destruct hk' as (_ & _ & hsB & _ & _ & _ & hsS).
    destruct msgsBD_shape as [mB1 mB2]. destruct msgsSD_shape as [mS1 mS2].
    assert (rowB : forall i, (i < SO)%nat -> List.length (nth i AMD []) = kB).
    { intros i hi. rewrite AMD_eq, app_nth1 by lia. rewrite Forall_forall in mB2. rewrite mB2, hkB; [reflexivity |].
      apply nth_In. lia. }
    assert (rowS : forall i, (SO <= i < SO + 11)%nat -> List.length (nth i AMD []) = kS).
    { intros i hi. rewrite AMD_eq, app_nth2 by lia. rewrite mB1.
      rewrite Forall_forall in mS2. rewrite mS2, hkS; [reflexivity |]. apply nth_In. lia. }
    assert (hcomb : forall cb, combD bBx bSx cb = fcomb (fun i => nth i AMD []) cb) by reflexivity.
    assert (hvec : forall v kk, (forall i, In i (map fst (mcbX n1 ell lo1 kd v)) -> List.length (nth i AMD []) = kk) ->
              mcbX n1 ell lo1 kd v <> [] ->
              Forall (fun iw => (List.length (nth (fst iw) AMD []) <= kk)%nat)
                     (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v) ->
              msg_ok (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v) kk).
    { intros v kk hm hne hu. unfold vecT, vecD. split.
      + rewrite xpadd_length. unfold xpscale. rewrite length_map. unfold msD, usD. cbn [dkp f1T front0] in hu |- *.
        rewrite !hcomb.
        assert (e1 : List.length (fcomb (fun i => nth i AMD []) (mcbX n1 ell lo1 kd v)) = kk).
        { apply fcomb_length_eq.
          + apply Forall_forall. intros iw hiw. rewrite hm; [lia | apply in_map, hiw].
          + assert (hx : exists iw, In iw (mcbX n1 ell lo1 kd v)).
            { clear -hne. destruct (mcbX n1 ell lo1 kd v) as [| iw r]; [contradiction | exists iw; left; reflexivity]. }
            destruct hx as (iw & hiw). exists iw. split; [exact hiw |]. apply hm, in_map, hiw. }
        pose proof (fcomb_length_le (fun i => nth i AMD []) _ _ hu). lia.
      + apply xpadd_reduced; [unfold msD; rewrite hcomb; apply fcomb_reduced | apply xpscale_reduced]. }
    assert (hus : forall v, (v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5)%nat ->
              Forall (fun iw => (List.length (nth (fst iw) AMD []) <= (if Nat.leb 3 v then kS else kB))%nat)
                     (xcbk kindD (frowD SO) (dt_kp T) (clsPD n1 ell lo1 kd base pplain a us (f1T T)) v)).
    { intros v hv. apply Forall_forall. intros iw hiw. destruct (dcb_rows T h0 h1 h2 hz ht v iw hiw) as [r12 r345].
      destruct (Nat.leb_spec 3 v); [rewrite rowS by (apply r345; lia) | rewrite rowB by (apply r12; lia)]; lia. }
    assert (hmv : forall v, (v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5)%nat ->
              msg_ok (vecT n1 ell lo1 lo2 kd base nB nS omB omS pplain off a us s e E k T v) (if Nat.leb 3 v then kS else kB)).
    { intros v hv. apply hvec; [| destruct hv as [-> | [-> | [-> | [-> | ->]]]]; discriminate | apply hus, hv].
      intros i hi. destruct hv as [-> | [-> | [-> | [-> | ->]]]]; cbn in hi; cbn [Nat.leb];
        [apply rowB | apply rowB | apply rowS | apply rowS | apply rowS]; unfold SOX in *; lia. }
    unfold wf_dparts. cbn [dparts_of proot_big proot_small pG pmG pzG pmT pzT pmu pvS1 pvS2 pvSe pvSm pvSs ppvB ppvS pcolsB pcolsS].
    destruct hsB as [hsB1 hsB2]. destruct hsS as [hsS1 hsS2].
    split; [apply broot_length; [exact h1B | rewrite <-hnB; exact hsB1 | exact hnB] |].
    split; [apply broot_length; [exact h1S | rewrite <-hnS; exact hsS1 | exact hnS] |].
    split; [reflexivity |].
    split; [unfold GD, mtotal; repeat constructor; apply xadd_reduced |].
    split; [exact mGok |].
    split; [rewrite length_firstn; destruct (dt_finG T); cbn in lfG |- *; lia |].
    split; [apply red_firstn_tl; exact finGok |].
    split; [exact mTok |].
    split; [destruct (dt_finT T) as [| f0 [| f1 [| f2 fs]]]; cbn in lfT |- *; lia |].
    split; [apply red_firstn_tl; exact finTok |].
    split; [unfold muD; apply xfsum_reduced |].
    split; [exact (hmv 1%nat ltac:(lia)) |]. split; [exact (hmv 2%nat ltac:(lia)) |].
    split; [exact (hmv 4%nat ltac:(lia)) |]. split; [exact (hmv 5%nat ltac:(lia)) |]. split; [exact (hmv 3%nat ltac:(lia)) |].
    split.
    { unfold pvBD. split.
      + rewrite xpadd_length, !hcomb.
        assert (e1 : List.length (fcomb (fun i => nth i AMD []) [((kd * rw + 4)%nat, xone); ((kd * rw + 5)%nat, xtg)]) = kB).
        { apply fcomb_length_eq;
            [apply Forall_forall; intros iw hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; rewrite rowB by (unfold SOX; lia); lia |].
          exists ((kd * rw + 4)%nat, xone). split; [left; reflexivity | cbn [fst]; apply rowB; unfold SOX; lia]. }
        assert (e2 : (List.length (fcomb (fun i => nth i AMD []) (combine (rwsBX n1 ell lo1 kd) (firstn (kd * rw + 4) (dgB (f1T T))))) <= kB)%nat).
        { apply fcomb_length_le, Forall_forall. intros [i w] hin. apply in_combine_l in hin. cbn [fst].
          unfold rwsBX in hin. apply in_seq in hin. rewrite rowB by (unfold SOX; lia). lia. }
        lia.
      + apply xpadd_reduced; rewrite hcomb; apply fcomb_reduced. }
    split.
    { unfold pvSD. split.
      + rewrite xpadd_length, !hcomb.
        assert (e1 : List.length (fcomb (fun i => nth i AMD []) [((SO + 9)%nat, xone); ((SO + 10)%nat, xtg)]) = kS).
        { apply fcomb_length_eq;
            [apply Forall_forall; intros iw hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; rewrite rowS by lia; lia |].
          exists ((SO + 9)%nat, xone). split; [left; reflexivity | cbn [fst]; apply rowS; lia]. }
        assert (e2 : (List.length (fcomb (fun i => nth i AMD []) (combine (rwsSX n1 ell lo1 kd) (firstn 9 (dgS (f1T T))))) <= kS)%nat).
        { apply fcomb_length_le, Forall_forall. intros [i w] hin. apply in_combine_l in hin. cbn [fst].
          unfold rwsSX in hin. apply in_map_iff in hin. destruct hin as (i0 & <- & hi0). apply in_seq in hi0.
          rewrite rowS by lia. lia. }
        lia.
      + apply xpadd_reduced; rewrite hcomb; apply fcomb_reduced. }
    split.
    { split; [rewrite !length_map; exact (drawn_count _ _ _ _ _ hnB hJB) |].
      apply Forall_map. pose proof (drawn_indices _ _ _ _ _ hnB hJB) as hj.
      rewrite Forall_forall in hj |- *. intros j hjin. constructor; [| constructor].
      apply bitem_ok; [exact hnB | reflexivity | exact hsB1 | exact hsB2 | exact mB1 | exact (hj j hjin)]. }
    { split; [rewrite !length_map; exact (drawn_count _ _ _ _ _ hnS hJS) |].
      apply Forall_map. pose proof (drawn_indices _ _ _ _ _ hnS hJS) as hj.
      rewrite Forall_forall in hj |- *. intros j hjin. constructor; [| constructor].
      apply bitem_ok; [exact hnS | reflexivity | exact hsS1 | exact hsS2 | exact mS1 | exact (hj j hjin)]. }
  Qed.

End DOpen.

(* ---------------------------------------------------------------------- *)
(* the theorem *)

Lemma xred_of_reduced : forall x, reduced x -> xred x = true.
Proof.
  intros [x0 x1] [h0 h1]. cbn [fst snd] in *. unfold xred. cbn [fst snd].
  rewrite !andb_true_iff. repeat split; first [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.

Lemma msgs_reduced : forall ms ds, Forall2 msg_ok ms ds -> Forall reduced (List.concat ms).
Proof.
  intros ms ds h. induction h as [| ev d ms ds [_ hr] _ ih]; [constructor |].
  cbn [List.concat]. apply Forall_app. split; assumption.
Qed.

Lemma msgs_lengths : forall ms ds, Forall2 msg_ok ms ds -> map (@List.length xf) ms = ds.
Proof. intros ms ds h. induction h as [| ev d ms ds [hl _] _ ih]; [reflexivity | cbn; rewrite hl, ih; reflexivity]. Qed.

Lemma dshape_ok : forall n1 ell lo1 kd base kB nB nqB kS nS nqS P,
  wf_dparts n1 ell lo1 kd base kB nB nqB kS nS nqS P -> dshape_front n1 ell kd base P = true.
Proof.
  intros n1 ell lo1 kd base kB nB nqB kS nS nqS P
    (_ & _ & hG1 & hG2 & hmG & hzG1 & hzG2 & hmT & hzT1 & hzT2 & hmu & [_ h1] & [_ h2] & [_ h3] & [_ h4] & [_ h5] & [_ h6] & [_ h7] & _).
  unfold dshape_front. cbv zeta.
  rewrite hG1, hzG1, hzT1, !Nat.eqb_refl, (msgs_lengths _ _ hmG), (msgs_lengths _ _ hmT).
  destruct (list_eq_dec Nat.eq_dec (dGX n1 ell base) (dGX n1 ell base)) as [_ | ne]; [| contradiction].
  destruct (list_eq_dec Nat.eq_dec (dTX n1) (dTX n1)) as [_ | ne]; [| contradiction].
  rewrite !andb_true_r. apply forallb_forall. intros x hx. apply xred_of_reduced.
  assert (hall : Forall reduced (pG P ++ List.concat (pmG P) ++ pzG P ++ List.concat (pmT P) ++ pzT P ++ [pmu P] ++ pvS1 P ++ pvS2 P
                                 ++ pvSs P ++ pvSe P ++ pvSm P ++ ppvB P ++ ppvS P)).
  { repeat (apply Forall_app; split); try assumption; try (eapply msgs_reduced; eassumption). constructor; [exact hmu | constructor]. }
  rewrite Forall_forall in hall. apply hall, hx.
Qed.

Section DFinal.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).
  Variables (s e : list Z) (E : list (list Z)).
  Variable k : dcoins.

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.

  (* Completeness of the decryption proof: for parameters and coins of the right shapes and a witness
     (s, e, E) of the relation, if the extracted prover returns proof bytes, the extracted verifier
     accepts them. The prover returns no proof only when rho_G or rho_T is zero. *)
  Theorem xdec_complete :
    dpok n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS ->
    dcok n1 ell lo1 lo2 kd base nB nqB nS nqS k ->
    dwshape n1 ell s e E ->
    dvalid n1 ell kd base pplain off a b us ts s e E ->
    (1 <= n1)%nat -> (2 * base + 1 <= DMAX)%nat ->
    List.length b = N -> List.length ts = tau -> Forall (fun l => List.length l = N) ts ->
    forall prf, xdec_prove n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS tag pplain off a b us ts s e E k = Some prf ->
    xdec_verify_bytes n1 ell lo1 kd base kB nB nqB kS nS nqS omB omS tag pplain off a b us ts prf = true.
  Proof.
    intros hp hk hw hv hn1 hdmax hb hts htl prf H.
    unfold xdec_prove in H.
    destruct (xdec_prove_parts n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS tag pplain off a b us ts s e E k) as [P |] eqn:eP;
      cbn [option_map] in H; [| discriminate]. injection H as <-.
    (* the transcript *)
    destruct (dprove_transcript n1 ell lo1 lo2 kd base nB nqB nS nqS omB omS tag pplain off a b us ts s e E k P eP) as [T hT].
    destruct hT as (hP & hdr & hnG & hnT & (c0 & c1 & eG) & (c2 & c3 & eT) & hfront).
    unfold ddrawn in hdr. cbv zeta in hdr.
    destruct hdr as (dth & dth1 & dth2 & dtz & dkG & drG & dtt & dkT & drT & dkp & dcl & dgB & dgS & dJB & dJS).
    assert (gl : forall nm n x, (exists c c', get_F c (sb nm) n = Some (x, c')) -> List.length x = n)
      by (intros nm n x (c & c' & h'); exact (proj1 (get_F_shape _ _ _ _ _ h'))).
    apply gl in dth, dth1, dth2, dtz, dkG, drG, dtt, dkT, drT, dkp.
    pose proof hw as (hE1 & hE2 & hs & he).
    pose proof hp as (_ & _ & hnB & h1B & hnS & h1S & _ & _ & _ & hbase).
    pose proof hk as (_ & _ & _ & hmask & _).
    pose proof hv as (hts' & hte' & _).
    (* the sumcheck layer *)
    destruct (dderive n1 ell kd base pplain off b ts s e E k hn1 hbase hdmax (conj hE1 hE2) hs he hmask
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ c0 c1 c2 c3 hb hts htl hts' hte' dth dth1 dth2 dtz dkG drG dtt dkT drT hnG hnT eG eT)
      as (g1 & g2 & eD & hg1 & hg2 & lrz & lrt & hfG & hfT).
    (* the shape of the output, and the parse *)
    assert (pG1 : forall d, In d (dGX n1 ell base) -> (1 <= d)%nat)
      by (intros d hd; unfold dGX in hd; apply in_map_iff in hd; destruct hd as (i & <- & _); destruct (Nat.eqb _ _); lia).
    assert (pT1 : forall d, In d (dTX n1) -> (1 <= d)%nat)
      by (intros d hd; unfold dTX in hd; apply in_map_iff in hd; destruct hd as (i & <- & _); destruct (Nat.eqb _ _); lia).
    destruct (sc_loop_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pG1 eG) as [mGok finGok].
    destruct (sc_loop_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pT1 eT) as [mTok finTok].
    assert (hdG : dGX n1 ell base <> [])
      by (intro ec; pose proof (f_equal (@List.length nat) ec) as e'; rewrite (dGX_len n1 ell base) in e'; cbn in e'; lia).
    assert (hdT : dTX n1 <> [])
      by (intro ec; pose proof (f_equal (@List.length nat) ec) as e'; rewrite (dTX_len n1) in e'; cbn in e'; lia).
    assert (lfG : List.length (dt_finG T) = S kd).
    { rewrite (sc_loop_fin_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdG eG).
      unfold tablesG, tmaskG, a_dig. cbn [List.length]. rewrite !length_map, length_seq, length_firstn, hmask. unfold n_maskD. lia. }
    assert (lfT : List.length (dt_finT T) = 3%nat) by (rewrite (sc_loop_fin_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hdT eT); reflexivity).
    pose proof (dwf n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS omB omS pplain off a us s e E k hp hk hw T
                  dth dth1 dth2 lrz lrt mGok finGok lfG mTok finTok lfT dJB dJS) as hwf.
    rewrite <-hP in hwf.
    unfold xdec_verify_bytes. rewrite (dparse_ser n1 ell lo1 kd base kB nB nqB kS nS nqS P hwf).
    unfold xdec_verify. rewrite (hfront (dshape_ok _ _ _ _ _ _ _ _ _ _ _ _ hwf)).
    (* the Merkle paths *)
    pose proof hk as (_ & _ & [hsB _] & _ & _ & _ & [hsS _]).
    assert (iB := drawn_indices _ _ _ _ _ hnB dJB). assert (iS := drawn_indices _ _ _ _ _ hnS dJS).
    assert (mB : merkle_ok [proot_big P] (map Z.to_nat (dt_JB T)) (pcolsB P) = true).
    { rewrite hP. cbn [dparts_of proot_big pcolsB].
      pose proof (merkle_ok_prover nB [btBD lo1 kd base nB omB off E k] (map Z.to_nat (dt_JB T))
                    ltac:(constructor; [apply good_commit; [exact hnB | exact hsB] | constructor]) iB) as hm.
      cbn [map] in hm. exact hm. }
    assert (mS : merkle_ok [proot_small P] (map Z.to_nat (dt_JS T)) (pcolsS P) = true).
    { rewrite hP. cbn [dparts_of proot_small pcolsS].
      pose proof (merkle_ok_prover nS [btSD lo2 nS omS s e k] (map Z.to_nat (dt_JS T))
                    ltac:(constructor; [apply good_commit; [exact hnS | exact hsS] | constructor]) iS) as hm.
      cbn [map] in hm. exact hm. }
    rewrite mB, mS. cbn [negb andb].
    (* the back end: lengths, the sumcheck layer, the opening *)
    unfold xdec_back. apply andb_true_iff. split.
    { unfold dlengths_ok, dfmk. cbn [ExecDec.drz ExecDec.drt ExecDec.dth2 ExecDec.dth1 ExecDec.dth].
      rewrite lrz, lrt, dth2, dth1, dth, !Nat.eqb_refl. reflexivity. }
    assert (eDX : derivedX n1 ell kd base pplain off b ts (dfmk n1 ell lo1 kd P T)
                  = Some ([VDx (bx pplain) (bx off) (map (map bx) ts) (dt_th T) (dt_th1 T); VKx (map bx b) (dt_th2 T)] ++
                          firstn kd (tl (dt_finG T)) ++ firstn 2 (tl (dt_finT T)) ++ [g1; g2])).
    { unfold derivedX, bDX, tsX, dfmk.
      cbn [ExecDec.dth ExecDec.dth1 ExecDec.dth2 ExecDec.dtz ExecDec.dkG ExecDec.drz ExecDec.dtt ExecDec.dkT ExecDec.drt
           ExecDec.dGG ExecDec.dGT ExecDec.dmG ExecDec.dmT ExecDec.dzG ExecDec.dzT].
      rewrite hP. cbn [dparts_of pG pmG pmT pzG pzT]. exact eD. }
    rewrite eDX.
    rewrite hP. rewrite hP in hwf.
    apply (dopen_complete n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS omB omS pplain off a us s e E k hp hk hw T _
             dth dth1 dth2 lrz lrt dkp ltac:(rewrite Forall_forall in iB; exact iB) ltac:(rewrite Forall_forall in iS; exact iS) hwf).
    symmetry.
    exact (dlayout n1 ell lo1 lo2 kd base kB nB nqB kS nS nqS omB omS pplain off a b us ts s e E k hp hk hw hv
             (dt_th T) (dt_th1 T) (dt_th2 T) (dt_tz T) (dt_rz T) (dt_tt T) (dt_rt T) (dt_finG T) (dt_finT T) g1 g2
             dth dth1 dth2 lrz lrt lfG lfT hts htl hfG hfT hg1 hg2).
  Qed.

End DFinal.
