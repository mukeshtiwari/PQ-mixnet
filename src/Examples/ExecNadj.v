(* The negacyclic adjoint nadj (Negacyclic.v) as executable code, in O(N log N).

   xnadj_slow is the direct definition (N^2 products). xnadj computes the same values with three NTTs
   (zenc, ExecFFT.v) and a pointwise product (NttInverse.v: eval_nadj, ntt_inverse):

     A_j = a(z_j^-1),  P_j = rho(z_j),  z_j = psi * omega^j  (j < N),
     result_i = N^-1 * psi^-i * sum_j A_j P_j omega^(-ij).

   psi is computed from q; that psi^N = -1, that omega = psi^2 has no power 1 below N, and that the
   computed N^-1 is an inverse are checked at run time, and if a check fails xnadj falls back to
   xnadj_slow. So to_F_nadj holds without hypotheses. *)

From Stdlib Require Import Utf8 ZArith Zpow_facts List Lia Bool PeanoNat Arith setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots Counting LogDer Negacyclic ReedSolomon NttInverse.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecFFT ExecOpen.
Import ListNotations.

Add Field fieldF2nadj : (@field_theory_for_stdlib_tactic Fq2 eq fzero fone fopp fadd fmul fsub finv fdiv Fq2_field).

Local Notation pwF := (@Negacyclic.pw Fq2 fone fmul).
Local Notation pevalF := (@PolyRoots.eval Fq2 fzero fadd fmul).
Local Notation nadjF := (@Negacyclic.nadj Fq2 fadd fmul fopp).
Local Notation nFF := (@LogDer.nF Fq2 fzero fone fadd).

(* ---------------------------------------------------------------------- *)
(* the direct definition *)

Definition xxadj (rho : list xf) : list xf :=
  match rho with
  | [] => []
  | h :: t => t ++ [xneg h]
  end.

Fixpoint xnadj_slow (a rho : list xf) : list xf :=
  match a with
  | [] => []
  | ai :: a' => xpadd (xpscale ai rho) (xxadj (xnadj_slow a' rho))
  end.

Lemma to_F_xadj : forall rho, map to_F (xxadj rho) = @xadj Fq2 fopp (map to_F rho).
Proof.
  intros [| h t]; [reflexivity |]. cbn [xxadj map Negacyclic.xadj]. rewrite map_app. cbn [map].
  rewrite to_F_neg. reflexivity.
Qed.

Lemma to_F_nadj_slow : forall a rho, map to_F (xnadj_slow a rho) = nadjF (map to_F a) (map to_F rho).
Proof.
  induction a as [| ai a ih]; intro rho; [reflexivity |].
  cbn [xnadj_slow map Negacyclic.nadj]. rewrite to_F_padd, to_F_pscale, to_F_xadj, ih. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* powers and twists over Z_q *)

Fixpoint zpw (x : Z) (k : nat) : Z :=
  match k with
  | O => 1%Z
  | S k' => (x * zpw x k') mod Q
  end.

Lemma to_F_zpw : forall x k, to_F (bz (zpw x k)) = pwF (to_F (bz x)) k.
Proof.
  intros x k; induction k as [| k ih]; cbn [zpw Negacyclic.pw]; [apply xfft_to_F_bx1 |].
  rewrite xfft_bz_mod, xfft_to_F_bx_mul, ih. reflexivity.
Qed.

(* the coefficient i of p multiplied by acc * c^i *)
Fixpoint xtw (c acc : Z) (p : list xf) : list xf :=
  match p with
  | [] => []
  | x :: p' => xmul (bz acc) x :: xtw c ((acc * c) mod Q) p'
  end.

Lemma xtw_length : forall c p acc, List.length (xtw c acc p) = List.length p.
Proof. intros c p; induction p as [| x p ih]; intro acc; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

Lemma xtw_eval : forall c p acc x,
  pevalF (map to_F (xtw c acc p)) x = fmul (to_F (bz acc)) (pevalF (map to_F p) (fmul (to_F (bz c)) x)).
Proof.
  intros c p; induction p as [| y p ih]; intros acc x; cbn [xtw map PolyRoots.eval]; [field |].
  rewrite ih, to_F_mul, xfft_bz_mod, xfft_to_F_bx_mul. field.
Qed.

Lemma xtw_nth : forall c p acc i, (i < List.length p)%nat ->
  to_F (nth i (xtw c acc p) xzero) = fmul (fmul (to_F (bz acc)) (pwF (to_F (bz c)) i)) (to_F (nth i p xzero)).
Proof.
  intros c p; induction p as [| y p ih]; intros acc i hi; [cbn in hi; lia |].
  destruct i as [| i]; cbn [xtw nth Negacyclic.pw].
  - rewrite to_F_mul. field.
  - rewrite ih by (cbn in hi; lia). rewrite xfft_bz_mod, xfft_to_F_bx_mul. field.
Qed.

Lemma xencv_length : forall w n p, List.length (xencv w n p) = n.
Proof. intros w n p. unfold xencv. unfold xf. rewrite length_combine, !xfft_zenc_length. lia. Qed.

Lemma xencv_eval : forall w n p j, (j < n)%nat ->
  to_F (nth j (xencv w n p) xzero) = pevalF (map to_F p) (pwF (to_F (bz w)) j).
Proof. intros. rewrite xencv_F by assumption. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the fast version and its run-time checks *)

Definition nadj_psi (n : nat) : Z := Zpow_mod 3 ((Q - 1) / (2 * Z.of_nat n)) Q.
Definition nadj_ninv (n : nat) : Z := Zpow_mod (Z.of_nat n) (Q - 2) Q.

Definition nadj_ok (n : nat) (psi ninv : Z) : bool :=
  Nat.ltb 0 n && Z.eqb (zpw psi n) (Q - 1) && Z.eqb ((ninv * Z.of_nat n) mod Q) 1
  && forallb (fun z => negb (Z.eqb (z mod Q) 1)) (tl (zpows ((psi * psi) mod Q)%Z n 1)).

Definition xnadj_fast (n : nat) (psi ninv : Z) (a rho : list xf) : list xf :=
  let om := ((psi * psi) mod Q)%Z in
  let omi := zpw om (n - 1) in
  let psii := zpw psi (2 * n - 1) in
  let A := xencv omi n (xtw psii 1%Z a) in
  let P := xencv om n (xtw psi 1%Z rho) in
  let E := map (fun p => xmul (fst p) (snd p)) (combine A P) in
  xtw psii ninv (xencv omi n E).

Definition xnadj (a rho : list xf) : list xf :=
  match a with
  | [] => []
  | _ :: _ =>
      let n := List.length rho in
      let psi := nadj_psi n in
      let ninv := nadj_ninv n in
      if nadj_ok n psi ninv then xnadj_fast n psi ninv a rho else xnadj_slow a rho
  end.

(* ---------------------------------------------------------------------- *)
(* correctness *)

Lemma to_F_bz_Qm1 : to_F (bz (Q - 1)) = fopp fone.
Proof.
  assert (h : fadd (to_F (bz (Q - 1))) (to_F (bz 1)) = fzero).
  { rewrite <-xfft_to_F_bx_add. replace (Q - 1 + 1)%Z with Q by lia.
    rewrite <-xfft_bz_mod, Z_mod_same_full. apply xfft_bz0. }
  rewrite xfft_to_F_bx1 in h.
  transitivity (fadd (fadd (to_F (bz (Q - 1))) fone) (fopp fone)); [field | rewrite h; field].
Qed.

Lemma to_F_bz_nat : forall n, to_F (bz (Z.of_nat n)) = nFF n.
Proof.
  induction n as [| n ih]; [apply xfft_bz0 |].
  rewrite Nat2Z.inj_succ, <-Z.add_1_l, xfft_to_F_bx_add, xfft_to_F_bx1, ih. reflexivity.
Qed.

Section Fast.
  Variables (n : nat) (psi ninv : Z).
  Hypothesis hok : nadj_ok n psi ninv = true.

  Let p := to_F (bz psi).
  Let om := to_F (bz ((psi * psi) mod Q)%Z).
  Let omi := to_F (bz (zpw ((psi * psi) mod Q)%Z (n - 1))).
  Let psii := to_F (bz (zpw psi (2 * n - 1))).

  Lemma ok_parts : (0 < n)%nat /\ zpw psi n = (Q - 1)%Z /\ ((ninv * Z.of_nat n) mod Q = 1)%Z /\
    forall z, In z (tl (zpows ((psi * psi) mod Q)%Z n 1)) -> (z mod Q <> 1)%Z.
  Proof.
    unfold nadj_ok in hok. apply andb_prop in hok as [h123 h4]. apply andb_prop in h123 as [h12 h3].
    apply andb_prop in h12 as [h1 h2].
    apply Nat.ltb_lt in h1. apply Z.eqb_eq in h2. apply Z.eqb_eq in h3.
    rewrite forallb_forall in h4.
    split; [exact h1 | split; [exact h2 | split; [exact h3 |]]].
    intros z hz e. specialize (h4 z hz). rewrite e in h4. discriminate.
  Qed.

  Lemma om_sq : om = fmul p p.
  Proof. unfold om, p. rewrite xfft_bz_mod, xfft_to_F_bx_mul. reflexivity. Qed.

  Lemma psi_n : pwF p n = fopp fone.
  Proof. destruct ok_parts as (_ & h & _). unfold p. rewrite <-to_F_zpw, h. apply to_F_bz_Qm1. Qed.

  Lemma om_n : pwF om n = fone.
  Proof.
    rewrite om_sq, (@pw_mul_base Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), psi_n. field.
  Qed.

  Lemma om_omi : fmul om omi = fone.
  Proof.
    destruct ok_parts as (hn & _). unfold omi. rewrite to_F_zpw. fold om.
    transitivity (pwF om (S (n - 1))); [reflexivity |]. replace (S (n - 1)) with n by lia. apply om_n.
  Qed.

  Lemma p_psii : fmul p psii = fone.
  Proof.
    destruct ok_parts as (hn & _). unfold psii. rewrite to_F_zpw. fold p.
    transitivity (pwF p (S (2 * n - 1))); [reflexivity |].
    replace (S (2 * n - 1)) with (n + n)%nat by lia.
    rewrite (@pw_add' Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), psi_n. field.
  Qed.

  Lemma om_prim : forall m, (0 < m < n)%nat -> pwF om m <> fone.
  Proof.
    destruct ok_parts as (hn & _ & _ & h4). intros m hm e.
    set (zs := zpows ((psi * psi) mod Q)%Z n 1).
    assert (hin : In (nth m zs 0%Z) (tl zs)).
    { unfold zs. destruct n as [| n']; [lia |]. cbn [zpows tl].
      destruct m as [| m]; [lia |]. cbn [nth]. apply nth_In. rewrite xfft_zpows_len. lia. }
    apply (h4 _ hin).
    assert (hv : to_F (bz (nth m zs 0%Z)) = to_F (bz 1)).
    { unfold zs. rewrite xfft_zpows_F by lia. fold om. rewrite e, xfft_to_F_bx1. field. }
    rewrite <-(xfft_bz_mod (nth m zs 0%Z)) in hv.
    apply xfft_bx_inj in hv; [exact hv | apply Z.mod_pos_bound, xfft_Q_pos_q |].
    assert (hQ := xfft_Q_pos_q). unfold Q in *. lia.
  Qed.

  Lemma ninv_n : fmul (to_F (bz ninv)) (nFF n) = fone.
  Proof.
    destruct ok_parts as (_ & _ & h3 & _).
    rewrite <-to_F_bz_nat, <-xfft_to_F_bx_mul, <-xfft_bz_mod, h3. apply xfft_to_F_bx1.
  Qed.

  Lemma xnadj_prod : forall a rho j, List.length rho = n -> (j < n)%nat ->
    to_F (nth j (map (fun pr : xf * xf => xmul (fst pr) (snd pr))
       (combine (xencv (zpw ((psi * psi) mod Q)%Z (n - 1)) n (xtw (zpw psi (2 * n - 1)) 1%Z a))
                (xencv ((psi * psi) mod Q)%Z n (xtw psi 1%Z rho)))) xzero)
    = pevalF (nadjF (map to_F a) (map to_F rho)) (fmul p (pwF om j)).
  Proof.
    intros a rho j hl hj.
    set (A := xencv (zpw ((psi * psi) mod Q)%Z (n - 1)) n (xtw (zpw psi (2 * n - 1)) 1%Z a)).
    set (P := xencv ((psi * psi) mod Q)%Z n (xtw psi 1%Z rho)).
    rewrite (nth_indep _ xzero ((fun pr : xf * xf => xmul (fst pr) (snd pr)) (xzero, xzero))).
    2:{ rewrite length_map. unfold xf. rewrite length_combine. unfold A, P. rewrite !xencv_length. lia. }
    rewrite (map_nth (fun pr : xf * xf => xmul (fst pr) (snd pr)) (combine A P) (xzero, xzero) j).
    rewrite (combine_nth A P j xzero xzero) by (unfold A, P; rewrite !xencv_length; reflexivity).
    cbn [fst snd]. rewrite to_F_mul. unfold A, P. rewrite !xencv_eval by exact hj. rewrite !xtw_eval.
    fold omi om psii p. rewrite xfft_to_F_bx1.
    rewrite (@eval_nadj Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n (fmul p (pwF om j)) (fmul psii (pwF omi j))).
    - field.
    - rewrite length_map. exact hl.
    - rewrite (@pw_mul_base Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), psi_n.
      rewrite (@pw_pw Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), Nat.mul_comm, <-(@pw_pw Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field), om_n, (@pw_one Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). field.
    - transitivity (fmul (fmul p psii) (pwF (fmul om omi) j)).
      + rewrite (@pw_mul_base Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). field.
      + rewrite p_psii, om_omi, (@pw_one Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). field.
  Qed.

  Theorem xnadj_fast_correct : forall a rho, a <> [] -> List.length rho = n ->
    map to_F (xnadj_fast n psi ninv a rho) = nadjF (map to_F a) (map to_F rho).
  Proof.
    intros a rho ha hl. destruct ok_parts as (hn & _).
    assert (hE := fun j => xnadj_prod a rho j hl).
    set (r := nadjF (map to_F a) (map to_F rho)) in *.
    assert (hlr : List.length r = n).
    { unfold r. destruct a as [| a0 a']; [contradiction |]. rewrite nadj_length by discriminate. rewrite length_map. exact hl. }
    unfold xnadj_fast. cbv zeta.
    set (E := map (fun pr : xf * xf => xmul (fst pr) (snd pr))
         (combine (xencv (zpw ((psi * psi) mod Q)%Z (n - 1)) n (xtw (zpw psi (2 * n - 1)) 1%Z a))
                  (xencv ((psi * psi) mod Q)%Z n (xtw psi 1%Z rho)))) in *.
    assert (hlE : List.length E = n).
    { unfold E. rewrite length_map. unfold xf. rewrite length_combine, !xencv_length. lia. }
    assert (hEm : map to_F E = map (fun j => pevalF r (fmul p (pwF om j))) (seq 0 n)).
    { apply nth_ext with (d := fzero) (d' := fzero); [rewrite !length_map, length_seq; exact hlE |].
      intros j hj. rewrite length_map in hj.
      rewrite (nth_indep (map to_F E) fzero (to_F xzero)) by (rewrite length_map; lia).
      rewrite map_nth, hE by lia.
      symmetry. rewrite (nth_indep _ fzero ((fun j => pevalF r (fmul p (pwF om j))) 0%nat)) by (rewrite length_map, length_seq; lia).
      rewrite (map_nth (fun j => pevalF r (fmul p (pwF om j)))), seq_nth by lia.
      cbn [Nat.add]. reflexivity. }
    apply nth_ext with (d := fzero) (d' := fzero).
    - rewrite length_map, xtw_length, xencv_length. symmetry. exact hlr.
    - intros i hi. rewrite length_map, xtw_length, xencv_length in hi.
      rewrite (nth_indep _ fzero (to_F xzero)) by (rewrite length_map, xtw_length, xencv_length; lia).
      rewrite map_nth.
      rewrite xtw_nth by (rewrite xencv_length; exact hi).
      rewrite xencv_eval by exact hi. rewrite hEm.
      fold psii omi.
      rewrite (@ntt_inverse Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field n p om omi r i om_n om_omi om_prim hlr hi).
      assert (hpp : fmul (pwF psii i) (pwF p i) = fone).
      { transitivity (pwF (fmul p psii) i).
        - rewrite (@pw_mul_base Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). field.
        - rewrite p_psii. apply (@pw_one Fq2 fzero fone fadd fmul fsub fdiv fopp finv Fq2_field). }
      assert (hnn := ninv_n).
      transitivity (fmul (fmul (to_F (bz ninv)) (nFF n)) (fmul (fmul (pwF psii i) (pwF p i)) (nth i r fzero))); [field |].
      rewrite hnn, hpp. field.
  Qed.
End Fast.

(* the executable adjoint computes nadj, whichever branch it takes *)
Theorem to_F_nadj : forall a rho, map to_F (xnadj a rho) = nadjF (map to_F a) (map to_F rho).
Proof.
  intros a rho. unfold xnadj. destruct a as [| a0 a']; [reflexivity |]. cbv zeta.
  destruct (nadj_ok (List.length rho) (nadj_psi (List.length rho)) (nadj_ninv (List.length rho))) eqn:e.
  - apply xnadj_fast_correct; [exact e | discriminate | reflexivity].
  - apply to_F_nadj_slow.
Qed.
