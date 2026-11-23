(* Prover side, stage 4a: the byte format. The verifier's parser reads back
   what the prover's serialiser writes (mix_deserialize . mix_serialize).

   Theorem parse_ser: for parts of the right shape (wf_parts: hashes of 32
   bytes, salts of 16, field elements and entries reduced mod q, every
   vector and message of the length the parameters fix),
     xmix_parse (ser_parts P) = Some P.
   Lemma sha256_length: SHA-256 gives 32 bytes (the roots and the path
   entries are hashes). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String.
From Examples Require Import ConcreteField ExecField ExecHash ExecVerify ExecProveBase.
Import ListNotations.
Local Open Scope list_scope.

(* ---------------------------------------------------------------------- *)
(* hashes *)

Lemma compress_length : forall hv blk, List.length (compress hv blk) = 8%nat.
Proof.
  intros hv blk. unfold compress.
  destruct (fold_left round _ _) as [[[[[[[a b] c] d] e] f] g] h]. reflexivity.
Qed.

Lemma blocks_length : forall fuel l hv, List.length hv = 8%nat -> List.length (blocks fuel l hv) = 8%nat.
Proof.
  induction fuel as [| f ih]; intros l hv h; [exact h |].
  cbn [blocks]. destruct l; [exact h |]. apply ih, compress_length.
Qed.

Lemma be_bytes_length : forall k x, List.length (be_bytes k x) = k.
Proof.
  induction k as [| k ih]; intro x; [reflexivity |].
  cbn [be_bytes]. rewrite length_app, ih. cbn. lia.
Qed.

Lemma flat_map_const_length : forall {A B : Type} (f : A -> list B) (c : nat) (l : list A),
  (forall x, List.length (f x) = c) -> List.length (flat_map f l) = (c * List.length l)%nat.
Proof.
  intros A B f c l h. induction l as [| x l ih]; [cbn; lia |].
  cbn [flat_map List.length]. rewrite length_app, h, ih. lia.
Qed.

Lemma sha256_length : forall m, List.length (sha256 m) = 32%nat.
Proof.
  intro m. unfold sha256, sha256_spec. rewrite (flat_map_const_length _ 4%nat), blocks_length; [reflexivity | reflexivity |].
  intro x. apply be_bytes_length.
Qed.

(* ---------------------------------------------------------------------- *)
(* integers *)

Lemma from_be_snoc : forall l b, from_be (l ++ [b]) = (from_be l * 256 + b)%Z.
Proof. intros l b. unfold from_be. rewrite fold_left_app. reflexivity. Qed.

Lemma from_be_be_bytes : forall k x, (0 <= x < 256 ^ Z.of_nat k)%Z -> from_be (be_bytes k x) = x.
Proof.
  induction k as [| k ih]; intros x hx.
  + cbn in hx |- *. lia.
  + cbn [be_bytes]. rewrite from_be_snoc, ih.
    - pose proof (Z.div_mod x 256 ltac:(lia)). lia.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in hx by lia. split.
      * apply Z.div_pos; lia.
      * apply Z.div_lt_upper_bound; lia.
Qed.

Lemma Q_bytes : (Q < 256 ^ Z.of_nat EB)%Z.
Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the parser's pieces *)

Lemma take_app : forall (l s : bytes), ExecVerify.take (List.length l) (l ++ s) = Some (l, s).
Proof. induction l as [| x l ih]; intro s; [reflexivity |]. cbn. rewrite ih. reflexivity. Qed.

Lemma take_len : forall k (l s : bytes), List.length l = k -> ExecVerify.take k (l ++ s) = Some (l, s).
Proof. intros k l s <-. apply take_app. Qed.

Definition zred (x : Z) : Prop := (0 <= x < Q)%Z.

Lemma pbase_ser : forall x s, zred x -> pbase (ser_base x ++ s) = Some (x, s).
Proof.
  intros x s hx. unfold pbase, ser_base. rewrite take_len by apply be_bytes_length. cbn [bindo fst snd].
  pose proof Q_bytes. rewrite from_be_be_bytes by (unfold zred in hx; lia).
  destruct (Z.ltb_spec x Q); [reflexivity | unfold zred in hx; lia].
Qed.

Lemma pf_ser : forall x s, reduced x -> pf (ser_f x ++ s) = Some (x, s).
Proof.
  intros [x y] s [h1 h2]. unfold pf, ser_f. cbn [fst snd] in *. rewrite <-app_assoc.
  rewrite pbase_ser by exact h1. cbn [bindo fst snd]. rewrite pbase_ser by exact h2. reflexivity.
Qed.

Lemma prep_ser : forall {A : Type} (f : bytes -> option (A * bytes)) (ser : A -> bytes) (P : A -> Prop),
  (forall x s, P x -> f (ser x ++ s) = Some (x, s)) ->
  forall xs n s, Forall P xs -> List.length xs = n -> prep n f (flat_map ser xs ++ s) = Some (xs, s).
Proof.
  intros A f ser P hf. induction xs as [| x xs ih]; intros n s hP hn; subst n; [reflexivity |].
  inversion hP as [| ? ? hx hxs]; subst.
  cbn [prep flat_map List.length]. rewrite <-app_assoc, hf by exact hx. cbn [bindo fst snd].
  rewrite ih by (auto). reflexivity.
Qed.

Lemma prep_fs : forall xs n s, Forall reduced xs -> List.length xs = n -> prep n pf (ser_fs xs ++ s) = Some (xs, s).
Proof. intros. apply (prep_ser pf ser_f reduced pf_ser); assumption. Qed.

Definition msg_ok (ev : list xf) (d : nat) : Prop := List.length ev = d /\ Forall reduced ev.

Lemma pmsgs_ser : forall degs msgs s, Forall2 msg_ok msgs degs -> pmsgs degs (flat_map ser_fs msgs ++ s) = Some (msgs, s).
Proof.
  induction degs as [| d ds ih]; intros msgs s h; inversion h as [| ev d' ms ds' hok hrest]; subst; [reflexivity |].
  destruct hok as [hl hr].
  cbn [pmsgs flat_map]. rewrite <-app_assoc, prep_fs by assumption. cbn [bindo fst snd].
  rewrite ih by exact hrest. reflexivity.
Qed.

Definition item_ok (cnt logn : nat) (it : list Z * bytes * list bytes) : Prop :=
  let '(e, salt, path) := it in
  List.length e = cnt /\ Forall zred e /\ List.length salt = 16%nat /\ List.length path = logn
  /\ Forall (fun h => List.length h = 32%nat) path.

Lemma prep_hashes : forall (path : list bytes) n s, Forall (fun h => List.length h = 32%nat) path -> List.length path = n ->
  prep n (ExecVerify.take 32) (List.concat path ++ s) = Some (path, s).
Proof.
  intros path n s h hn.
  assert (e : List.concat path = flat_map (fun x => x) path)
    by (clear; induction path as [| x l ih]; [reflexivity | cbn; rewrite ih; reflexivity]). rewrite e.
  apply (prep_ser (ExecVerify.take 32) (fun x => x) (fun h => List.length h = 32%nat)); [| assumption | assumption].
  intros x s' hx. apply take_len. exact hx.
Qed.

Lemma pitem_ser : forall cnt logn it s, item_ok cnt logn it -> pitem cnt logn (ser_item it ++ s) = Some (it, s).
Proof.
  intros cnt logn [[e salt] path] s (h1 & h2 & h3 & h4 & h5). unfold pitem, ser_item.
  rewrite <-!app_assoc. rewrite (prep_ser pbase ser_base zred pbase_ser) by assumption. cbn [bindo fst snd].
  rewrite take_len by exact h3. cbn [bindo fst snd]. rewrite prep_hashes by assumption. reflexivity.
Qed.

Lemma pbatches_ser : forall cnts logn its s, Forall2 (fun it c => item_ok c logn it) its cnts ->
  pbatches cnts logn (flat_map ser_item its ++ s) = Some (its, s).
Proof.
  induction cnts as [| c cs ih]; intros logn its s h; inversion h as [| it c' its' cs' hit hrest]; subst; [reflexivity |].
  cbn [pbatches flat_map]. rewrite <-app_assoc, pitem_ser by exact hit. cbn [bindo fst snd].
  rewrite ih by exact hrest. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the whole proof *)

Section Parse.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat).

  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).

  Definition cols_ok (nq : nat) (cnts : list nat) (logn : nat) (cols : list (list (list Z * bytes * list bytes))) : Prop :=
    List.length cols = nq /\ Forall (fun its => Forall2 (fun it c => item_ok c logn it) its cnts) cols.

  Definition wf_parts (P : mparts) : Prop :=
    List.length (qrB P) = 32%nat /\ List.length (qr1 P) = 32%nat /\ List.length (qr2 P) = 32%nat
    /\ List.length (qG P) = 3%nat /\ Forall reduced (qG P)
    /\ Forall2 msg_ok (qmA P) (dAE ell) /\ List.length (qevA P) = 4%nat /\ Forall reduced (qevA P)
    /\ Forall2 msg_ok (qmB P) (dBE n1) /\ Forall2 msg_ok (qmC P) (dCE n1 ell)
    /\ List.length (qevC P) = 3%nat /\ Forall reduced (qevC P) /\ reduced (qmu P)
    /\ msg_ok (qv1 P) kB /\ msg_ok (qv2 P) kB /\ msg_ok (qv3 P) kS /\ msg_ok (qv4 P) kS
    /\ msg_ok (qpvB P) kB /\ msg_ok (qpvS P) kS
    /\ cols_ok nqB [(3 * rw + 6)%nat] (log2n 64 nB) (qcB P)
    /\ cols_ok nqS [(rs + 6)%nat; (4 * rs + 1)%nat] (log2n 64 nS) (qcS P).

  Lemma prep_cols : forall nq cnts logn cols s, cols_ok nq cnts logn cols ->
    prep nq (pbatches cnts logn) (flat_map (flat_map ser_item) cols ++ s) = Some (cols, s).
  Proof.
    intros nq cnts logn cols s [hl hf].
    apply (prep_ser (pbatches cnts logn) (flat_map ser_item) (fun its => Forall2 (fun it c => item_ok c logn it) its cnts));
      [| exact hf | exact hl].
    intros x s' hx. apply pbatches_ser. exact hx.
  Qed.

  Theorem parse_ser : forall P, wf_parts P ->
    xmix_parse n1 ell lo1 lo2 kB nB nqB kS nS nqS (ser_parts P) = Some P.
  Proof.
    intros [rB r1 r2 G mA evA mB mC evC mu v1 v2 v3 v4 pvB pvS cB cS]
      (h1 & h2 & h3 & h4 & h5 & h6 & h7 & h8 & h9 & h10 & h11 & h12 & h13 & h14 & h15 & h16 & h17 & h18 & h19 & h20 & h21).
    cbn [qrB qr1 qr2 qG qmA qevA qmB qmC qevC qmu qv1 qv2 qv3 qv4 qpvB qpvS qcB qcS] in *.
    destruct h14, h15, h16, h17, h18, h19.
    unfold xmix_parse, ser_parts. cbn [qrB qr1 qr2 qG qmA qevA qmB qmC qevC qmu qv1 qv2 qv3 qv4 qpvB qpvS qcB qcS].
    rewrite take_len by exact h1. cbn [bindo fst snd].
    rewrite take_len by exact h2. cbn [bindo fst snd].
    rewrite take_len by exact h3. cbn [bindo fst snd].
    rewrite prep_fs by assumption. cbn [bindo fst snd].
    rewrite pmsgs_ser by assumption. cbn [bindo fst snd].
    rewrite prep_fs by assumption. cbn [bindo fst snd].
    rewrite pmsgs_ser by assumption. cbn [bindo fst snd].
    rewrite pmsgs_ser by assumption. cbn [bindo fst snd].
    rewrite prep_fs by assumption. cbn [bindo fst snd].
    rewrite pf_ser by assumption. cbn [bindo fst snd].
    do 6 (rewrite prep_fs by assumption; cbn [bindo fst snd]).
    rewrite prep_cols by exact h20. cbn [bindo fst snd].
    rewrite <-(app_nil_r (flat_map (flat_map ser_item) cS)), prep_cols by exact h21. cbn [bindo fst snd].
    reflexivity.
  Qed.

End Parse.
