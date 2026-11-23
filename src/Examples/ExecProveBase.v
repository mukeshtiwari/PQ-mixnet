(* Generic pieces of the prover (ExecProve.v): lists, encoding, Merkle trees, the sumcheck prover, the coins and
   the trace. Split from ExecProve.v so that the lemma files can be imported by it.

   Original description of the prover: *)
(* Prover side, stage 3: the shuffle prover (mix_proof.py: mix_prove) as
   executable code, producing the bytes of mix_serialize.

   The prover's randomness is an input (the record coins): the random rows
   and pads of the committed matrices, the Merkle salts and the mask table.
   coins_of cuts two streams (integers mod q, 16-byte salts) into these
   pieces in the order in which mix_prove draws them from rnd, so that the
   same streams give the same proof as mix_prove (tested in
   Unverified/cross_prove.py).

   Pieces:
   - zenc: the codeword of a row of integers mod q (Horner at om^j over
     Z_q; fp_core.py uses an NTT for the same values).
   - layers / lpath: the Merkle tree built once, and its paths
     (ExecMerkle.v: mpath recomputes the tree for every path).
   - xsc_prove: fp_core.sc_prove (tables folded round by round, masked
     extensions in the last round, round polynomials masked by rho * g).
   - xmix_prove: mix_prove. The Fiat-Shamir calls are those of xmix_front
     (ExecVerify.v), in the same order; the claims and the compiled slots
     of the opening are computed by the verifier's own functions (clsE,
     xcbk, xLk, mcbE) on a front record holding the prover's challenges.

   Completeness (the verifier accepts this output) is stage P5; nothing is
   proven here. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String.
From Crypto Require Import MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecMerkle.
From Examples Require Export ExecFFT.
Import ListNotations.
Local Open Scope list_scope.

Local Notation "x <- o ;; f" := (bindo o (fun x => f)) (at level 61, o at next level, right associativity).

(* ---------------------------------------------------------------------- *)
(* lists *)

Fixpoint zipcons {A : Type} (r : list A) (acc : list (list A)) : list (list A) :=
  match r, acc with
  | x :: r', a :: acc' => (x :: a) :: zipcons r' acc'
  | _, _ => []
  end.

(* rows (each of length n) to columns *)
Definition transpose {A : Type} (n : nat) (rows : list (list A)) : list (list A) :=
  fold_right zipcons (repeat [] n) rows.

Fixpoint chunks {A : Type} (fuel C : nat) (l : list A) : list (list A) :=
  match fuel with
  | O => []
  | S f => match l with [] => [] | _ => firstn C l :: chunks f C (skipn C l) end
  end.

(* fp_core.split_rows *)
Definition split_rows (C : nat) (l : list Z) : list (list Z) :=
  if Nat.leb (List.length l) C then [l] else chunks (List.length l) C l.

(* the first k items of a stream, and the rest *)
Definition cut {A : Type} (k : nat) (s : list A) : list A * list A := (firstn k s, skipn k s).

Fixpoint cuts {A : Type} (ks : list nat) (s : list A) : list (list A) * list A :=
  match ks with
  | [] => ([], s)
  | k :: ks' => let '(x, s1) := cut k s in let '(xs, s2) := cuts ks' s1 in (x :: xs, s2)
  end.

Definition zm (x : Z) : Z := x mod Q.

(* ---------------------------------------------------------------------- *)
(* encoding and Merkle trees *)

Fixpoint layers (d : nat) (l : list bytes) : list (list bytes) :=
  match d with
  | O => [l]
  | S d' => l :: layers d' (up l)
  end.

Fixpoint lpath (lys : list (list bytes)) (j : nat) : list bytes :=
  match lys with
  | [] | [_] => []
  | l :: lys' => nth (sib j) l [] :: lpath lys' (Nat.div2 j)
  end.

(* one committed batch: its columns, salts and tree *)
Record batch : Type := mk_batch {
  bmsgs : list (list Z); bcols : list (list Z); bsalts : list bytes; blayers : list (list bytes) }.

Definition commit (om : Z) (n d : nat) (msgs : list (list Z)) (salts : list bytes) : batch :=
  let cols := transpose n (map (zenc om n) msgs) in
  let leaves := map (fun p => leaf_hash (fst p) (snd p)) (combine salts cols) in
  mk_batch msgs cols salts (layers d leaves).

Definition broot (bt : batch) : bytes := nth 0 (last (blayers bt) []) [].

Definition bitem (bt : batch) (j : nat) : list Z * bytes * list bytes :=
  (nth j (bcols bt) [], nth j (bsalts bt) [], lpath (blayers bt) j).

Definition ser_item (it : list Z * bytes * list bytes) : bytes :=
  let '(e, salt, path) := it in flat_map ser_base e ++ salt ++ List.concat path.

(* mix_serialize *)
Definition ser_parts (P : mparts) : bytes :=
  qrB P ++ qr1 P ++ qr2 P ++ ser_fs (qG P) ++ flat_map ser_fs (qmA P) ++ ser_fs (qevA P)
  ++ flat_map ser_fs (qmB P) ++ flat_map ser_fs (qmC P) ++ ser_fs (qevC P) ++ ser_f (qmu P)
  ++ ser_fs (qv1 P) ++ ser_fs (qv2 P) ++ ser_fs (qv3 P) ++ ser_fs (qv4 P) ++ ser_fs (qpvB P) ++ ser_fs (qpvS P)
  ++ flat_map (flat_map ser_item) (qcB P) ++ flat_map (flat_map ser_item) (qcS P).

(* a row of C data entries (padded with zeros) followed by its random pads *)
Definition padrow (C : nat) (row pads : list Z) : list Z := map zm row ++ repeat 0%Z (C - List.length row) ++ pads.

(* ---------------------------------------------------------------------- *)
(* the sumcheck prover (fp_core.sc_prove) *)

Fixpoint pairs (t : list xf) : list (xf * xf) :=
  match t with
  | x :: y :: r => (x, y) :: pairs r
  | _ => []
  end.

Definition xext (p : xf * xf) (x : xf) : xf := xadd (fst p) (xmul x (xsub (snd p) (fst p))).

Definition xfold (t : list xf) (r : xf) : list xf := map (fun p => xext p r) (pairs t).

Definition sterm : Type := (xf * list nat)%type.

Definition term_val (vals : list xf) (t : sterm) : xf :=
  fold_left (fun p i => xmul p (nth i vals xzero)) (snd t) (fst t).

Definition terms_val (terms : list sterm) (vals : list xf) : xf := xfsum (map (term_val vals) terms).

Definition xfint (c : nat) : xf := xint (Z.of_nat c).

(* the mask g(x) = a0 + sum_j sum_t cs_j[t-1] x_j^t (SumcheckMask.v, fp_core.SCMask) *)
Definition xuni (c : list xf) (x : xf) : xf := xmul x (xeval c x).
Definition xpow2 (k : nat) : xf := xint (2 ^ Z.of_nat k).

Definition mtotal (a0 : xf) (cs : list (list xf)) : xf :=
  xadd (xmul a0 (xpow2 (List.length cs))) (xmul (xfsum (List.concat cs)) (xpow2 (List.length cs - 1))).

Definition mvalue (a0 : xf) (cs : list (list xf)) (j : nat) (pref : list xf) (c : nat) : xf :=
  let rem := (List.length cs - j - 1)%nat in
  let base := xadd a0 (xfsum (map (fun p => xuni (fst p) (snd p)) (combine (firstn j cs) pref))) in
  let tail := xfsum (List.concat (skipn (S j) cs)) in
  let v := xmul (xadd base (xuni (nth j cs []) (xfint c))) (xpow2 rem) in
  if Nat.leb 1 rem then xadd v (xmul tail (xpow2 (rem - 1))) else v.

(* the points of a message: 0, 2, .., d *)
Definition spoints (d : nat) : list nat := 0%nat :: seq 2 (d - 1).

(* the value of the summand's round polynomial at c, first rounds *)
Definition round_val (terms : list sterm) (rows : list (list (xf * xf))) (c : nat) : xf :=
  let x := xfint c in xfsum (map (fun row => terms_val terms (map (fun p => xext p x) row)) rows).

(* last round: two entries per table, and the off-cube masks *)
Definition last_uni (zprev : xf) (t : list xf) (mk : option xf) (x : xf) : xf :=
  let v := xext (nth 0 t xzero, nth 1 t xzero) x in
  match mk with
  | Some a => xadd v (xmul (xmul a zprev) (xmul x (xsub xone x)))
  | None => v
  end.

Definition last_vals (zprev : xf) (tables : list (list xf)) (tmask : list (option xf)) (x : xf) : list xf :=
  map (fun p => last_uni zprev (fst p) (snd p) x) (combine tables tmask).

Section SCProve.

  Variable draw : chal -> bytes -> option (list xf * chal).
  Variable name : string.
  Variable tmask : list (option xf).
  Variable terms : list sterm.
  Variables (a0 : xf) (cs : list (list xf)).
  Variable rho : xf.

  (* messages, point, final values of the (masked) tables, transcript *)
  Fixpoint sc_loop (degs : list nat) (j : nat) (tables : list (list xf)) (point : list xf) (ch : chal)
    : option (list (list xf) * list xf * list xf * chal) :=
    match degs with
    | [] => Some ([], point, [], ch)
    | d :: ds =>
        let last := match ds with [] => true | _ => false end in
        let zprev := xzval point in
        let rows := transpose (List.length (pairs (nth 0 tables []))) (map pairs tables) in
        let core c := if last then terms_val terms (last_vals zprev tables tmask (xfint c)) else round_val terms rows c in
        let vals := map (fun c => xadd (core c) (xmul rho (mvalue a0 cs j point c))) (spoints d) in
        let ch1 := fs_absorb ch (sb name ++ sb ".m" ++ dec j) (ser_fs vals) in
        p <- draw ch1 (sb name ++ sb ".r" ++ dec j);;
        let r := nth 0 (fst p) xzero in
        if last then Some ([vals], point ++ [r], last_vals zprev tables tmask r, snd p)
        else q <- sc_loop ds (S j) (map (fun t => xfold t r) tables) (point ++ [r]) (snd p);;
             let '(ms, pt, fin, ch2) := q in Some (vals :: ms, pt, fin, ch2)
    end.

End SCProve.

Definition xsc_proveG (draw : chal -> bytes -> option (list xf * chal)) (name : string) (tables : list (list xf))
  (tmask : list (option xf)) (terms : list sterm) (degs : list nat) (a0 : xf) (cs : list (list xf)) (rho : xf) (ch : chal)
  : option (list (list xf) * list xf * list xf * chal) :=
  sc_loop draw name tmask terms a0 cs rho degs 0 tables [] ch.

Definition xsc_prove := xsc_proveG draw1.

Lemma bindo_some : forall {A B : Type} (a : A) (f : A -> option B), bindo (Some a) f = f a.
Proof. reflexivity. Qed.

Lemma fst_pair : forall {A B : Type} (x : A) (y : B), fst (x, y) = x.
Proof. reflexivity. Qed.
Lemma snd_pair : forall {A B : Type} (x : A) (y : B), snd (x, y) = y.
Proof. reflexivity. Qed.

Lemma bindo_none : forall {A B : Type} (f : A -> option B), bindo None f = None.
Proof. reflexivity. Qed.

Lemma sc_chalsG_nil : forall draw name j ch, sc_chalsG draw name j [] ch = Some ([], ch).
Proof. reflexivity. Qed.

Lemma sc_chalsG_cons : forall draw name j ev ms ch,
  sc_chalsG draw name j (ev :: ms) ch =
  bindo (draw (fs_absorb ch (sb name ++ sb ".m" ++ dec j) (ser_fs ev)) (sb name ++ sb ".r" ++ dec j))
        (fun p => bindo (sc_chalsG draw name (S j) ms (snd p)) (fun q => Some (nth 0 (fst p) xzero :: fst q, snd q))).
Proof. reflexivity. Qed.

(* replace a call of the drawing function by its value, up to conversion of the arguments *)
Ltac use_draw hg :=
  match type of hg with
  | ?dr ?x ?y = ?v =>
      match goal with |- context [dr ?x' ?y'] => replace (dr x' y') with v by (rewrite <-hg; reflexivity) end
  end.

(* the verifier's sumcheck transcript draws the prover's point *)
Lemma sc_loop_chals : forall draw name tmask terms a0 cs rho ds j tables point ch msgs pt fin ch',
  List.length point = j ->
  sc_loop draw name tmask terms a0 cs rho ds j tables point ch = Some (msgs, pt, fin, ch') ->
  sc_chalsG draw name j msgs ch = Some (skipn j pt, ch') /\ firstn j pt = point
  /\ List.length pt = (j + List.length ds)%nat /\ List.length msgs = List.length ds.
Proof.
  intros draw name tmask terms a0 cs rho. induction ds as [| d ds ih]; intros j tables point ch msgs pt fin ch' hpt H.
  { cbn [sc_loop] in H. injection H as <- <- <- <-. rewrite sc_chalsG_nil.
    rewrite skipn_all2, firstn_all2 by lia. cbn [List.length]. repeat split; lia. }
  cbn [sc_loop] in H.
  destruct (draw _ _) as [[rl chr] |] eqn:hg; [| discriminate].
  rewrite bindo_some in H. cbv beta in H.
  set (r := nth 0 (fst (rl, chr)) xzero) in *.
  destruct ds as [| d' ds']; cbv beta iota zeta in H, hg.
  - injection H as <- <- <- <-. rewrite sc_chalsG_cons. use_draw hg. rewrite bindo_some, sc_chalsG_nil, bindo_some.
    split; [| split; [| split]].
    + rewrite skipn_app, hpt, Nat.sub_diag, skipn_all2 by lia. reflexivity.
    + rewrite firstn_app, hpt, Nat.sub_diag, firstn_all2 by lia. cbn [firstn]. apply app_nil_r.
    + rewrite length_app, hpt. reflexivity.
    + reflexivity.
  - destruct (sc_loop draw name tmask terms a0 cs rho (d' :: ds') (S j) _ (point ++ [r]) (snd (rl, chr)))
      as [[[[ms pt0] fin0] ch0] |] eqn:hrec; [| discriminate].
    rewrite bindo_some in H. injection H as <- <- <- <-.
    destruct (ih (S j) _ (point ++ [r]) _ _ _ _ _ ltac:(rewrite length_app, hpt; cbn; lia) hrec)
      as (h1 & h2 & h3 & h4).
    assert (hnth : nth j pt0 xzero = r).
    { rewrite <-(firstn_skipn (S j) pt0), app_nth1 by (rewrite length_firstn; cbn [List.length] in h3; lia).
      rewrite h2, app_nth2 by lia. rewrite hpt, Nat.sub_diag. reflexivity. }
    assert (hsk : skipn j pt0 = r :: skipn (S j) pt0).
    { rewrite (skipn_nth_cons pt0 j xzero) by (cbn [List.length] in h3; lia). rewrite hnth. reflexivity. }
    split; [| split; [| split]].
    + rewrite sc_chalsG_cons. use_draw hg. rewrite bindo_some, h1, bindo_some, hsk. reflexivity.
    + replace (firstn j pt0) with (firstn j (firstn (S j) pt0)) by (rewrite firstn_firstn, Nat.min_l by lia; reflexivity).
      rewrite h2, firstn_app, hpt, Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. apply firstn_all2. lia.
    + rewrite h3. cbn [List.length]. lia.
    + cbn [List.length]. rewrite h4. reflexivity.
Qed.


(* ---------------------------------------------------------------------- *)
(* the prover's coins *)

Record coins : Type := mk_coins {
  kfB : list (list Z);    (* the 6 random rows of the big matrix (3 F-rows) *)
  kpB : list (list Z);    (* the pads of every big row *)
  ksB : list bytes;       (* the salts of the big matrix *)
  kfS : list (list Z);    (* the 6 random rows of the first small batch *)
  kpS1 : list (list Z);
  ksS1 : list bytes;
  kmask : list xf;        (* the mask table *)
  kpS2 : list (list Z);
  ksS2 : list bytes
}.

(* what the prover draws from the transcript, and the outputs of its sumchecks *)
Record ptrace : Type := mk_ptrace {
  tru : list xf; trv : list xf; tab : list xf;
  ttc : list xf; tkA : list xf; trhoA : list xf; tmA : list (list xf); trA : list xf; tfinA : list xf;
  trhoB : list xf; tmB : list (list xf); try : list xf;
  ttz : list xf; tkC : list xf; trhoC : list xf; tmC : list (list xf); trz : list xf; tfinC : list xf;
  tkp : list xf; tcl : list xf; tgB : list xf; tgS : list xf; tJB : list Z; tJS : list Z
}.

