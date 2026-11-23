(* The verifier of the shuffle proof (mix_proof.py: mix_deserialize,
   mix_verify = mix_derive + pcs_open_verify) as executable code, and what
   its acceptance implies.

   xmix_front parses the proof, replays the Fiat-Shamir transcript, checks
   the Merkle paths, and collects challenges, messages and opened columns
   in a record. xmix_back runs the algebraic checks on that record:
   xderive (sumcheck layer), xclaims9 (the nine claims), xaccO (opening).
   xmix_verify is front followed by back.

   Theorem xmix_back_sound: if the back end accepts a record, then at
   GF(q^2), for the challenge tuple of the record and the prover whose
   messages are those of the record,
     - the claimed values are vals9 and PreAcc holds (xderive_sound),
     - the claims are claims9 for the verifier's tables of the statement
       (to_F_claims9, ExecPublic.v),
     - AccO holds for the committed words read off the opened columns
       (xaccO_sound).
   These are the events of mix_full / mix_theorem_5_2 (RealAcc), with the
   committed words replaced by the opened entries.

   Not proven, and outside the model of the soundness theorems: the parser,
   the Fiat-Shamir transcript and the Merkle paths (xmix_front). The code
   parameters (k, n, nq, omega for each matrix) and the transcript tag are
   inputs, computed by the caller as in fp_core.code_params. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String Ascii.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import Counting LogDer Mle Negacyclic Bgv CubeIndex MixMultiset MixSound OpenSound SlotKinds RowLayout MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive.
Import ListNotations.
Local Open Scope list_scope.

Definition bindo {A B : Type} (o : option A) (f : A -> option B) : option B :=
  match o with Some a => f a | None => None end.
Local Notation "x <- o ;; f" := (bindo o (fun x => f)) (at level 61, o at next level, right associativity).

(* ---------------------------------------------------------------------- *)
(* parsing (mix_deserialize; every field element and entry must be < q) *)

(* the first k bytes, without measuring the rest *)
Fixpoint take (k : nat) (s : bytes) : option (bytes * bytes) :=
  match k with
  | O => Some ([], s)
  | S k' =>
      match s with
      | [] => None
      | x :: s' => match take k' s' with Some (t, r) => Some (x :: t, r) | None => None end
      end
  end.

Definition pbase (s : bytes) : option (Z * bytes) :=
  p <- take EB s;; let v := from_be (fst p) in if Z.ltb v Q then Some (v, snd p) else None.

Definition pf (s : bytes) : option (xf * bytes) :=
  p1 <- pbase s;; p2 <- pbase (snd p1);; Some ((fst p1, fst p2), snd p2).

Fixpoint prep {A : Type} (n : nat) (f : bytes -> option (A * bytes)) (s : bytes) : option (list A * bytes) :=
  match n with
  | O => Some ([], s)
  | S n' => p <- f s;; q <- prep n' f (snd p);; Some (fst p :: fst q, snd q)
  end.

Fixpoint pmsgs (degs : list nat) (s : bytes) : option (list (list xf) * bytes) :=
  match degs with
  | [] => Some ([], s)
  | d :: ds => p <- prep d pf s;; q <- pmsgs ds (snd p);; Some (fst p :: fst q, snd q)
  end.

(* one batch of one opened column: entries, salt, path *)
Definition pitem (cnt logn : nat) (s : bytes) : option ((list Z * bytes * list bytes) * bytes) :=
  e <- prep cnt pbase s;; salt <- take 16 (snd e);; path <- prep logn (take 32) (snd salt);;
  Some ((fst e, fst salt, fst path), snd path).

Fixpoint pbatches (cnts : list nat) (logn : nat) (s : bytes) : option (list (list Z * bytes * list bytes) * bytes) :=
  match cnts with
  | [] => Some ([], s)
  | c :: cs => p <- pitem c logn s;; q <- pbatches cs logn (snd p);; Some (fst p :: fst q, snd q)
  end.

(* ---------------------------------------------------------------------- *)
(* transcript helpers *)

Fixpoint dec_aux (fuel n : nat) (acc : bytes) : bytes :=
  match fuel with
  | O => acc
  | S f => if Nat.ltb n 10 then Z.of_nat (48 + n) :: acc else dec_aux f (n / 10) (Z.of_nat (48 + n mod 10) :: acc)
  end.
Definition dec (n : nat) : bytes := dec_aux 20 n [].

Definition sb (s : string) : bytes := bytes_of_string s.

Definition absorb (ch : chal) (lab : string) (data : bytes) : chal := fs_absorb ch (sb lab) data.

(* the rounds of a sumcheck: absorb message j, draw r_j. Generic in the drawing function, so that
   proofs about it never ask the kernel to evaluate the challenger. *)
Fixpoint sc_chalsG (draw : chal -> bytes -> option (list xf * chal))
  (name : string) (j : nat) (msgs : list (list xf)) (ch : chal) : option (list xf * chal) :=
  match msgs with
  | [] => Some ([], ch)
  | ev :: ms =>
      let ch1 := fs_absorb ch (sb name ++ sb ".m" ++ dec j) (ser_fs ev) in
      p <- draw ch1 (sb name ++ sb ".r" ++ dec j);;
      q <- sc_chalsG draw name (S j) ms (snd p);;
      Some (nth 0 (fst p) xzero :: fst q, snd q)
  end.

Definition draw1 (ch : chal) (nm : bytes) : option (list xf * chal) := get_F ch nm 1.

Definition sc_chals : string -> nat -> list (list xf) -> chal -> option (list xf * chal) := sc_chalsG draw1.

Definition bx (z : Z) : xf := (z, 0%Z).

(* ---------------------------------------------------------------------- *)
(* the parsed proof (mix_deserialize) *)

Record mparts : Type := mk_mparts {
  qrB : bytes; qr1 : bytes; qr2 : bytes;
  qG : list xf; qmA : list (list xf); qevA : list xf; qmB : list (list xf); qmC : list (list xf); qevC : list xf;
  qmu : xf; qv1 : list xf; qv2 : list xf; qv3 : list xf; qv4 : list xf; qpvB : list xf; qpvS : list xf;
  qcB : list (list (list Z * bytes * list bytes)); qcS : list (list (list Z * bytes * list bytes))
}.

(* ---------------------------------------------------------------------- *)
(* the record handed from the front end to the back end *)

Record front : Type := mk_front {
  fru : list xf; frv : list xf; fal : xf; fbe : xf;
  ftc : list xf; fkA : list xf; frA : list xf; frhoB : xf; fry : list xf;
  ftz : list xf; fkC : list xf; frz : list xf;
  fGA : xf; fGB : xf; fGC : xf;
  fmA : list (list xf); fU : xf; fUh : xf; fsv : xf; fHd : xf;
  fmB : list (list xf); fmC : list (list xf); fw1 : xf; fw2 : xf; fw3 : xf;
  fkp : list xf; fc : xf; fgB : list xf; fgS : list xf; fJB : list nat; fJS : list nat;
  fmu : xf; fub : nat -> list xf; fpvB : list xf; fpvS : list xf;
  fXe : nat -> nat -> xf
}.

Section Verify.

  (* the instance and the parameters *)
  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Definition rwE : nat := MixLayout.rw n1 ell lo1.
  Definition rsE : nat := MixLayout.rs ell lo2.
  Definition SOE : nat := (3 * rwE + 6)%nat.

  Definition dAE : list nat := map (fun i => if Nat.eqb (S i) ell then 5%nat else 3%nat) (seq 0 ell).
  Definition dBE : list nat := map (fun _ => 2%nat) (seq 0 n1).
  Definition dCE : list nat := map (fun i => if Nat.eqb (S i) m then 7%nat else 4%nat) (seq 0 m).

  Definition aX : list xf := map bx a.
  Definition bX : list xf := map bx b.
  Definition ctxX (c : list Z * list Z) : list xf * list xf := (map bx (fst c), map bx (snd c)).
  Definition cinX : list (list xf * list xf) := map ctxX cin.
  Definition coutX : list (list xf * list xf) := map ctxX cout.

  Definition digest : bytes :=
    sha256 (flat_map ser_base (a ++ b ++ flat_map (fun c => fst c ++ snd c) cin ++ flat_map (fun c => fst c ++ snd c) cout)).

  (* layout of the opening (MixFinal.v) *)
  Definition kindE (v : nat) : bool := Nat.eqb v 4.
  Definition frowE (_ : nat) : nat := MixLayout.rM ell lo2 SOE.
  Definition mcbE (v : nat) : list (nat * xf) :=
    match v with
    | 1 => [((3 * rwE)%nat, xone); ((3 * rwE + 1)%nat, xtg)]
    | 2 => [((3 * rwE + 2)%nat, xone); ((3 * rwE + 3)%nat, xtg)]
    | 3 => [((SOE + rsE)%nat, xone); ((SOE + rsE + 1)%nat, xtg)]
    | _ => [((SOE + rsE + 2)%nat, xone); ((SOE + rsE + 3)%nat, xtg)]
    end.
  Definition rwsBE : list nat := seq 0 (3 * rwE + 4).
  Definition rwsSE : list nat := map (fun i => (SOE + i)%nat) (seq 0 (rsE + 4) ++ seq (rsE + 6) (4 * rsE + 1)).

  (* ------------------------------------------------------------------ *)
  (* back end *)

  Section Back.

    Variable f : front.

    Definition invNE : xf := xinv (xint (Z.of_nat N)).
    Definition rp1E : list xf := xrho_r aX bX (fru f) (frv f).
    Definition rp2E : list xf := xrho_e (bx pplain) (fru f).
    Definition rp3E : list xf := xrho_e (bx pplain) (frv f).

    Definition clsE : list (list xterm) :=
      xclaims9 n1 ell lo1 lo2 SOE dAE dBE dCE invNE (frA f) (fry f) (frz f) (frhoB f)
               (xmle rp1E (fry f)) (xmle rp2E (fry f)) (xmle rp3E (fry f)).

    Definition LtE (v : nat) : list xf :=
      if Nat.eqb v 1 then xlo_vec lo1 (fry f ++ frA f)
      else if Nat.eqb v 2 then xlo_vec lo1 (frz f) else xlo_vec lo2 (frA f).

    Definition xmpBE (j : nat) : xf := xadd (fXe f (3 * rwE + 4) j) (xmul xtg (fXe f (3 * rwE + 5) j)).
    Definition xmpSE (j : nat) : xf := xadd (fXe f (SOE + rsE + 4) j) (xmul xtg (fXe f (SOE + rsE + 5) j)).

    Definition derivedE : option (list xf) :=
      xderive cinX coutX n1 ell (fru f) (frv f) (fal f) (fbe f) (ftc f) (fkA f) (frA f) (frhoB f) (fry f)
              (ftz f) (fkC f) (frz f) (fGA f) (fGB f) (fGC f) (fmA f) (fU f) (fUh f) (fsv f) (fHd f)
              (fmB f) (fmC f) (fw1 f) (fw2 f) (fw3 f).

    Definition openE (vals : list xf) : bool :=
      xaccO (fXe f) (bx omB) (bx omS) nB nS kB kS xmpBE xmpSE rwsBE rwsSE kindE frowE LtE mcbE [1; 2]%nat [3; 4]%nat
            clsE vals (fkp f) (fc f) (fgB f) (fgS f) (fJB f) (fJS f) (fmu f) (fub f) (fpvB f) (fpvS f).

    Definition lengths_ok : bool :=
      Nat.eqb (List.length (frA f)) ell && Nat.eqb (List.length (fry f)) n1 && Nat.eqb (List.length (frz f)) m
      && Nat.eqb (List.length (fru f)) N && Nat.eqb (List.length (frv f)) N && Nat.ltb 0 (List.length a)
      && Nat.eqb (List.length a) N && Nat.eqb (List.length b) N.

    Definition xmix_back : bool :=
      lengths_ok && match derivedE with Some vals => openE vals | None => false end.

  End Back.

  (* ------------------------------------------------------------------ *)
  (* front end: parse, transcript, Merkle paths *)

  Fixpoint log2n (fuel n : nat) : nat :=
    match fuel with O => 0 | S f => if Nat.leb n 1 then 0 else S (log2n f (n / 2)) end.

  Definition lookup (js : list nat) (cols : list (list Z)) (j : nat) : list Z :=
    nth (match find (fun p => Nat.eqb (fst p) j) (combine (seq 0 (List.length js)) js) with
         | Some p => fst p | None => 0 end)%nat cols [].

  Fixpoint idx_of (js : list nat) (j : nat) (k : nat) : nat :=
    match js with [] => k | x :: r => if Nat.eqb x j then k else idx_of r j (S k) end.

  Definition merkle_ok (roots : list bytes) (js : list nat) (cols : list (list (list Z * bytes * list bytes))) : bool :=
    forallb (fun p =>
      let '(j, per_batch) := p in
      forallb (fun q =>
        let '(bidx, item) := q in
        let '(e, salt, path) := item in
        match nth_error roots bidx with
        | Some rt => if list_eq_dec Z.eq_dec (root_from (leaf_hash salt e) (Z.of_nat j) path) rt then true else false
        | None => false
        end) (combine (seq 0 (List.length per_batch)) per_batch)) (combine js cols).

  Definition xmix_parse (prf : bytes) : option mparts :=
    let rB := (3 * rwE + 6)%nat in
    let RS := [(rsE + 6)%nat; (4 * rsE + 1)%nat] in
    p <- take 32 prf;; let root_big := fst p in
    p <- take 32 (snd p);; let root_s1 := fst p in
    p <- take 32 (snd p);; let root_s2 := fst p in
    p <- prep 3 pf (snd p);; let G := fst p in
    p <- pmsgs dAE (snd p);; let mA := fst p in
    p <- prep 4 pf (snd p);; let evA := fst p in
    p <- pmsgs dBE (snd p);; let mB := fst p in
    p <- pmsgs dCE (snd p);; let mC := fst p in
    p <- prep 3 pf (snd p);; let evC := fst p in
    p <- pf (snd p);; let mu := fst p in
    p <- prep kB pf (snd p);; let v1 := fst p in
    p <- prep kB pf (snd p);; let v2 := fst p in
    p <- prep kS pf (snd p);; let v3 := fst p in
    p <- prep kS pf (snd p);; let v4 := fst p in
    p <- prep kB pf (snd p);; let pvB := fst p in
    p <- prep kS pf (snd p);; let pvS := fst p in
    p <- prep nqB (pbatches [rB] (log2n 64 nB)) (snd p);; let colsB := fst p in
    p <- prep nqS (pbatches RS (log2n 64 nS)) (snd p);; let colsS := fst p in
    if match snd p with [] => false | _ => true end then None else
    Some (mk_mparts root_big root_s1 root_s2 G mA evA mB mC evC mu v1 v2 v3 v4 pvB pvS colsB colsS).

  (* the record handed to the back end, from the challenges and the parsed proof *)
  Definition front_mk (ru rv ab tc kA rhoA rA rhoB ry tz kC rhoC rz kp cl gB gS : list xf) (JBz JSz : list Z)
    (P : mparts) : front :=
    let JB := map Z.to_nat JBz in
    let JS := map Z.to_nat JSz in
    let colB := map (fun bs => flat_map (fun it => fst (fst it)) bs) (qcB P) in
    let colS := map (fun bs => flat_map (fun it => fst (fst it)) bs) (qcS P) in
    let Xe i j := if Nat.ltb i SOE then bx (nth i (nth (idx_of JB j 0) colB []) 0%Z)
                  else bx (nth (i - SOE) (nth (idx_of JS j 0) colS []) 0%Z) in
    let ub v := match v with 1 => qv1 P | 2 => qv2 P | 3 => qv3 P | _ => qv4 P end in
    mk_front ru rv (nth 0 ab xzero) (nth 1 ab xzero) tc (kA ++ rhoA) rA (nth 0 rhoB xzero) ry
             tz (kC ++ rhoC) rz (nth 0 (qG P) xzero) (nth 1 (qG P) xzero) (nth 2 (qG P) xzero)
             (qmA P) (nth 0 (qevA P) xzero) (nth 1 (qevA P) xzero) (nth 2 (qevA P) xzero) (nth 3 (qevA P) xzero)
             (qmB P) (qmC P) (nth 0 (qevC P) xzero) (nth 1 (qevC P) xzero) (nth 2 (qevC P) xzero)
             kp (nth 0 cl xzero) (firstn (3 * rwE + 4) gB) (firstn (rsE + 4) gS ++ skipn (rsE + 6) gS) JB JS
             (qmu P) ub (qpvB P) (qpvS P) Xe.

  (* generic in the challenger's two drawing operations (the proofs about it never evaluate them) *)
  Definition xmix_trG (gF : chal -> bytes -> nat -> option (list xf * chal))
    (gI : chal -> bytes -> nat -> Z -> option (list Z * chal)) (P : mparts) : option front :=
    let rB := (3 * rwE + 6)%nat in
    let root_big := qrB P in let root_s1 := qr1 P in let root_s2 := qr2 P in
    let G := qG P in let mA := qmA P in let evA := qevA P in let mB := qmB P in let mC := qmC P in
    let evC := qevC P in let mu := qmu P in
    let v1 := qv1 P in let v2 := qv2 P in let v3 := qv3 P in let v4 := qv4 P in
    let pvB := qpvB P in let pvS := qpvS P in let colsB := qcB P in let colsS := qcS P in
    (* transcript of mix_derive *)
    let ch := fs_init (sb "mix") in
    let ch := absorb ch "params" tag in
    let ch := absorb ch "stmt" digest in
    let ch := absorb ch "round1" (root_big ++ root_s1) in
    q <- gF ch (sb "rho_u") N;; let ru := fst q in
    q <- gF (snd q) (sb "rho_v") N;; let rv := fst q in
    q <- gF (snd q) (sb "ab") 2;; let ab := fst q in
    let ch := absorb (snd q) "round2" (root_s2 ++ ser_fs G) in
    q <- gF ch (sb "tc") ell;; let tc := fst q in
    q <- gF (snd q) (sb "kA") 3;; let kA := fst q in
    q <- gF (snd q) (sb "rhoA") 1;; let rhoA := fst q in
    q <- sc_chalsG (fun c nm => gF c nm 1) "A" 0 mA (snd q);; let rA := fst q in
    let ch := absorb (snd q) "evalsA" (ser_fs evA) in
    q <- gF ch (sb "rhoB") 1;; let rhoB := fst q in
    q <- sc_chalsG (fun c nm => gF c nm 1) "B" 0 mB (snd q);; let ry := fst q in
    q <- gF (snd q) (sb "tz") m;; let tz := fst q in
    q <- gF (snd q) (sb "kC") 3;; let kC := fst q in
    q <- gF (snd q) (sb "rhoC") 1;; let rhoC := fst q in
    q <- sc_chalsG (fun c nm => gF c nm 1) "C" 0 mC (snd q);; let rz := fst q in
    let ch := absorb (snd q) "evalsC" (ser_fs evC) in
    (* transcript of pcs_open_verify *)
    q <- gF ch (sb "pcs.kappa") 9;; let kp := fst q in
    let ch := absorb (snd q) "pcs.mu" (ser_f mu) in
    q <- gF ch (sb "pcs.c") 1;; let cl := fst q in
    q <- gF (snd q) (sb "pcs.gamma.big") rB;; let gB := fst q in
    q <- gF (snd q) (sb "pcs.gamma.small") (rsE + 6 + (4 * rsE + 1))%nat;; let gS := fst q in
    let ch := absorb (snd q) "pcs.vec" (ser_fs v1 ++ ser_fs v2 ++ ser_fs v3 ++ ser_fs v4 ++ ser_fs pvB ++ ser_fs pvS) in
    q <- gI ch (sb "pcs.J.big") nqB (Z.of_nat nB);; let JBz := fst q in
    q <- gI (snd q) (sb "pcs.J.small") nqS (Z.of_nat nS);; let JSz := fst q in
    if negb (merkle_ok [root_big] (map Z.to_nat JBz) colsB && merkle_ok [root_s1; root_s2] (map Z.to_nat JSz) colsS)
    then None else
    Some (front_mk ru rv ab tc kA rhoA rA rhoB ry tz kC rhoC rz kp cl gB gS JBz JSz P).

  Definition xmix_tr : mparts -> option front := xmix_trG get_F get_I.

  Definition xmix_front (prf : bytes) : option front := P <- xmix_parse prf;; xmix_tr P.

  Definition xmix_verify (prf : bytes) : bool :=
    match xmix_front prf with Some f => xmix_back f | None => false end.

  (* ------------------------------------------------------------------ *)
  (* what acceptance of the back end implies *)

  Lemma xnadj_length : forall a' rho, a' <> [] -> List.length (xnadj a' rho) = List.length rho.
  Proof.
    intros a' rho h. rewrite <-(length_map to_F), to_F_nadj.
    rewrite (@nadj_length Fq2 fadd fmul fopp (map to_F a') (map to_F rho)) by (destruct a'; [contradiction | discriminate]).
    apply length_map.
  Qed.

  Lemma xpadd_length : forall p q, List.length (xpadd p q) = Nat.max (List.length p) (List.length q).
  Proof. intros p q. rewrite <-(length_map to_F), to_F_padd, (@length_padd Fq2 fadd), !length_map. reflexivity. Qed.

  Theorem xmix_back_sound : forall f, xmix_back f = true ->
    exists vals,
      let cinF' := @cinF cinX in
      map to_F vals
        = vals9F cinX coutX n1 ell (fru f) (frv f) (fal f) (fbe f) (ftc f) (fkA f) (frA f) (frhoB f) (fry f)
                 (ftz f) (fkC f) (frz f) (fGA f) (fGB f) (fGC f) (fmA f) (fU f) (fUh f) (fsv f) (fHd f)
                 (fmB f) (fmC f) (fw1 f) (fw2 f) (fw3 f)
      /\ PreAccF cinX n1 ell (fru f) (frv f) (fal f) (fbe f) (ftc f) (fkA f) (frA f) (frhoB f) (fry f)
                 (ftz f) (fkC f) (frz f) (fGA f) (fGB f) (fGC f) (fmA f) (fHd f) (fmB f) (fmC f)
      /\ map (map tF) (clsE f)
         = @claims9 Fq2 fzero fone fadd fmul fsub ftg (finv (@nF Fq2 fzero fone fadd N)) n1 ell lo1 lo2 SOE
                    dAE dBE dCE (map to_F (frA f)) (map to_F (fry f)) (map to_F (frz f)) (to_F (frhoB f))
                    (rp1T (map to_F aX) (map to_F bX) n1 (c1F (fru f) (frv f) (fal f) (fbe f)))
                    (rp2T (to_F (bx pplain)) n1 (c1F (fru f) (frv f) (fal f) (fbe f)))
                    (rp3T (to_F (bx pplain)) n1 (c1F (fru f) (frv f) (fal f) (fbe f)))
      /\ @AccO Fq2 fzero fone fadd fmul (to_F (bx omB)) (to_F (bx omS)) kB kS (fun i j => to_F (fXe f i j))
               rwsBE rwsSE (fun j => to_F (xmpBE f j)) (fun j => to_F (xmpSE f j)) (map to_F vals)
               (fun kp' => @Lk Fq2 fadd fmul kindE (fun v => map to_F (LtE f v)) kp' (map (map tF) (clsE f)))
               (fun kp' => @cbk Fq2 fone fmul kindE frowE kp' (map (map tF) (clsE f)))
               (fun v => map pairF (mcbE v)) [1; 2]%nat [3; 4]%nat
               (fun _ => to_F (fmu f)) (fun _ _ v => map to_F (fub f v)) (fun _ _ => map to_F (fpvB f))
               (fun _ _ => map to_F (fpvS f))
               (map to_F (fkp f)) (to_F (fc f), (map to_F (fgB f), map to_F (fgS f))) (fJB f, fJS f).
  Proof.
    intros f h. unfold xmix_back in h. apply andb_true_iff in h. destruct h as [hl h].
    destruct (derivedE f) as [vals |] eqn:ed; [| discriminate].
    exists vals. cbv zeta.
    unfold lengths_ok in hl. repeat rewrite andb_true_iff in hl.
    destruct hl as (((((((hr & hy) & hz) & hu) & hv) & ha0) & ha) & hb).
    apply Nat.eqb_eq in hr, hy, hz, hu, hv, ha, hb. apply Nat.ltb_lt in ha0.
    destruct (xderive_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed) as [e1 e2].
    split; [exact e1 |]. split; [exact e2 |]. split.
    + unfold clsE.
      destruct (point_fields n1 (map to_F (fru f)) (map to_F (frv f)) (to_F (fal f)) (to_F (fbe f))
                  ltac:(rewrite length_map; exact hu) ltac:(rewrite length_map; exact hv)) as (p1 & p2 & _ & _).
      replace (finv (@nF Fq2 fzero fone fadd N)) with (to_F invNE)
        by (unfold invNE; rewrite to_F_inv, to_F_xint_nat; reflexivity).
      apply to_F_claims9; [exact hr | exact hy | exact hz | | |].
      * unfold rp1E. rewrite to_F_mle, hy.
        2:{ unfold xrho_r. rewrite xpadd_length, !xnadj_length, hu, hv, hy; [lia | |];
            unfold aX, bX; destruct a, b; cbn in *; try discriminate; lia. }
        unfold ExecPublic.rp1T. fold (c1F (fru f) (frv f) (fal f) (fbe f)) in p1, p2. rewrite p1, p2, to_F_rho_r.
        reflexivity.
      * unfold rp2E. rewrite to_F_mle, hy by (unfold xrho_e, xpscale; rewrite length_map, hu, hy; reflexivity).
        unfold ExecPublic.rp2T. fold (c1F (fru f) (frv f) (fal f) (fbe f)) in p1. rewrite p1, to_F_rho_e. reflexivity.
      * unfold rp3E. rewrite to_F_mle, hy by (unfold xrho_e, xpscale; rewrite length_map, hv, hy; reflexivity).
        unfold ExecPublic.rp3T. fold (c1F (fru f) (frv f) (fal f) (fbe f)) in p2. rewrite p2.
        unfold xrho_e. rewrite to_F_pscale. reflexivity.
    + exact (xaccO_sound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h).
  Qed.

End Verify.
