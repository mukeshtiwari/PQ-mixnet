(* The decryption prover (dec_proof.py: dec_prove) as executable code, producing the bytes that the
   extracted decryption verifier reads (ExecDec.v: xdec_parse, xdec_verify_bytes).

   As for the shuffle prover (ExecProve.v), the randomness is an input: dcoins_of cuts a stream of
   integers mod q and a stream of 16-byte salts into the random rows, pads, salts and mask table, in
   the order in which dec_prove draws them.

   - The big matrix holds the kd digit tables of E + off (base `base`), split into rows of C1, and
     three random F-rows; the small matrix holds s, e, the mask table and four random F-rows.
   - Sumcheck G proves that every digit is in [0, base): sum eq(tz, .) sum_d kG_d prod_(v < base)
     (D_d - v) = 0. The product is expanded into its coefficients, prod_(v<base) (X - v) =
     sum_j c_j X^j, so the terms are c_j kG_d eq D_d^j; at every point these have the same value as
     the product, so the round messages are those of dec_prove.
   - Sumcheck T proves that s and e are ternary.
   - The claims and the compiled slots of the opening are the verifier's own (clsX, xcbk, xLk, mcbX)
     on a front record holding the prover's challenges.

   Nothing is proven here yet: completeness and the zero-knowledge refinement are later stages. *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String.
From Crypto Require Import DecLayout.
From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive
  ExecVerify ExecMerkle ExecProveBase ExecDec.
Import ListNotations.
Local Open Scope list_scope.

Local Notation "x <- o ;; f" := (bindo o (fun x => f)) (at level 61, o at next level, right associativity).

(* prod_(v < k) (X - v), coefficients from the constant term *)
Fixpoint xrcoefs (k : nat) : list xf :=
  match k with
  | O => [xone]
  | S k' => let p := xrcoefs k' in xpadd (xzero :: p) (xpscale (xneg (xint (Z.of_nat k'))) p)
  end.

(* dec_serialize: the order in which xdec_parse reads *)
Definition ser_dparts (P : dparts) : bytes :=
  proot_big P ++ proot_small P ++ ser_fs (pG P) ++ flat_map ser_fs (pmG P) ++ ser_fs (pzG P)
  ++ flat_map ser_fs (pmT P) ++ ser_fs (pzT P) ++ ser_f (pmu P)
  ++ ser_fs (pvS1 P) ++ ser_fs (pvS2 P) ++ ser_fs (pvSe P) ++ ser_fs (pvSm P) ++ ser_fs (pvSs P)
  ++ ser_fs (ppvB P) ++ ser_fs (ppvS P)
  ++ flat_map (flat_map ser_item) (pcolsB P) ++ flat_map (flat_map ser_item) (pcolsS P).

(* a mask (a0, cs) for the degrees ds, from a list of F entries (as ExecProve.mask_of) *)
Definition mask_ofD (ds : list nat) (l : list xf) : xf * list (list xf) := (nth 0 l xzero, fst (cuts ds (tl l))).

Record dcoins : Type := mk_dcoins {
  dfB : list (list Z);    (* the 6 random rows of the big matrix (3 F-rows) *)
  dpB : list (list Z);    (* the pads of every big row *)
  dsB : list bytes;       (* the salts of the big matrix *)
  dmask : list xf;        (* the mask table *)
  dfS : list (list Z);    (* the 8 random rows of the small matrix (4 F-rows) *)
  dpS : list (list Z);    (* the pads of every small row *)
  dsS : list bytes        (* the salts of the small matrix *)
}.

Section DecProve.

  Variables n1 ell lo1 lo2 kd base : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variables (pplain off : Z).
  Variables (a b : list Z) (us ts : list (list Z)).

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwX n1 ell lo1).
  Local Notation SO := (SOX n1 ell lo1 kd).
  Local Notation dG := (dGX n1 ell base).
  Local Notation dT := (dTX n1).

  Definition n_maskD : nat := (kd + 2 + (1 + list_sum dG) + (1 + list_sum dT))%nat.

  (* dec_prove's order of the draws: rand_frow x3 (big), pads (big), salts (big), the mask table,
     rand_frow x4 (small), pads (small), salts (small) *)
  Definition dcoins_of (zs : list Z) (ss : list bytes) : dcoins :=
    let '(fB, z1) := cuts (repeat C1 6) zs in
    let '(pB, z2) := cuts (repeat nqB SO) z1 in
    let '(mk, z3) := cut (2 * n_maskD) z2 in
    let '(fS, z4) := cuts (repeat C2 8) z3 in
    let '(pS, _) := cuts (repeat nqS 11) z4 in
    let '(sB, s1) := cut nB ss in
    let '(sS, _) := cut nS s1 in
    mk_dcoins fB pB sB (map (fun p => (nth 0 p 0%Z, nth 1 p 0%Z)) (fst (cuts (repeat 2%nat n_maskD) mk))) fS pS sS.

  Definition dzcoins_needed : nat := (6 * C1 + SO * nqB + 2 * n_maskD + 8 * C2 + 11 * nqS)%nat.
  Definition dscoins_needed : nat := (nB + nS)%nat.

  Variables (s e : list Z) (E : list (list Z)).   (* the key share, its noise, the flooding noise (mod q) *)
  Variable k : dcoins.

  (* ------------------------------------------------------------------ *)
  (* round 1: the digits of E + off, and the key share *)

  Definition digit (d : nat) (x : Z) : Z := Z.modulo (Z.div ((x + off) mod Q) (Z.of_nat base ^ Z.of_nat d)) (Z.of_nat base).
  Definition Tdig (d : nat) : list Z := List.concat (map (map (digit d)) E).

  Definition msgsBD : list (list Z) :=
    map (fun p => padrow C1 (fst p) (snd p))
        (combine (flat_map (fun d => split_rows C1 (Tdig d)) (seq 0 kd) ++ dfB k) (dpB k)).
  Definition btBD : batch := commit omB nB (log2n 64 nB) msgsBD (dsB k).

  Definition a_dig : list xf := firstn kd (dmask k).
  Definition a_s : xf := nth kd (dmask k) xzero.
  Definition a_e : xf := nth (kd + 1) (dmask k) xzero.
  Definition gGD : xf * list (list xf) := mask_ofD dG (skipn (kd + 2) (dmask k)).
  Definition gTD : xf * list (list xf) := mask_ofD dT (skipn (kd + 3 + list_sum dG) (dmask k)).
  Definition mask_rowD : list Z := flat_map (fun x => [fst x; snd x]) (dmask k).
  Definition GD : list xf := [mtotal (fst gGD) (snd gGD); mtotal (fst gTD) (snd gTD)].

  Definition sZ : list Z := map zm s.
  Definition eZ : list Z := map zm e.
  Definition msgsSD : list (list Z) :=
    map (fun p => padrow C2 (fst p) (snd p)) (combine ([sZ; eZ; mask_rowD] ++ dfS k) (dpS k)).
  Definition btSD : batch := commit omS nS (log2n 64 nS) msgsSD (dsS k).

  Definition ch_r1D (bB bS : batch) : chal :=
    absorb (absorb (absorb (fs_init (sb "dec")) "params" tag) "stmt" (ddigest a b us ts)) "round1"
           (broot bB ++ broot bS ++ ser_fs GD).

  (* ------------------------------------------------------------------ *)
  (* the sumchecks *)

  Definition tablesG (tz : list xf) : list (list xf) := xeq_table tz :: map (fun d => map bx (Tdig d)) (seq 0 kd).
  Definition tmaskG : list (option xf) := None :: map Some a_dig.
  Definition termsG (kG : list xf) : list sterm :=
    let rc := xrcoefs base in
    flat_map (fun d => map (fun j => (xmul (nth d kG xzero) (nth j rc xzero), 0%nat :: repeat (S d) j))
                           (seq 0 (S base))) (seq 0 kd).

  Definition tablesT (tt : list xf) : list (list xf) := [xeq_table tt; map bx sZ; map bx eZ].
  Definition tmaskT : list (option xf) := [None; Some a_s; Some a_e].
  Definition termsT (kT : list xf) : list sterm :=
    let k0 := nth 0 kT xzero in let k1 := nth 1 kT xzero in
    [(k0, [0; 1; 1; 1]); (xneg k0, [0; 1]); (k1, [0; 2; 2; 2]); (xneg k1, [0; 2])]%nat.

  (* ------------------------------------------------------------------ *)
  (* the opening *)

  Section Open.
    Variables bB bS : batch.
    Variable f : dfront.

    Definition clsPD : list (list xterm) := clsX n1 ell lo1 kd base pplain a us f.
    Definition allmsgsD : list (list Z) := bmsgs bB ++ bmsgs bS.
    Definition combD (cb : list (nat * xf)) : list xf :=
      fold_right (fun iw acc => xpadd (xpscale (snd iw) (map bx (nth (fst iw) allmsgsD []))) acc) [] cb.
    Definition msD (v : nat) : list xf := combD (mcbX n1 ell lo1 kd v).
    Definition usD (v : nat) : list xf := combD (xcbk kindD (frowD SO) (dkp f) clsPD v).
    Definition LD (v : nat) : list xf := xLk kindD (LtX lo1 f) (dkp f) clsPD v.
    Definition muD : xf := xfsum (map (fun v => xdot (msD v) (LD v)) [1; 2; 3; 4; 5]%nat).
    Definition vecD (v : nat) : list xf := xpadd (msD v) (xpscale (dc f) (usD v)).
    Definition pvBD : list xf :=
      xpadd (combD [((kd * rw + 4)%nat, xone); ((kd * rw + 5)%nat, xtg)])
            (combD (combine (rwsBX n1 ell lo1 kd) (firstn (kd * rw + 4) (dgB f)))).
    Definition pvSD : list xf :=
      xpadd (combD [((SO + 9)%nat, xone); ((SO + 10)%nat, xtg)])
            (combD (combine (rwsSX n1 ell lo1 kd) (firstn 9 (dgS f)))).
    (* the absorb order of pcs_open_prove: slots by name S1, S2, Se, Sm, Ss *)
    Definition vec_dataD : bytes :=
      ser_fs (vecD 1%nat) ++ ser_fs (vecD 2%nat) ++ ser_fs (vecD 4%nat) ++ ser_fs (vecD 5%nat) ++ ser_fs (vecD 3%nat)
      ++ ser_fs pvBD ++ ser_fs pvSD.
  End Open.

  Definition front0 (th th1 th2 tz kG rz tt kT rt kp : list xf) (c : xf) (gB gS : list xf) : dfront :=
    mk_dfront th th1 th2 tz kG rz tt kT rt xzero xzero [] [] [] [] kp c gB gS [] [] xzero (fun _ => []) [] []
              (fun _ _ => xzero).

  Definition xdec_prove_partsG (gF : chal -> bytes -> nat -> option (list xf * chal))
    (gI : chal -> bytes -> nat -> Z -> option (list Z * chal)) : option dparts :=
    let bB := btBD in
    let bS := btSD in
    q <- gF (ch_r1D bB bS) (sb "theta") ell;; let th := fst q in
    q <- gF (snd q) (sb "theta1") n1;; let th1 := fst q in
    q <- gF (snd q) (sb "theta2") n1;; let th2 := fst q in
    q <- gF (snd q) (sb "tz") m;; let tz := fst q in
    q <- gF (snd q) (sb "kG") kd;; let kG := fst q in
    q <- gF (snd q) (sb "rhoG") 1;; let rhoG := fst q in
    if negb (xnz (nth 0 rhoG xzero)) then None else
    sG <- xsc_proveG (fun c nm => gF c nm 1) "G" (tablesG tz) tmaskG (termsG kG) dG (fst gGD) (snd gGD)
            (nth 0 rhoG xzero) (snd q);;
    let '(mG, rz, finG, ch) := sG in
    let zG := firstn kd (tl finG) in
    let ch := absorb ch "evalsG" (ser_fs zG) in
    q <- gF ch (sb "tt") n1;; let tt := fst q in
    q <- gF (snd q) (sb "kT") 2;; let kT := fst q in
    q <- gF (snd q) (sb "rhoT") 1;; let rhoT := fst q in
    if negb (xnz (nth 0 rhoT xzero)) then None else
    sT <- xsc_proveG (fun c nm => gF c nm 1) "T" (tablesT tt) tmaskT (termsT kT) dT (fst gTD) (snd gTD)
            (nth 0 rhoT xzero) (snd q);;
    let '(mT, rt, finT, ch) := sT in
    let zT := firstn 2 (tl finT) in
    let ch := absorb ch "evalsT" (ser_fs zT) in
    q <- gF ch (sb "pcs.kappa") (kd + 6);; let kp := fst q in
    let f0 := front0 th th1 th2 tz (kG ++ rhoG) rz tt (kT ++ rhoT) rt kp xzero [] [] in
    let mu := muD bB bS f0 in
    let ch := absorb (snd q) "pcs.mu" (ser_f mu) in
    q <- gF ch (sb "pcs.c") 1;; let c := nth 0 (fst q) xzero in
    q <- gF (snd q) (sb "pcs.gamma.big") (kd * rw + 6);; let gB := fst q in
    q <- gF (snd q) (sb "pcs.gamma.small") 11;; let gS := fst q in
    let f1 := front0 th th1 th2 tz (kG ++ rhoG) rz tt (kT ++ rhoT) rt kp c gB gS in
    let ch := absorb (snd q) "pcs.vec" (vec_dataD bB bS f1) in
    q <- gI ch (sb "pcs.J.big") nqB (Z.of_nat nB);; let JB := fst q in
    q <- gI (snd q) (sb "pcs.J.small") nqS (Z.of_nat nS);; let JS := fst q in
    Some (mk_dparts (broot bB) (broot bS) GD mG zG mT zT mu
                    (vecD bB bS f1 1) (vecD bB bS f1 2) (vecD bB bS f1 4) (vecD bB bS f1 5) (vecD bB bS f1 3)
                    (pvBD bB bS f1) (pvSD bB bS f1)
                    (map (fun j => [bitem bB j]) (map Z.to_nat JB))
                    (map (fun j => [bitem bS j]) (map Z.to_nat JS))).

  Definition xdec_prove_parts : option dparts := xdec_prove_partsG get_F get_I.
  Definition xdec_prove : option bytes := option_map ser_dparts xdec_prove_parts.

End DecProve.

