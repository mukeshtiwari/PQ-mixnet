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
From Crypto Require Import MixLayout. From Examples Require Import ConcreteField ExecField ExecSumcheck ExecHash ExecClaims ExecOpen ExecPublic ExecDerive ExecVerify ExecMerkle ExecProveBase ExecSerial ExecFold ExecFront ExecShape ExecDec.
Import ListNotations.
Local Open Scope list_scope.

Local Notation "x <- o ;; f" := (bindo o (fun x => f)) (at level 61, o at next level, right associativity).

Section Prove.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).

  Local Notation N := (2 ^ n1)%nat.
  Local Notation tau := (2 ^ ell)%nat.
  Local Notation m := (n1 + ell)%nat.
  Local Notation C1 := (2 ^ lo1)%nat.
  Local Notation C2 := (2 ^ lo2)%nat.
  Local Notation rw := (rwE n1 ell lo1).
  Local Notation rs := (rsE ell lo2).
  Local Notation SO := (SOE n1 ell lo1).

  Definition dA : list nat := dAE ell.
  Definition dB : list nat := dBE n1.
  Definition dC : list nat := dCE n1 ell.

  (* number of F entries of the mask table *)
  Definition n_mask : nat :=
    (7 + (1 + list_sum dA) + (1 + list_sum dB) + (1 + list_sum dC))%nat.

  (* fp_core order of the draws: rand_frow x3 (big), pads (big), salts (big), rand_frow x3 (small),
     pads (small, batch 1), salts, the mask table, pads (small, batch 2), salts *)
  Definition coins_of (zs : list Z) (ss : list bytes) : coins :=
    let '(fB, z1) := cuts (repeat C1 6) zs in
    let '(pB, z2) := cuts (repeat nqB (3 * rw + 6)) z1 in
    let '(fS, z3) := cuts (repeat C2 6) z2 in
    let '(pS1, z4) := cuts (repeat nqS (rs + 6)) z3 in
    let '(mk, z5) := cut (2 * n_mask) z4 in
    let '(pS2, _) := cuts (repeat nqS (4 * rs + 1)) z5 in
    let '(sB, s1) := cut nB ss in
    let '(sS1, s2) := cut nS s1 in
    let '(sS2, _) := cut nS s2 in
    mk_coins fB pB sB fS pS1 sS1 (map (fun p => (nth 0 p 0%Z, nth 1 p 0%Z)) (fst (cuts (repeat 2%nat n_mask) mk)))
             pS2 sS2.

  (* how many coins coins_of consumes *)
  Definition zcoins_needed : nat :=
    (6 * C1 + (3 * rw + 6) * nqB + 6 * C2 + (rs + 6) * nqS + 2 * n_mask + (4 * rs + 1) * nqS)%nat.
  Definition scoins_needed : nat := (nB + 2 * nS)%nat.

  (* a mask (a0, cs) for the degrees ds, from a list of F entries *)
  Definition mask_of (ds : list nat) (l : list xf) : xf * list (list xf) :=
    (nth 0 l xzero, fst (cuts ds (tl l))).

  Variable sig : list Z.                        (* the permutation, sigma i *)
  Variables wr we1 we2 : list (list Z).         (* the re-randomisers, tau polynomials of N coefficients *)
  Variable k : coins.

  (* ------------------------------------------------------------------ *)
  (* round 1: the witness and sigma *)

  Definition Wpol : list (list (list Z)) := map (map (map zm)) [wr; we1; we2].
  Definition Wk : list (list Z) := map (@List.concat Z) Wpol.
  Definition sigZ : list Z := map zm sig.

  Definition msgsB : list (list Z) :=
    map (fun p => padrow C1 (fst p) (snd p)) (combine (flat_map (split_rows C1) Wk ++ kfB k) (kpB k)).
  Definition msgsS1 : list (list Z) :=
    map (fun p => padrow C2 (fst p) (snd p)) (combine (split_rows C2 sigZ ++ kfS k) (kpS1 k)).
  Definition btB : batch := commit omB nB (log2n 64 nB) msgsB (ksB k).
  Definition btS1 : batch := commit omS nS (log2n 64 nS) msgsS1 (ksS1 k).

  Definition ch_r1 (bB b1 : batch) : chal :=
    absorb (absorb (absorb (fs_init (sb "mix")) "params" tag) "stmt" (digest a b cin cout)) "round1"
           (broot bB ++ broot b1).

  (* ------------------------------------------------------------------ *)
  (* round 2: the inverses and the mask table *)

  Definition zpubP (ru rv : list xf) : list xf := map (xproj ru rv) (cinX cin).
  Definition zhatP (ru rv : list xf) : list xf := map (xproj ru rv) (cinX cout).
  Definition rpP (ru rv : list xf) : list (list xf) :=
    [xrho_r (aX a) (aX b) ru rv; xrho_e (bx pplain) ru; xrho_e (bx pplain) rv].

  Definition hP (ru rv : list xf) (alpha beta : xf) : list xf :=
    let zp := zpubP ru rv in
    let rw := combine (rpP ru rv) Wpol in
    map (fun i =>
      xsub (xadd (xadd (nth i zp xzero)
                       (xfsum (map (fun p => xdot (fst p) (map bx (nth i (snd p) []))) rw)))
                 (xmul beta (xfint i))) alpha) (seq 0 tau).
  Definition hhP (ru rv : list xf) (alpha beta : xf) : list xf :=
    map (fun p => xsub (xadd (fst p) (xmul beta (bx (snd p)))) alpha) (combine (zhatP ru rv) sigZ).
  Definition uP ru rv alpha beta : list xf := map xinv (hP ru rv alpha beta).
  Definition uhP ru rv alpha beta : list xf := map xinv (hhP ru rv alpha beta).

  Definition a_u : xf := nth 0 (kmask k) xzero.
  Definition a_uh : xf := nth 1 (kmask k) xzero.
  Definition a_sig : xf := nth 2 (kmask k) xzero.
  Definition a_h : xf := nth 3 (kmask k) xzero.
  Definition a_w : list xf := [nth 4 (kmask k) xzero; nth 5 (kmask k) xzero; nth 6 (kmask k) xzero].
  Definition gA : xf * list (list xf) := mask_of dA (skipn 7 (kmask k)).
  Definition gB : xf * list (list xf) := mask_of dB (skipn (8 + list_sum dA) (kmask k)).
  Definition gC : xf * list (list xf) := mask_of dC (skipn (9 + list_sum dA + list_sum dB) (kmask k)).
  Definition mask_row : list Z := flat_map (fun x => [fst x; snd x]) (kmask k).
  Definition GP : list xf := [mtotal (fst gA) (snd gA); mtotal (fst gB) (snd gB); mtotal (fst gC) (snd gC)].

  Definition msgsS2 ru rv alpha beta : list (list Z) :=
    let u := uP ru rv alpha beta in let uh := uhP ru rv alpha beta in
    map (fun p => padrow C2 (fst p) (snd p))
        (combine (split_rows C2 (map fst u) ++ split_rows C2 (map snd u)
                  ++ split_rows C2 (map fst uh) ++ split_rows C2 (map snd uh) ++ [mask_row]) (kpS2 k)).
  Definition btS2 ru rv alpha beta : batch := commit omS nS (log2n 64 nS) (msgsS2 ru rv alpha beta) (ksS2 k).

  (* ------------------------------------------------------------------ *)
  (* the sumchecks *)

  Definition tablesA ru rv alpha beta (tc : list xf) : list (list xf) :=
    [xeq_table tc; uP ru rv alpha beta; hP ru rv alpha beta; uhP ru rv alpha beta; hhP ru rv alpha beta].
  Definition tmaskA (beta : xf) : list (option xf) := [None; Some a_u; Some a_h; Some a_uh; Some (xmul beta a_sig)].
  Definition termsA (kA : list xf) : list sterm :=
    [(nth 0 kA xzero, [0; 1; 2]); (nth 1 kA xzero, [0; 3; 4]); (nth 2 kA xzero, [1]); (xneg (nth 2 kA xzero), [3])]%nat.

  Definition s_valP (rA : list xf) : xf := xadd (xmle (map bx sigZ) rA) (xmul a_sig (xzval rA)).
  Definition evAP (rA finA : list xf) : list xf := [nth 1 finA xzero; nth 3 finA xzero; s_valP rA; nth 2 finA xzero].

  Definition WpP (rA : list xf) : list (list xf) :=
    map (fun pols => fold_right xpadd [] (map (fun p => xpscale (fst p) (map bx (snd p))) (combine (xeq_table rA) pols)))
        Wpol.
  Definition cstP (rA : list xf) : xf := xmul (xmul a_h (xzval rA)) (xinv (xfint N)).
  Definition tablesB ru rv (rA : list xf) : list (list xf) := rpP ru rv ++ WpP rA ++ [repeat (cstP rA) N].
  Definition termsB : list sterm := [(xone, [0; 3]); (xone, [1; 4]); (xone, [2; 5]); (xone, [6])]%nat.

  Definition tablesC (tz : list xf) : list (list xf) := xeq_table tz :: map (map bx) Wk.
  Definition tmaskC : list (option xf) := None :: map Some a_w.
  Definition termsC (kC : list xf) : list sterm :=
    let kc i := nth i kC xzero in
    ([(kc 0, [0; 1; 1; 1]); (kc 1, [0; 2; 2; 2]); (kc 2, [0; 3; 3; 3]);
      (xneg (kc 0), [0; 1]); (xneg (kc 1), [0; 2]); (xneg (kc 2), [0; 3])])%nat.
  Definition evCP (finC : list xf) : list xf := [nth 1 finC xzero; nth 2 finC xzero; nth 3 finC xzero].

  (* ------------------------------------------------------------------ *)
  (* the opening *)

  Section Open.

    Variables bB b1 b2 : batch.
    Variable T : ptrace.

    Definition alT : xf := nth 0 (tab T) xzero.
    Definition beT : xf := nth 1 (tab T) xzero.
    Definition evAT : list xf := evAP (trA T) (tfinA T).
    Definition evCT : list xf := evCP (tfinC T).

    (* the challenges and messages the claims depend on, as a front record *)
    Definition fpre : front :=
      mk_front (tru T) (trv T) alT beT (ttc T) (tkA T ++ trhoA T) (trA T) (nth 0 (trhoB T) xzero) (try T)
               (ttz T) (tkC T ++ trhoC T) (trz T) (nth 0 GP xzero) (nth 1 GP xzero) (nth 2 GP xzero)
               (tmA T) (nth 0 evAT xzero) (nth 1 evAT xzero) (nth 2 evAT xzero) (nth 3 evAT xzero)
               (tmB T) (tmC T) (nth 0 evCT xzero) (nth 1 evCT xzero) (nth 2 evCT xzero)
               [] xzero [] [] [] [] xzero (fun _ => []) [] [] (fun _ _ => xzero).

    Definition clsP : list (list xterm) := clsE n1 ell lo1 lo2 pplain a b fpre.
    Definition allmsgs : list (list Z) := bmsgs bB ++ bmsgs b1 ++ bmsgs b2.
    Definition comb (cb : list (nat * xf)) : list xf :=
      fold_right (fun iw acc => xpadd (xpscale (snd iw) (map bx (nth (fst iw) allmsgs []))) acc) [] cb.
    Definition msP (v : nat) : list xf := comb (mcbE n1 ell lo1 lo2 v).
    Definition usP (v : nat) : list xf := comb (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) clsP v).
    Definition LP (v : nat) : list xf := xLk kindE (LtE lo1 lo2 fpre) (tkp T) clsP v.
    Definition muP : xf := xfsum (map (fun v => xdot (msP v) (LP v)) [1; 2; 3; 4]%nat).
    Definition vecP (v : nat) : list xf := xpadd (msP v) (xpscale (nth 0 (tcl T) xzero) (usP v)).
    Definition pvBP : list xf :=
      xpadd (comb [((3 * rw + 4)%nat, xone); ((3 * rw + 5)%nat, xtg)])
            (comb (combine (rwsBE n1 ell lo1) (firstn (3 * rw + 4) (tgB T)))).
    Definition pvSP : list xf :=
      xpadd (comb [((SO + rs + 4)%nat, xone); ((SO + rs + 5)%nat, xtg)])
            (comb (combine (rwsSE n1 ell lo1 lo2) (firstn (rs + 4) (tgS T) ++ skipn (rs + 6) (tgS T)))).
    Definition vec_data : bytes :=
      ser_fs (vecP 1%nat) ++ ser_fs (vecP 2%nat) ++ ser_fs (vecP 3%nat) ++ ser_fs (vecP 4%nat)
      ++ ser_fs pvBP ++ ser_fs pvSP.

    Definition parts_of : mparts :=
      mk_mparts (broot bB) (broot b1) (broot b2) GP (tmA T) evAT (tmB T) (tmC T) evCT muP
                (vecP 1%nat) (vecP 2%nat) (vecP 3%nat) (vecP 4%nat) pvBP pvSP
                (map (fun j => [bitem bB j]) (map Z.to_nat (tJB T)))
                (map (fun j => [bitem b1 j; bitem b2 j]) (map Z.to_nat (tJS T))).

  End Open.

  (* ------------------------------------------------------------------ *)
  (* the prover: the transcript, then parts_of *)

  Definition xmix_prove_partsG (gF : chal -> bytes -> nat -> option (list xf * chal))
    (gI : chal -> bytes -> nat -> Z -> option (list Z * chal)) : option mparts :=
    let bB := btB in
    let b1 := btS1 in
    q <- gF (ch_r1 bB b1) (sb "rho_u") N;; let ru := fst q in
    q <- gF (snd q) (sb "rho_v") N;; let rv := fst q in
    q <- gF (snd q) (sb "ab") 2;; let ab := fst q in
    let alpha := nth 0 ab xzero in
    let beta := nth 1 ab xzero in
    if existsb (fun x => negb (xnz x)) (hP ru rv alpha beta ++ hhP ru rv alpha beta) then None else
    let b2 := btS2 ru rv alpha beta in
    let ch := absorb (snd q) "round2" (broot b2 ++ ser_fs GP) in
    q <- gF ch (sb "tc") ell;; let tc := fst q in
    q <- gF (snd q) (sb "kA") 3;; let kA := fst q in
    q <- gF (snd q) (sb "rhoA") 1;; let rhoA := fst q in
    if negb (xnz (nth 0 rhoA xzero)) then None else
    sA <- xsc_proveG (fun c nm => gF c nm 1) "A" (tablesA ru rv alpha beta tc) (tmaskA beta) (termsA kA) dA (fst gA) (snd gA)
            (nth 0 rhoA xzero) (snd q);;
    let '(mA, rA, finA, ch) := sA in
    let ch := absorb ch "evalsA" (ser_fs (evAP rA finA)) in
    q <- gF ch (sb "rhoB") 1;; let rhoB := fst q in
    sB <- xsc_proveG (fun c nm => gF c nm 1) "B" (tablesB ru rv rA) (repeat None 7) termsB dB (fst gB) (snd gB) (nth 0 rhoB xzero) (snd q);;
    let '(mB, ry, _, ch) := sB in
    q <- gF ch (sb "tz") m;; let tz := fst q in
    q <- gF (snd q) (sb "kC") 3;; let kC := fst q in
    q <- gF (snd q) (sb "rhoC") 1;; let rhoC := fst q in
    if negb (xnz (nth 0 rhoC xzero)) then None else
    sC <- xsc_proveG (fun c nm => gF c nm 1) "C" (tablesC tz) tmaskC (termsC kC) dC (fst gC) (snd gC) (nth 0 rhoC xzero) (snd q);;
    let '(mC, rz, finC, ch) := sC in
    let ch := absorb ch "evalsC" (ser_fs (evCP finC)) in
    q <- gF ch (sb "pcs.kappa") 9;; let kp := fst q in
    let T0 := mk_ptrace ru rv ab tc kA rhoA mA rA finA rhoB mB ry tz kC rhoC mC rz finC kp [] [] [] [] [] in
    let ch := absorb (snd q) "pcs.mu" (ser_f (muP bB b1 b2 T0)) in
    q <- gF ch (sb "pcs.c") 1;; let cl := fst q in
    q <- gF (snd q) (sb "pcs.gamma.big") (3 * rw + 6);; let gamB := fst q in
    q <- gF (snd q) (sb "pcs.gamma.small") (rs + 6 + (4 * rs + 1));; let gamS := fst q in
    let T1 := mk_ptrace ru rv ab tc kA rhoA mA rA finA rhoB mB ry tz kC rhoC mC rz finC kp cl gamB gamS [] [] in
    let ch := absorb (snd q) "pcs.vec" (vec_data bB b1 b2 T1) in
    q <- gI ch (sb "pcs.J.big") nqB (Z.of_nat nB);; let JB := fst q in
    q <- gI (snd q) (sb "pcs.J.small") nqS (Z.of_nat nS);; let JS := fst q in
    Some (parts_of bB b1 b2 (mk_ptrace ru rv ab tc kA rhoA mA rA finA rhoB mB ry tz kC rhoC mC rz finC kp cl gamB gamS JB JS)).

  Definition xmix_prove_parts : option mparts := xmix_prove_partsG get_F get_I.

  (* ------------------------------------------------------------------ *)
  (* Transcript agreement (completeness, step 1): the prover's output is parts_of of its trace T,
     and the verifier's replay of the transcript on it draws exactly T's challenges. Generic in the
     challenger's drawing operations gF, gI. *)

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
    | context [if ?bb then None else _] => destruct bb eqn:e; cbv beta iota in H; [discriminate H |]
    | context [if negb ?bb then None else _] => destruct bb eqn:e; cbv beta iota in H; [| discriminate H]
    end.

  (* every field of the trace was drawn from the challenger, with the length asked for *)
  Definition drawn (gF : chal -> bytes -> nat -> option (list xf * chal))
    (gI : chal -> bytes -> nat -> Z -> option (list Z * chal)) (T : ptrace) : Prop :=
    let dF (nm : string) (n : nat) (x : list xf) := exists c c', gF c (sb nm) n = Some (x, c') in
    let dI (nm : string) (n : nat) (bd : Z) (x : list Z) := exists c c', gI c (sb nm) n bd = Some (x, c') in
    dF "rho_u"%string N (tru T) /\ dF "rho_v"%string N (trv T) /\ dF "ab"%string 2%nat (tab T) /\ dF "tc"%string ell (ttc T)
    /\ dF "kA"%string 3%nat (tkA T) /\ dF "rhoA"%string 1%nat (trhoA T) /\ dF "rhoB"%string 1%nat (trhoB T) /\ dF "tz"%string m (ttz T)
    /\ dF "kC"%string 3%nat (tkC T) /\ dF "rhoC"%string 1%nat (trhoC T) /\ dF "pcs.kappa"%string 9%nat (tkp T) /\ dF "pcs.c"%string 1%nat (tcl T)
    /\ dF "pcs.gamma.big"%string (3 * rw + 6)%nat (tgB T) /\ dF "pcs.gamma.small"%string (rs + 6 + (4 * rs + 1))%nat (tgS T)
    /\ dI "pcs.J.big"%string nqB (Z.of_nat nB) (tJB T) /\ dI "pcs.J.small"%string nqS (Z.of_nat nS) (tJS T).

  Definition ptrans (gF : chal -> bytes -> nat -> option (list xf * chal))
    (gI : chal -> bytes -> nat -> Z -> option (list Z * chal)) (P : mparts) (T : ptrace) : Prop :=
      let b2 := btS2 (tru T) (trv T) (alT T) (beT T) in
      P = parts_of btB btS1 b2 T /\ drawn gF gI T
      /\ existsb (fun x => negb (xnz x)) (hP (tru T) (trv T) (alT T) (beT T) ++ hhP (tru T) (trv T) (alT T) (beT T)) = false
      /\ xnz (nth 0 (trhoA T) xzero) = true /\ xnz (nth 0 (trhoC T) xzero) = true
      /\ (exists c0 c1, sc_loop (fun c nm => gF c nm 1) "A" (tmaskA (beT T)) (termsA (tkA T)) (fst gA) (snd gA)
                          (nth 0 (trhoA T) xzero) dA 0 (tablesA (tru T) (trv T) (alT T) (beT T) (ttc T)) [] c0
                        = Some (tmA T, trA T, tfinA T, c1))
      /\ (exists c0 fB c1, sc_loop (fun c nm => gF c nm 1) "B" (repeat None 7) termsB (fst gB) (snd gB)
                             (nth 0 (trhoB T) xzero) dB 0 (tablesB (tru T) (trv T) (trA T)) [] c0
                           = Some (tmB T, try T, fB, c1))
      /\ (exists c0 c1, sc_loop (fun c nm => gF c nm 1) "C" tmaskC (termsC (tkC T)) (fst gC) (snd gC)
                          (nth 0 (trhoC T) xzero) dC 0 (tablesC (ttz T)) [] c0
                        = Some (tmC T, trz T, tfinC T, c1))
      /\ xmix_trG n1 ell lo1 lo2 nB nqB nS nqS tag a b cin cout gF gI P =
         (if negb (merkle_ok [broot btB] (map Z.to_nat (tJB T)) (qcB P)
                   && merkle_ok [broot btS1; broot b2] (map Z.to_nat (tJS T)) (qcS P)) then None
          else Some (front_mk n1 ell lo1 lo2 (tru T) (trv T) (tab T) (ttc T) (tkA T) (trhoA T) (trA T) (trhoB T) (try T)
                              (ttz T) (tkC T) (trhoC T) (trz T) (tkp T) (tcl T) (tgB T) (tgS T) (tJB T) (tJS T) P)).

  Theorem prove_transcript : forall gF gI P, xmix_prove_partsG gF gI = Some P -> exists T, ptrans gF gI P T.
  Proof.
    intros gF gI P H. unfold xmix_prove_partsG in H. cbv zeta in H.
    stepF H gF ru c1 e1. stepF H gF rv c2 e2. stepF H gF ab c3 e3.
    stepIf H enz.
    stepF H gF tc c4 e4. stepF H gF kA c5 e5. stepF H gF rhoA c6 e6.
    stepIf H enA.
    stepS H mA rA finA cA eA.
    stepF H gF rhoB c7 e7.
    stepS H mB ry finB cB eB.
    stepF H gF tz c8 e8. stepF H gF kC c9 e9. stepF H gF rhoC c10 e10.
    stepIf H enC.
    stepS H mC rz finC cC eC.
    stepF H gF kp c11 e11. stepF H gF cl c12 e12. stepF H gF gamB c13 e13. stepF H gF gamS c14 e14.
    stepI H gI JB c15 e15. stepI H gI JS c16 e16.
    apply (f_equal (fun o => match o with Some x => x | None => P end)) in H. cbv beta iota in H.
    exists (mk_ptrace ru rv ab tc kA rhoA mA rA finA rhoB mB ry tz kC rhoC mC rz finC kp cl gamB gamS JB JS).
    unfold ptrans. cbv zeta. subst P.
    unfold xsc_proveG in eA, eB, eC.
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eA) as (hA & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eB) as (hB & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eC) as (hC & _).
    split; [reflexivity |].
    split; [unfold drawn; cbv zeta; repeat split; do 2 eexists; eassumption |].
    split; [exact enz |].
    split; [exact (proj1 (negb_false_iff _) enA) |]. split; [exact (proj1 (negb_false_iff _) enC) |].
    split; [exists c6, cA; exact eA |]. split; [exists c7, finB, cB; exact eB |]. split; [exists c10, cC; exact eC |].
    unfold xmix_trG. cbv zeta.
    Ltac bs := rewrite bindo_some; cbv beta.
    use_eq e1; bs. use_eq e2; bs. use_eq e3; bs. use_eq e4; bs. use_eq e5; bs. use_eq e6; bs.
    use_eq hA; bs. use_eq e7; bs. use_eq hB; bs. use_eq e8; bs. use_eq e9; bs. use_eq e10; bs. use_eq hC; bs.
    use_eq e11; bs. use_eq e12; bs. use_eq e13; bs. use_eq e14; bs. use_eq e15; bs. use_eq e16; bs.
    reflexivity.
  Qed.

  Definition xmix_prove : option bytes := option_map ser_parts xmix_prove_parts.

  (* ------------------------------------------------------------------ *)
  (* The shape of the prover's output: what the verifier's parser needs (wf_parts). *)

  Definition params_ok : Prop :=
    kB = (C1 + nqB)%nat /\ kS = (C2 + nqS)%nat
    /\ nB = (2 ^ log2n 64 nB)%nat /\ (1 <= log2n 64 nB)%nat /\ nS = (2 ^ log2n 64 nS)%nat /\ (1 <= log2n 64 nS)%nat
    /\ (2 * n_mask <= C2)%nat.

  Definition witness_shape : Prop :=
    List.length sig = tau /\ List.length cout = tau
    /\ Forall (fun t => List.length t = tau /\ Forall (fun p => List.length p = N) t) [wr; we1; we2].

  Definition rows_ok (cnt len : nat) (rows : list (list Z)) : Prop :=
    List.length rows = cnt /\ Forall (fun r => List.length r = len) rows.

  Definition coins_ok : Prop :=
    rows_ok 6 C1 (kfB k) /\ rows_ok (3 * rw + 6) nqB (kpB k) /\ rows_ok nB 16 (ksB k)
    /\ rows_ok 6 C2 (kfS k) /\ rows_ok (rs + 6) nqS (kpS1 k) /\ rows_ok nS 16 (ksS1 k)
    /\ List.length (kmask k) = n_mask /\ rows_ok (4 * rs + 1) nqS (kpS2 k) /\ rows_ok nS 16 (ksS2 k).

  Lemma rows_le : forall cnt len rows, rows_ok cnt len rows -> Forall (fun r => (List.length r <= len)%nat) rows.
  Proof. intros cnt len rows [_ h]. eapply Forall_impl; [| exact h]. intros r hr. cbv beta in *. lia. Qed.

  Lemma split_tau : forall l : list Z, List.length l = tau ->
    List.length (split_rows C2 l) = rs /\ Forall (fun r => (List.length r <= C2)%nat) (split_rows C2 l).
  Proof. intros l hl. exact (split_rows_shape lo2 ell l hl). Qed.

  Lemma msgsB_shape : witness_shape -> coins_ok ->
    List.length msgsB = (3 * rw + 6)%nat /\ Forall (fun r => List.length r = (C1 + nqB)%nat) msgsB.
  Proof.
    intros (hs & hc & hw) hk. destruct hk as (hfB & hpB & _).
    assert (ht : forall t, In t [wr; we1; we2] -> List.length (List.concat (map (map zm) t)) = (2 ^ m)%nat).
    { intros t hin. rewrite Forall_forall in hw. destruct (hw t hin) as [h1 h2].
      rewrite (length_concat_uniform _ N), length_map, h1.
      - rewrite Nat.pow_add_r. lia.
      - intros l hl. apply in_map_iff in hl. destruct hl as (p & <- & hp). rewrite length_map.
        rewrite Forall_forall in h2. apply h2, hp. }
    assert (hs3 : forall t, In t [wr; we1; we2] ->
              List.length (split_rows C1 (List.concat (map (map zm) t))) = rw
              /\ Forall (fun r => (List.length r <= C1)%nat) (split_rows C1 (List.concat (map (map zm) t))))
      by (intros t hin; exact (split_rows_shape lo1 m _ (ht t hin))).
    destruct (hs3 wr ltac:(cbn; tauto)) as [a1 b1]. destruct (hs3 we1 ltac:(cbn; tauto)) as [a2 b2].
    destruct (hs3 we2 ltac:(cbn; tauto)) as [a3 b3].
    unfold msgsB, Wk, Wpol. cbn [map flat_map]. rewrite app_nil_r.
    match goal with |- context [combine ?rows (kpB k)] => destruct (padrows_shape C1 rows (kpB k) nqB) as [e1 e2] end.
    + repeat (apply Forall_app; split); try assumption. exact (rows_le _ _ _ hfB).
    + exact (proj2 hpB).
    + rewrite !length_app, a1, a2, a3. destruct hfB as [-> _]. destruct hpB as [-> _]. lia.
    + split; [rewrite e1, !length_app, a1, a2, a3; destruct hfB as [-> _]; lia | exact e2].
  Qed.

  Lemma msgsS1_shape : witness_shape -> coins_ok ->
    List.length msgsS1 = (rs + 6)%nat /\ Forall (fun r => List.length r = (C2 + nqS)%nat) msgsS1.
  Proof.
    intros (hs & hc & hw) hk. destruct hk as (_ & _ & _ & hfS & hpS1 & _).
    destruct (split_tau sigZ ltac:(unfold sigZ; rewrite length_map; exact hs)) as [a1 b1].
    unfold msgsS1. match goal with |- context [combine ?rows (kpS1 k)] => destruct (padrows_shape C2 rows (kpS1 k) nqS) as [e1 e2] end.
    + apply Forall_app; split; [exact b1 | exact (rows_le _ _ _ hfS)].
    + exact (proj2 hpS1).
    + rewrite length_app, a1. destruct hfS as [-> _]. destruct hpS1 as [-> _]. lia.
    + split; [rewrite e1, length_app, a1; destruct hfS as [-> _]; lia | exact e2].
  Qed.

  Lemma msgsS2_shape : forall ru rv al be, params_ok -> witness_shape -> coins_ok ->
    List.length (msgsS2 ru rv al be) = (4 * rs + 1)%nat
    /\ Forall (fun r => List.length r = (C2 + nqS)%nat) (msgsS2 ru rv al be).
  Proof.
    intros ru rv al be hp (hs & hc & hw) hk. destruct hk as (_ & _ & _ & _ & _ & _ & hm & hpS2 & _).
    destruct hp as (_ & _ & _ & _ & _ & _ & hmr).
    assert (hu : List.length (uP ru rv al be) = tau) by (unfold uP, hP; cbv zeta; rewrite !length_map, length_seq; reflexivity).
    assert (huh : List.length (uhP ru rv al be) = tau)
      by (unfold uhP, hhP, zhatP, sigZ; unfold cinX; repeat rewrite ?length_map, ?length_combine; rewrite hc, hs; lia).
    destruct (split_tau (map fst (uP ru rv al be)) ltac:(rewrite length_map; exact hu)) as [a1 b1].
    destruct (split_tau (map snd (uP ru rv al be)) ltac:(rewrite length_map; exact hu)) as [a2 b2].
    destruct (split_tau (map fst (uhP ru rv al be)) ltac:(rewrite length_map; exact huh)) as [a3 b3].
    destruct (split_tau (map snd (uhP ru rv al be)) ltac:(rewrite length_map; exact huh)) as [a4 b4].
    assert (hmrow : (List.length mask_row <= C2)%nat).
    { unfold mask_row. rewrite (flat_map_const_length _ 2) by reflexivity.
      apply (Nat.le_trans _ (2 * n_mask)); [apply Nat.eq_le_incl; f_equal; exact hm | exact hmr]. }
    unfold msgsS2. cbv zeta. match goal with |- context [combine ?rows (kpS2 k)] => destruct (padrows_shape C2 rows (kpS2 k) nqS) as [e1 e2] end.
    + repeat (apply Forall_app; split); try assumption. constructor; [exact hmrow | constructor].
    + exact (proj2 hpS2).
    + rewrite !length_app, a1, a2, a3, a4. destruct hpS2 as [-> _]. cbn. lia.
    + split; [rewrite e1, !length_app, a1, a2, a3, a4; cbn; lia | exact e2].
  Qed.

  Theorem prove_wf : params_ok -> witness_shape -> coins_ok -> forall P,
    xmix_prove_parts = Some P -> wf_parts n1 ell lo1 lo2 kB nB nqB kS nS nqS P.
  Proof.
    intros hp hw hk P H.
    destruct (prove_transcript get_F get_I P H) as [T hT]. unfold ptrans in hT. cbv zeta in hT.
    destruct hT as (hP & hdr & _ & _ & _ & (cA0 & cA1 & eA) & (cB0 & fB & cB1 & eB) & (cC0 & cC1 & eC) & _).
    destruct (degs_pos ell n1) as (pA & pB & pC).
    destruct (sc_loop_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pA eA) as [mAok finAok].
    destruct (sc_loop_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pB eB) as [mBok _].
    destruct (sc_loop_shape _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pC eC) as [mCok finCok].
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eA) as (_ & _ & lA & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eB) as (_ & _ & lB & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eC) as (_ & _ & lC & _).
    unfold dA, dB, dC, dAE, dBE, dCE in lA, lB, lC. rewrite length_map, length_seq in lA, lB, lC.
    cbn [Nat.add] in lA, lB, lC.
    pose proof hp as hp'. destruct hp' as (hkB & hkS & hnB & h1B & hnS & h1S & hmr).
    pose proof hk as hk'. destruct hk' as (_ & _ & hsB & _ & _ & hsS1 & _ & _ & hsS2).
    destruct (msgsB_shape hw hk) as [mB1 mB2]. destruct (msgsS1_shape hw hk) as [mS1 mS1'].
    set (ru := tru T). set (rv := trv T). set (al := alT T). set (be := beT T).
    destruct (msgsS2_shape ru rv al be hp hw hk) as [mS2 mS2'].
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hJB & hJS).
    set (b2 := btS2 ru rv al be) in *.
    (* the rows of the three batches *)
    set (AM := allmsgs btB btS1 b2).
    assert (hAM : AM = msgsB ++ msgsS1 ++ msgsS2 ru rv al be) by reflexivity.
    assert (rowB : forall i, (i < 3 * rw + 6)%nat -> List.length (nth i AM []) = kB).
    { intros i hi. rewrite hAM, app_nth1 by lia. rewrite Forall_forall in mB2. rewrite mB2, hkB; [reflexivity |].
      apply nth_In. lia. }
    assert (rowS : forall i, (SO <= i < SO + (rs + 6) + (4 * rs + 1))%nat -> List.length (nth i AM []) = kS).
    { intros i hi. unfold SOE in hi. rewrite hAM, app_nth2 by lia. rewrite mB1.
      destruct (Nat.lt_ge_cases (i - (3 * rw + 6)) (rs + 6)) as [h1 | h1].
      + rewrite app_nth1 by lia. rewrite Forall_forall in mS1'. rewrite mS1', hkS; [reflexivity |]. apply nth_In. lia.
      + rewrite app_nth2 by lia. rewrite Forall_forall in mS2'. rewrite mS2', hkS; [reflexivity |]. apply nth_In. lia. }
    assert (hcomb : forall cb, comb btB btS1 b2 cb = fcomb (fun i => nth i AM []) cb) by reflexivity.
    (* the rows the compiled slots use *)
    assert (hcls : forall cl t, In cl (clsP T) -> In t cl -> row_ok n1 ell lo1 lo2 SO t).
    { intros cl t hcl ht. unfold clsP, clsE in hcl.
      apply (xclaims9_rows n1 ell lo1 lo2 SO _ _ _ _ _ _ _ _ _ _ _ lA lB lC cl t hcl ht). }
    assert (husB : forall v, (v = 1 \/ v = 2)%nat ->
              Forall (fun iw => (List.length (nth (fst iw) AM []) <= kB)%nat)
                     (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsP T) v)).
    { intros v hv. unfold xcbk, kindE. replace (Nat.eqb v 4) with false by (destruct hv as [-> | ->]; reflexivity).
      apply Forall_forall. intros iw hiw. destruct (xgbatch_rows _ _ _ _ hiw) as (cl & t & h1 & h2 & h3 & h4).
      destruct (hcls cl t h1 h2) as (_ & hr & _). rewrite h4, rowB; [lia |]. assert (trowx t < 3 * rw)%nat by (apply hr; lia). lia. }
    assert (husS : forall v, (v = 3 \/ v = 4)%nat ->
              Forall (fun iw => (List.length (nth (fst iw) AM []) <= kS)%nat)
                     (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsP T) v)).
    { intros v hv. unfold xcbk, kindE. destruct hv as [-> | ->]; cbn [Nat.eqb].
      + apply Forall_forall. intros iw hiw. destruct (xgbatch_rows _ _ _ _ hiw) as (cl & t & h1 & h2 & h3 & h4).
        destruct (hcls cl t h1 h2) as (_ & _ & hr). rewrite h4, rowS; [lia |]. apply hr. lia.
      + constructor; [| constructor]. cbn [fst]. unfold frowE, MixLayout.rM. rewrite rowS; [lia |]. unfold SOE, rsE, rwE in *. lia. }
    assert (hvec : forall v kk, (forall i, In i (map fst (mcbE n1 ell lo1 lo2 v)) -> List.length (nth i AM []) = kk) ->
              mcbE n1 ell lo1 lo2 v <> [] ->
              Forall (fun iw => (List.length (nth (fst iw) AM []) <= kk)%nat) (xcbk kindE (frowE n1 ell lo1 lo2) (tkp T) (clsP T) v) ->
              msg_ok (vecP btB btS1 b2 T v) kk).
    { intros v kk hm hne hu. unfold vecP. split.
      + rewrite xpadd_length. unfold xpscale. rewrite length_map. unfold msP, usP. rewrite !hcomb.
        assert (e1 : List.length (fcomb (fun i => nth i AM []) (mcbE n1 ell lo1 lo2 v)) = kk).
        { apply fcomb_length_eq.
          + apply Forall_forall. intros iw hiw. rewrite hm; [lia | apply in_map, hiw].
          + assert (hx : exists iw, In iw (mcbE n1 ell lo1 lo2 v)).
            { clear -hne. destruct (mcbE n1 ell lo1 lo2 v) as [| iw r]; [contradiction | exists iw; left; reflexivity]. }
            destruct hx as (iw & hiw). exists iw. split; [exact hiw |]. apply hm, in_map, hiw. }
        pose proof (fcomb_length_le (fun i => nth i AM []) _ _ hu). lia.
      + apply xpadd_reduced; [unfold msP; rewrite hcomb; apply fcomb_reduced | apply xpscale_reduced]. }
    assert (hmB : forall v, (v = 1 \/ v = 2)%nat -> msg_ok (vecP btB btS1 b2 T v) kB).
    { intros v hv. apply hvec; [| destruct hv as [-> | ->]; discriminate | apply husB, hv].
      intros i hi. destruct hv as [-> | ->]; cbn in hi; apply rowB; lia. }
    assert (hmS : forall v, (v = 3 \/ v = 4)%nat -> msg_ok (vecP btB btS1 b2 T v) kS).
    { intros v hv. apply hvec; [| destruct hv as [-> | ->]; discriminate | apply husS, hv].
      intros i hi. destruct hv as [-> | ->]; cbn in hi; apply rowS; unfold SOE; lia. }
    (* the parts *)
    subst P. unfold wf_parts. cbn [parts_of qrB qr1 qr2 qG qmA qevA qmB qmC qevC qmu qv1 qv2 qv3 qv4 qpvB qpvS qcB qcS].
    destruct hsB as [hsB1 hsB2]. destruct hsS1 as [hs11 hs12]. destruct hsS2 as [hs21 hs22].
    split; [apply broot_length; [exact h1B | rewrite <-hnB; exact hsB1 | exact hnB] |].
    split; [apply broot_length; [exact h1S | rewrite <-hnS; exact hs11 | exact hnS] |].
    split; [apply broot_length; [exact h1S | rewrite <-hnS; exact hs21 | exact hnS] |].
    split; [reflexivity |].
    split; [unfold GP, mtotal; repeat constructor; apply xadd_reduced |].
    split; [exact mAok |].
    split; [reflexivity |].
    split; [unfold evAT, evAP, s_valP; repeat constructor; first [apply xadd_reduced | apply nth_reduced; exact finAok] |].
    split; [exact mBok |].
    split; [exact mCok |].
    split; [reflexivity |].
    split; [unfold evCT, evCP; repeat constructor; apply nth_reduced; exact finCok |].
    split; [unfold muP; apply xfsum_reduced |].
    split; [apply hmB; tauto |]. split; [apply hmB; tauto |]. split; [apply hmS; tauto |]. split; [apply hmS; tauto |].
    split.
    { (* the proximity vector of the big matrix *)
      unfold pvBP. split.
      + rewrite xpadd_length, !hcomb.
        assert (e1 : List.length (fcomb (fun i => nth i AM []) [((3 * rw + 4)%nat, xone); ((3 * rw + 5)%nat, xtg)]) = kB).
        { apply fcomb_length_eq;
            [apply Forall_forall; intros iw hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; rewrite rowB; lia |].
          exists ((3 * rw + 4)%nat, xone). split; [left; reflexivity | cbn [fst]; apply rowB; lia]. }
        assert (e2 : (List.length (fcomb (fun i => nth i AM []) (combine (rwsBE n1 ell lo1) (firstn (3 * rw + 4) (tgB T)))) <= kB)%nat).
        { apply fcomb_length_le, Forall_forall. intros [i w] hin. apply in_combine_l in hin. cbn [fst].
          unfold rwsBE in hin. apply in_seq in hin. rewrite rowB; lia. }
        lia.
      + apply xpadd_reduced; rewrite hcomb; apply fcomb_reduced. }
    split.
    { (* the proximity vector of the small matrix *)
      unfold pvSP. split.
      + rewrite xpadd_length, !hcomb.
        assert (e1 : List.length (fcomb (fun i => nth i AM []) [((SO + rs + 4)%nat, xone); ((SO + rs + 5)%nat, xtg)]) = kS).
        { apply fcomb_length_eq;
            [apply Forall_forall; intros iw hiw; destruct hiw as [<- | [<- | []]]; cbn [fst]; rewrite rowS by (unfold SOE; lia); lia |].
          exists ((SO + rs + 4)%nat, xone). split; [left; reflexivity | cbn [fst]; apply rowS; unfold SOE; lia]. }
        assert (e2 : (List.length (fcomb (fun i => nth i AM [])
                        (combine (rwsSE n1 ell lo1 lo2) (firstn (rs + 4) (tgS T) ++ skipn (rs + 6) (tgS T)))) <= kS)%nat).
        { apply fcomb_length_le, Forall_forall. intros [i w] hin. apply in_combine_l in hin. cbn [fst].
          unfold rwsSE in hin. apply in_map_iff in hin. destruct hin as (i0 & <- & hi0).
          apply in_app_or in hi0. destruct hi0 as [hi0 | hi0]; apply in_seq in hi0; rewrite rowS; unfold SOE; lia. }
        lia.
      + apply xpadd_reduced; rewrite hcomb; apply fcomb_reduced. }
    split.
    { (* the opened columns of the big matrix *)
      split; [rewrite !length_map; exact (drawn_count _ _ _ _ _ hnB hJB) |].
      apply Forall_map. pose proof (drawn_indices _ _ _ _ _ hnB hJB) as hj.
      rewrite Forall_forall in hj |- *. intros j hjin. constructor; [| constructor].
      apply bitem_ok; [exact hnB | reflexivity | exact hsB1 | exact hsB2 | exact mB1 | exact (hj j hjin)]. }
    { (* the opened columns of the small matrix *)
      split; [rewrite !length_map; exact (drawn_count _ _ _ _ _ hnS hJS) |].
      apply Forall_map. pose proof (drawn_indices _ _ _ _ _ hnS hJS) as hj.
      rewrite Forall_forall in hj |- *. intros j hjin. constructor; [| constructor; [| constructor]].
      + apply bitem_ok; [exact hnS | reflexivity | exact hs11 | exact hs12 | exact mS1 | exact (hj j hjin)].
      + apply bitem_ok; [exact hnS | reflexivity | exact hs21 | exact hs22 | exact mS2 | exact (hj j hjin)]. }
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The front end on the prover's output: the verifier parses the bytes back, replays the transcript
     (drawing exactly the prover's challenges) and accepts the Merkle paths. *)

  Theorem prove_front : params_ok -> coins_ok -> forall P, xmix_prove_parts = Some P ->
    exists T, ptrans get_F get_I P T
      /\ xmix_tr n1 ell lo1 lo2 nB nqB nS nqS tag a b cin cout P
         = Some (front_mk n1 ell lo1 lo2 (tru T) (trv T) (tab T) (ttc T) (tkA T) (trhoA T) (trA T) (trhoB T) (try T)
                          (ttz T) (tkC T) (trhoC T) (trz T) (tkp T) (tcl T) (tgB T) (tgS T) (tJB T) (tJS T) P).
  Proof.
    intros hp hk P H. destruct (prove_transcript get_F get_I P H) as [T hT].
    exists T. split; [exact hT |].
    destruct hp as (_ & _ & HnB & _ & HnS & _ & _). destruct hk as (_ & _ & [HsB _] & _ & _ & [HsS1 _] & _ & _ & [HsS2 _]).
    destruct hT as (hP & hdr & _ & _ & _ & _ & _ & _ & htr).
    unfold xmix_tr. rewrite htr.
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & hJB & hJS).
    assert (gB : good_batch nB btB) by (apply good_commit; assumption).
    assert (g1 : good_batch nS btS1) by (apply good_commit; assumption).
    assert (g2 : good_batch nS (btS2 (tru T) (trv T) (alT T) (beT T))) by (apply good_commit; assumption).
    assert (eB : merkle_ok [broot btB] (map Z.to_nat (tJB T)) (qcB P) = true).
    { rewrite hP. cbn [parts_of qcB].
      apply (merkle_ok_prover nB [btB]); [constructor; [exact gB | constructor] |].
      exact (drawn_indices _ _ _ _ _ HnB hJB). }
    assert (eS : merkle_ok [broot btS1; broot (btS2 (tru T) (trv T) (alT T) (beT T))] (map Z.to_nat (tJS T)) (qcS P) = true).
    { rewrite hP. cbn [parts_of qcS].
      apply (merkle_ok_prover nS [btS1; btS2 (tru T) (trv T) (alT T) (beT T)]); [repeat constructor; assumption |].
      exact (drawn_indices _ _ _ _ _ HnS hJS). }
    rewrite eB, eS. reflexivity.
  Qed.

  Theorem prove_front_bytes : params_ok -> witness_shape -> coins_ok -> forall prf, xmix_prove = Some prf ->
    exists P T, prf = ser_parts P /\ ptrans get_F get_I P T
      /\ xmix_front n1 ell lo1 lo2 kB nB nqB kS nS nqS tag a b cin cout prf
         = Some (front_mk n1 ell lo1 lo2 (tru T) (trv T) (tab T) (ttc T) (tkA T) (trhoA T) (trA T) (trhoB T) (try T)
                          (ttz T) (tkC T) (trhoC T) (trz T) (tkp T) (tcl T) (tgB T) (tgS T) (tJB T) (tJS T) P).
  Proof.
    intros hp hw hk prf H. unfold xmix_prove in H.
    destruct xmix_prove_parts as [P |] eqn:eP; cbn [option_map] in H; [| discriminate].
    injection H as <-. destruct (prove_front hp hk P eP) as (T & hT & htr).
    exists P, T. split; [reflexivity |]. split; [exact hT |].
    unfold xmix_front. rewrite parse_ser by (exact (prove_wf hp hw hk P eP)). cbn [bindo]. exact htr.
  Qed.

End Prove.
