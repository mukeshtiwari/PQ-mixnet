(* Completeness of the shuffle proof (stage P5): the verifier accepts what
   the prover outputs, for a valid witness and any coins.

   Theorem xmix_complete. Under
     params_ok      the parameters of the two row codes are consistent,
     witness_shape  sigma and the outputs have tau entries, the
                    re-randomisers are tau polynomials of N coefficients,
     coins_ok       the prover's coins have the counts and lengths it draws,
     stmt_ok        the public key has N coefficients, there are tau inputs,
                    log N, log tau >= 1, and N + tau < q,
     valid          sig = sigma, and over GF(q^2) the outputs are the inputs
                    permuted by sigma and re-randomised with ternary
                    (r, e1, e2) (Rmix of Bgv.v),
   if xmix_prove returns proof bytes, xmix_verify accepts them.

   xmix_prove returns None when a denominator h_i or hhat_j vanishes or
   when rho_A or rho_C is zero; completeness is stated for the runs in
   which it returns a proof (how rarely it returns None is not proven
   here).

   Pieces: prove_front_bytes (front end, ExecProve.v), derive_complete
   (the sumcheck layer, ExecBackD.v), open_complete (the opening,
   ExecBackO.v). *)

From Stdlib Require Import Utf8 ZArith List Lia Bool PeanoNat Arith String.
From Examples Require Import ConcreteField ExecField ExecHash ExecVerify ExecProveBase ExecSerial ExecFront ExecShape ExecProve ExecBack ExecBackD ExecBackO.
Import ListNotations.

Section Complete.

  Variables n1 ell lo1 lo2 : nat.
  Variables (kB nB nqB kS nS nqS : nat) (omB omS : Z).
  Variable tag : bytes.
  Variable pplain : Z.
  Variables (a b : list Z) (cin cout : list (list Z * list Z)).
  Variable sig : list Z.
  Variables wr we1 we2 : list (list Z).
  Variable k : coins.
  Variable sigma : list nat.

  Theorem xmix_complete :
    params_ok n1 ell lo1 lo2 kB nB nqB kS nS nqS ->
    witness_shape n1 ell cout sig wr we1 we2 ->
    coins_ok n1 ell lo1 lo2 nB nqB nS nqS k ->
    stmt_ok n1 ell a b cin ->
    valid n1 ell pplain a b cin cout sig wr we1 we2 sigma ->
    forall prf, xmix_prove n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k = Some prf ->
    xmix_verify n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS tag pplain a b cin cout prf = true.
  Proof.
    intros hp hw hk hs hv prf H. unfold xmix_prove in H.
    destruct (xmix_prove_parts n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k) as [P |] eqn:eP;
      cbn [option_map] in H; [| discriminate].
    injection H as <-.
    pose proof (prove_wf n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k hp hw hk P eP) as hwf.
    destruct (prove_front n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k hp hk P eP)
      as (T & hT & htr).
    unfold xmix_verify, xmix_front. rewrite parse_ser by exact hwf. cbn [bindo]. rewrite htr.
    destruct (derive_complete n1 ell lo1 lo2 nB nqB nS nqS omB omS tag pplain a b cin cout sig wr we1 we2 k sigma
                hs hw hk hv P T hT) as (hl & vals & hd & hvals).
    unfold xmix_back. change (front_mk n1 ell lo1 lo2 (tru T) (trv T) (tab T) (ttc T) (tkA T) (trhoA T) (trA T) (trhoB T)
                                        (try T) (ttz T) (tkC T) (trhoC T) (trz T) (tkp T) (tcl T) (tgB T) (tgS T)
                                        (tJB T) (tJS T) P)
                            with (fT n1 ell lo1 lo2 P T).
    rewrite hl, hd. cbn [andb].
    (* the shape of the trace *)
    destruct hT as (hP & hdr & _ & _ & _ & (cA0 & cA1 & eA) & (cB0 & fB & cB1 & eB) & (cC0 & cC1 & eC) & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eA) as (_ & _ & lA & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eB) as (_ & _ & lB & _).
    destruct (sc_loop_chals _ _ _ _ _ _ _ _ 0 _ [] _ _ _ _ _ eq_refl eC) as (_ & _ & lC & _).
    rewrite (dA_len ell) in lA. rewrite (dB_len n1) in lB. rewrite (dC_len n1 ell) in lC. cbn [Nat.add] in lA, lB, lC.
    unfold drawn in hdr. cbv zeta in hdr.
    destruct hdr as (dru & drv & _ & _ & _ & _ & _ & _ & _ & _ & dkp & _ & _ & _ & dJB & dJS).
    apply drawn_F in dru, drv, dkp.
    destruct hp as (hkB & hkS & hnB & h1B & hnS & h1S & hmr).
    pose proof (drawn_indices _ _ _ _ _ hnB dJB) as iB. pose proof (drawn_indices _ _ _ _ _ hnS dJS) as iS.
    rewrite Forall_forall in iB, iS.
    subst P.
    exact (open_complete n1 ell lo1 lo2 kB nB nqB kS nS nqS omB omS pplain a b cin cout sig wr we1 we2 k
             (conj hkB (conj hkS (conj hnB (conj h1B (conj hnS (conj h1S hmr)))))) hw hk hs T dru drv lA lB lC dkp iB iS hwf vals hvals).
  Qed.

End Complete.
