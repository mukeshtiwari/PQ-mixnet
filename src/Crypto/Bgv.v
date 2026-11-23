(* BGV ciphertexts and the shuffle relation (paper, Section 2.1), and the
   two facts about them that the shuffle proof uses.

   Everything is stated over one field F. In the protocol the public key,
   the ciphertexts and the witness have coefficients in the prime field
   Z_q, a subfield of F = GF(q^2), and the challenge rho has coordinates
   in F; the identities below hold for arbitrary coefficients in F.

   - proj_rerand is paper equation (1) composed with the projection, in the
     form the protocol needs: the projection of a re-randomised ciphertext
     is the projection of the ciphertext plus an inner product of the
     witness with the public vector rho' = rho * M_pk, whose three blocks
     are rho_r, rho_e1 and rho_e2 ("the verifier's linear algebra").
   - cube_ternary: w^3 = w exactly for w in {-1, 0, 1}, the shortness
     test of sumcheck C. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Negacyclic.
Import ListNotations.

Section Bgv.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation padd := (@padd F add).
  Local Notation pscale := (@pscale F mul).
  Local Notation nmul := (@nmul F zero add mul opp).
  Local Notation nadj := (@nadj F add mul opp).
  Local Notation mul_nonzero := (@mul_nonzero F zero one add mul sub div opp inv Hf).

  (* public key (a, b) and plaintext modulus p *)
  Variables (a b : list F) (p : F).

  Definition ctx : Type := (list F * list F)%type.
  Definition rand : Type := (list F * list F * list F)%type.

  (* Enc_0(w) = (a r + p e1, b r + p e2) for w = (r, e1, e2) *)
  Definition enc0 (w : rand) : ctx :=
    match w with
    | (r, e1, e2) => (padd (nmul a r) (pscale p e1), padd (nmul b r) (pscale p e2))
    end.

  Definition cadd (c c' : ctx) : ctx := (padd (fst c) (fst c'), padd (snd c) (snd c')).

  (* the projection of a ciphertext along rho = (ru, rv) *)
  Definition proj (ru rv : list F) (c : ctx) : F := dot ru (fst c) + dot rv (snd c).

  (* rho' = rho * M_pk, in three blocks *)
  Definition rho_r (ru rv : list F) : list F := padd (nadj a ru) (nadj b rv).
  Definition rho_e1 (ru : list F) : list F := pscale p ru.
  Definition rho_e2 (rv : list F) : list F := pscale p rv.

  Definition wdot (ru rv : list F) (w : rand) : F :=
    match w with
    | (r, e1, e2) => dot (rho_r ru rv) r + dot (rho_e1 ru) e1 + dot (rho_e2 rv) e2
    end.

  Theorem proj_enc0 : forall ru rv r e1 e2,
    length ru = length r -> length rv = length r ->
    proj ru rv (enc0 (r, e1, e2)) = wdot ru rv (r, e1, e2).
  Proof.
    intros ru rv r e1 e2 hu hv. unfold proj, enc0, wdot, rho_r, rho_e1, rho_e2. cbn [fst snd].
    rewrite !dot_padd_r, !dot_pscale_r, dot_padd_l, !dot_pscale_l.
    rewrite (nmul_adjoint a ru r hu), (nmul_adjoint b rv r hv). field.
  Qed.

  Theorem proj_rerand : forall ru rv c r e1 e2,
    length ru = length r -> length rv = length r ->
    proj ru rv (cadd c (enc0 (r, e1, e2))) = proj ru rv c + wdot ru rv (r, e1, e2).
  Proof.
    intros ru rv c r e1 e2 hu hv.
    rewrite <-(proj_enc0 ru rv r e1 e2 hu hv).
    unfold proj, cadd. cbn [fst snd]. rewrite !dot_padd_r. field.
  Qed.

  (* Shortness *)
  Definition tern (x : F) : Prop := x = zero \/ x = one \/ x = opp one.

  Lemma cube_ternary : forall x : F, x * x * x = x <-> tern x.
  Proof.
    intro x; unfold tern; split.
    + intro h.
      destruct (Fdec x zero) as [e0 | e0]; [left; exact e0 |].
      destruct (Fdec x one) as [e1 | e1]; [right; left; exact e1 |].
      right; right.
      destruct (Fdec (x + one) zero) as [e2 | e2].
      - assert (hx : x = (x + one) - one) by field. rewrite hx, e2. field.
      - exfalso.
        assert (h1 : x - one <> zero).
        { intro e. apply e1. assert (hx : x = (x - one) + one) by field. rewrite hx, e. field. }
        apply (mul_nonzero (x * (x - one)) (x + one)); [apply mul_nonzero; assumption | exact e2 |].
        assert (hz : x * (x - one) * (x + one) = x * x * x - x) by field.
        rewrite hz, h. field.
    + intros [-> | [-> | ->]]; field.
  Qed.

  Definition ternary (x : list F) : Prop := Forall tern x.

  (* The shuffle relation R_mix. Output j is input sigma(j), re-randomised
     with the randomness of that input. *)
  Definition Rmix (N tau : nat) (cin cout : list ctx) (sigma : list nat) (ws : list rand) : Prop :=
    length cin = tau /\ length cout = tau /\ length ws = tau /\
    Permutation sigma (seq 0 tau) /\
    (forall r e1 e2, In (r, e1, e2) ws ->
       length r = N /\ length e1 = N /\ length e2 = N /\ ternary r /\ ternary e1 /\ ternary e2) /\
    (forall j, (j < tau)%nat ->
       nth j cout ([], []) =
       cadd (nth (nth j sigma 0%nat) cin ([], [])) (enc0 (nth (nth j sigma 0%nat) ws ([], [], [])))).

End Bgv.
