(* Zero knowledge of the opening at the level of transcripts (paper,
   Theorem 5.3, steps (4) to (6)), for one matrix.

   Setting, as in ZkOpen.v: data rows with messages data_i ++ pads_i; nm
   masked vectors, each with a mask message ms_v of length kk that is also
   committed as a mask row; the shifts tfun pads (c times the batched slot
   rows; the gamma-combination of the rows for the proximity test).

   Honest prover, on coins (pads, ms), sends
     mu       = sum_v <ms_v, L_v>
     zs_v     = ms_v + shift_v                      the masked vectors
     ys_i     = the entries of data row i in the opened columns J
     mrows_v  = the entries of mask row v in the opened columns J.

   Simulator, on coins (ys, zs) (uniform), sends
     mu       = sum_v <zs_v, L_v> - cv
     zs, ys
     mrows_v  = enc(zs_v) at J  minus  the shift at J, recomputed from ys.

   Two facts about the honest run are hypotheses; both are the equations
   that the verifier checks, for true claims:
     Hmu   sum_v <shift_v, L_v> = cv        (cv = c * <kappa, values>)
     Hsh   the shifts at the opened columns are a function shJ of the
           opened entries of the data rows.

   Theorems:
     open_honest_sim   the honest transcript on (pads, ms) is the simulated
                       transcript on oview (pads, ms);
     open_zk           the lists of honest and of simulated transcripts
                       over all coins are permutations of each other.

   A mask is one row over F here. In the implementation an F-row is stored
   as two rows over Z_q; that needs the subfield, which this development
   does not have yet. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle Negacyclic Proximity ReedSolomon ZkBlocks ZkSumcheck ZkOpen ZkTranscript.
Import ListNotations.

Section ZkOpenTranscript.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "-" := sub.
  Local Notation pw := (@pw F one mul).
  Local Notation dot := (@dot F zero add mul).
  Local Notation fsum := (@fsum F zero add).
  Local Notation padd := (@padd F add).
  Local Notation vadd := (@vadd F add).
  Local Notation vsub := (@vsub F sub).
  Local Notation lens := (@lens F).
  Local Notation shaped := (@shaped F).

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Variable omega : F.
  Variable n : nat.
  Hypothesis Hnodes : forall i j, (i < n)%nat -> (j < n)%nat -> pw omega i = pw omega j -> i = j.
  Hypothesis Homega : omega <> zero.

  Variable J : list nat.
  Hypothesis HJnd : NoDup J.
  Hypothesis HJ : forall j, In j J -> (j < n)%nat.

  Local Notation rs_enc := (@rs_enc F zero one add mul omega).
  Local Notation opened := (@opened F zero one add mul omega).

  (* a message at the opened columns *)
  Definition encJ (p : list F) : list F := map (fun j => rs_enc p j) J.

  Lemma vsub_vadd : forall x y : list F, length x = length y -> vsub (vadd x y) y = x.
  Proof.
    induction x as [| x0 x ih]; intros y hl; destruct y as [| y0 y]; cbn in hl; try lia; [reflexivity |].
    cbn. rewrite ih by lia. f_equal. field.
  Qed.

  Lemma enc_padd_list : forall (Jl : list nat) p q,
    map (fun j => rs_enc (padd p q) j) Jl = vadd (map (fun j => rs_enc p j) Jl) (map (fun j => rs_enc q j) Jl).
  Proof.
    induction Jl as [| j Jl ih]; intros p q; [reflexivity |].
    cbn [map LogDer.vadd]. rewrite ih. f_equal. unfold ReedSolomon.rs_enc.
    apply (@eval_padd F zero one add mul sub div opp inv Hf).
  Qed.

  Lemma encJ_padd : forall p q, encJ (padd p q) = vadd (encJ p) (encJ q).
  Proof. intros p q. unfold encJ. apply enc_padd_list. Qed.

  Lemma encJ_length : forall p, length (encJ p) = length J.
  Proof. intro p. unfold encJ. apply length_map. Qed.

  Lemma masks_open : forall ms ts : list (list F), length ms = length ts ->
    zipw vsub (map encJ (zipw padd ms ts)) (map encJ ts) = map encJ ms.
  Proof.
    induction ms as [| m0 ms ih]; intros ts hl; destruct ts as [| t ts]; cbn in hl; try lia; [reflexivity |].
    cbn [zipw map]. rewrite encJ_padd, vsub_vadd by (rewrite !encJ_length; reflexivity).
    rewrite ih by lia. reflexivity.
  Qed.

  Lemma mu_split : forall (ms ts Ls : list (list F)), length ms = length ts ->
    fsum (zipw dot (zipw padd ms ts) Ls) = fsum (zipw dot ms Ls) + fsum (zipw dot ts Ls).
  Proof.
    induction ms as [| m0 ms ih]; intros ts Ls hl; destruct ts as [| t ts]; cbn in hl; try lia.
    + cbn. field.
    + destruct Ls as [| L Ls]; [cbn; field |].
      cbn [zipw LogDer.fsum]. rewrite (ih ts Ls ltac:(lia)).
      rewrite (@dot_padd_l F zero one add mul sub div opp inv Hf). field.
  Qed.

  (* shapes *)
  Lemma zipw_length : forall {A B C : Type} (f : A -> B -> C) (la : list A) (lb : list B),
    length la = length lb -> length (zipw f la lb) = length la.
  Proof.
    intros A B C f; induction la as [| x la ih]; intros lb hl; destruct lb as [| y lb]; cbn in hl; try lia;
      [reflexivity |]. cbn. rewrite ih by lia. reflexivity.
  Qed.

  Lemma zipw_Forall : forall {A B C : Type} (f : A -> B -> C) (Q : C -> Prop) (la : list A) (lb : list B),
    (forall x y, Q (f x y)) -> Forall Q (zipw f la lb).
  Proof.
    intros A B C f Q; induction la as [| x la ih]; intros lb h; destruct lb as [| y lb]; cbn; constructor;
      [apply h | apply ih; exact h].
  Qed.

  Lemma shaped_repeat : forall d k (ls : list (list F)), shaped (repeat d k) ls <-> length ls = k /\ lens d ls.
  Proof.
    intros d; induction k as [| k ih]; intro ls; cbn [repeat]; split.
    + intro h. inversion h. split; [reflexivity | constructor].
    + intros [h _]. destruct ls; [constructor | cbn in h; lia].
    + intro h. destruct ls as [| l ls]; [inversion h |].
      apply Forall2_cons_iff in h. destruct h as [hl hls]. apply ih in hls. destruct hls as [h1 h2].
      split; [cbn; lia | constructor; [exact hl | exact h2]].
    + intros [h1 h2]. destruct ls as [| l ls]; [cbn in h1; lia |].
      apply Forall_cons_iff in h2. destruct h2 as [hl hls].
      constructor; [exact hl |]. apply ih. split; [cbn in h1; lia | exact hls].
  Qed.

  (* ------------------------------------------------------------------ *)

  Variable datas : list (list F).
  Variable kk nm : nat.
  Variable tfun : list (list F) -> list (list F).
  Hypothesis Htlen : forall pads, length (tfun pads) = nm.
  Hypothesis Htk : forall pads, Forall (fun t => (length t <= kk)%nat) (tfun pads).

  Variable Ls : list (list F).                         (* the vector of every masked vector *)
  Variable cv : F.
  Variable shJ : list (list F) -> list (list F).
  Hypothesis Hmu : forall pads, length pads = length datas -> lens (length J) pads ->
    fsum (zipw dot (tfun pads) Ls) = cv.
  Hypothesis Hsh : forall pads, length pads = length datas -> lens (length J) pads ->
    map encJ (tfun pads) = shJ (zipw (fun d p => opened d p J) datas pads).

  Local Notation orand := (@orand F).
  Local Notation shaped_orand := (@shaped_orand F J datas kk nm).
  Local Notation oview := (@oview F zero one add mul omega J datas tfun).

  Definition otr : Type := (F * (list (list F) * (list (list F) * list (list F))))%type.

  (* the honest prover of the opening *)
  Definition honO (x : orand) : otr :=
    (fsum (zipw dot (snd x) Ls),
     (zipw padd (snd x) (tfun (fst x)),
      (zipw (fun d p => opened d p J) datas (fst x), map encJ (snd x)))).

  (* the simulator: coins are the opened entries and the masked vectors *)
  Definition simO (v : orand) : otr :=
    (fsum (zipw dot (snd v) Ls) - cv,
     (snd v, (fst v, zipw vsub (map encJ (snd v)) (shJ (fst v))))).

  Theorem open_honest_sim : forall x, shaped_orand x -> honO x = simO (oview x).
  Proof.
    intros [pads ms] (h1 & h2 & h3 & h4). cbn [fst snd] in *.
    unfold honO, simO, ZkOpen.oview. cbn [fst snd].
    assert (hl : length ms = length (tfun pads)) by (rewrite Htlen; exact h3).
    f_equal; [| f_equal; f_equal].
    + rewrite (mu_split ms (tfun pads) Ls hl), (Hmu pads h1 h2). field.
    + rewrite <-(Hsh pads h1 h2). symmetry. apply masks_open. exact hl.
  Qed.

  (* all coins of the right shape *)
  Definition OL : list orand :=
    list_prod (@all_shaped F lf (repeat (length J) (length datas))) (@all_shaped F lf (repeat kk nm)).

  Lemma OL_In : forall x : orand, In x OL <-> shaped_orand x.
  Proof.
    intros [pads ms]. unfold ZkOpen.shaped_orand. cbn [fst snd]. split.
    + intro h. unfold OL in h. apply in_prod_iff in h. destruct h as [hp hm].
      apply (@all_shaped_In F lf Hall) in hp. apply (@all_shaped_In F lf Hall) in hm.
      apply shaped_repeat in hp. apply shaped_repeat in hm. tauto.
    + intros (h1 & h2 & h3 & h4). unfold OL. apply in_prod_iff.
      split; apply (@all_shaped_In F lf Hall); apply shaped_repeat; tauto.
  Qed.

  Lemma OL_NoDup : NoDup OL.
  Proof. unfold OL. apply NoDup_list_prod; apply (@all_shaped_NoDup F lf Hnd). Qed.

  Lemma padd_lens : forall (ms ts : list (list F)), lens kk ms -> Forall (fun t => (length t <= kk)%nat) ts ->
    lens kk (zipw padd ms ts).
  Proof.
    induction ms as [| m0 ms ih]; intros ts hm ht; destruct ts as [| t ts]; cbn [zipw]; try constructor.
    + inversion hm; inversion ht; subst. rewrite (@length_padd F add). lia.
    + inversion hm; inversion ht; subst. apply ih; assumption.
  Qed.

  Lemma oview_shaped : forall x, shaped_orand x -> shaped_orand (oview x).
  Proof.
    intros [pads ms] (h1 & h2 & h3 & h4). unfold ZkOpen.shaped_orand, ZkOpen.oview. cbn [fst snd] in *.
    repeat split.
    + rewrite zipw_length by lia. reflexivity.
    + apply zipw_Forall. intros d p. unfold ReedSolomon.opened. apply length_map.
    + rewrite zipw_length by (rewrite Htlen; exact h3). exact h3.
    + apply padd_lens; [exact h4 | apply Htk].
  Qed.

  (* Theorem 5.3 for the opening of one matrix: the honest transcripts
     over all prover coins and the simulated transcripts over all
     simulator coins are the same multiset. *)
  Theorem open_zk : Permutation (map honO OL) (map simO OL).
  Proof.
    apply (zk_perm oview honO simO OL OL OL_NoDup OL_NoDup).
    + intros x hx. apply OL_In. apply oview_shaped. apply OL_In. exact hx.
    + intros x x' hx hx' e. apply OL_In in hx. apply OL_In in hx'.
      exact (@oview_inj F zero one add mul sub div opp inv Fdec Hf omega n Hnodes Homega J HJnd HJ datas kk nm tfun
               Htlen x x' hx hx' e).
    + intros v hv. apply OL_In in hv.
      destruct (@oview_surj F zero one add mul sub div opp inv Fdec Hf lf Hnd Hall omega n Hnodes Homega J HJnd HJ
                  datas kk nm tfun Htlen Htk v hv) as (x & hx & e).
      exists x. split; [apply OL_In; exact hx | exact e].
    + intros x hx. apply open_honest_sim. apply OL_In. exact hx.
  Qed.

End ZkOpenTranscript.
