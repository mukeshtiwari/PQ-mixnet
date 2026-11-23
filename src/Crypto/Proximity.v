(* From lines to affine spaces (paper, Appendix A): the proximity lemma
   (Lemma 4.2) in regime Delta = 3, derived from the line lemma.

   Words are functions nat -> F, of which only the columns j < n matter.
   A code is a predicate on words, closed under addition and scaling,
   invariant under pointwise equality on the columns, and of distance d:
   two codewords that agree outside fewer than d columns agree everywhere.

   LineLemma is a hypothesis of the section. It is the statement of
   Diamond and Posen, Theorem 2.1 (attributed to Roth and Zemor): if more
   than e + 1 points of the line x + t y are within distance e of the
   code, then x and y agree with codewords outside a common set of at
   most e columns.

   Theorem prox_affine. Let m be a word and rows a list of R words. If
   the number of gamma in F^R for which m + sum_i gamma_i row_i is within
   distance e of the code exceeds (e + 2) |F|^(R-1), then there is one
   set E of at most e columns outside which m and every row agree with
   codewords.

   This is the contrapositive of Lemma 4.2 with eps_prox = (e + 2)/|F|.

   The proof follows the appendix in its first step and replaces the
   second (the "affine space of error vectors") by an induction:
   1. all_close: every point of the affine space is close. Averaging over
      the lines through a point (count_swap) yields a line with at least
      e + 2 close points, and the line lemma applies.
   2. affine_decode: decoding is affine. There are codewords cm, cs with
      m + sum gamma_i row_i within e of cm + sum gamma_i cs_i for all gamma.
   3. The columns where some error m - cm, row_i - cs_i is non-zero number
      at most e: otherwise e + 1 of them give e + 1 non-zero affine forms
      in gamma, which have a common non-vanishing point because
      e + 1 < |F|, and the error at that point has weight above e. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
From Crypto Require Import PolyRoots.
From Crypto Require Import Counting LogDer Mle.
Import ListNotations.

Section Proximity.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation dot := (@dot F zero add mul).
  Local Notation vsub := (@vsub F sub).
  Local Notation shift := (@shift F add mul).
  Local Notation allzero := (@allzero F zero Fdec).
  Local Notation feqb := (@feqb F Fdec).
  Local Notation feqb_true := (@feqb_true F Fdec).

  Lemma dot_comm : forall a b : list F, dot a b = dot b a.
  Proof.
    induction a as [| x a ih]; intro b; destruct b as [| y b]; cbn; try reflexivity.
    rewrite ih; field.
  Qed.

  Lemma vsub_allzero_eq : forall a b : list F, length a = length b ->
    allzero (vsub a b) = true -> a = b.
  Proof.
    induction a as [| x a ih]; intros b hl hz; destruct b as [| y b]; cbn in *; try lia; [reflexivity |].
    destruct (Fdec (x - y) zero) as [e | e]; [| discriminate]. cbn in hz.
    f_equal; [| apply ih; [lia | exact hz]].
    assert (h : x = (x - y) + y) by field. rewrite h, e; field.
  Qed.

  Lemma shift_dir_inj : forall t : F, t <> zero -> forall g0 x y : list F,
    length x = length g0 -> length y = length g0 ->
    shift x t g0 = shift y t g0 -> x = y.
  Proof.
    intros t ht0; unfold LogDer.shift; induction g0 as [| a g ihg]; intros x y hx hy exy;
      destruct x as [| x0 x], y as [| y0 y]; cbn in *; try lia; [reflexivity |].
    inversion exy as [[e1 e2]]. f_equal.
    + assert (h : x0 = inv t * ((a + t * x0) - a)) by (field; exact ht0).
      rewrite h, e1; field; exact ht0.
    + apply ihg; [lia | lia | exact e2].
  Qed.

  (* Fewer than |lf| non-zero affine forms k + dot g gamma have a common
     point at which none of them vanishes. *)
  Lemma affine_common_nonzero : forall (lf : list F), NoDup lf ->
    forall (R : nat) (gs : list (F * list F)),
    (forall kg, In kg gs -> length (snd kg) = R /\ (fst kg <> zero \/ allzero (snd kg) = false)) ->
    (length gs < length lf)%nat ->
    exists c, length c = R /\ forall kg, In kg gs -> fst kg + dot (snd kg) c <> zero.
  Proof.
    intros lf hnd; induction R as [| R ih]; intros gs hgs hlen.
    + exists []; split; [reflexivity |]. intros [k g] hg e.
      destruct (hgs (k, g) hg) as [hl hz]. cbn in *. destruct g; [| discriminate].
      destruct hz as [hz | hz]; [| cbn in hz; discriminate].
      apply hz. rewrite <-e. cbn. field.
    + set (isz := fun k : F => if Fdec k zero then true else false).
      set (keep := filter (fun kg : F * list F => negb (isz (fst kg) && allzero (tl (snd kg)))) gs).
      set (tails := map (fun kg : F * list F => (fst kg, tl (snd kg))) keep).
      assert (hk : forall kg, In kg tails -> length (snd kg) = R /\ (fst kg <> zero \/ allzero (snd kg) = false)).
      { intros kt ht. apply in_map_iff in ht; destruct ht as ([k g] & <- & hg).
        apply filter_In in hg; destruct hg as [hg hnz]. cbn in *.
        destruct (hgs (k, g) hg) as [hl _]. cbn in hl. split.
        + destruct g; cbn in *; lia.
        + unfold isz in hnz. destruct (Fdec k zero) as [hk0 | hk0]; [right | left; exact hk0].
          cbn in hnz. destruct (allzero (tl g)) eqn:ea; [discriminate | exact ea]. }
      assert (hkl : (length tails < length lf)%nat).
      { unfold tails, keep. rewrite length_map.
        pose proof (filter_length_le (fun kg : F * list F => negb (isz (fst kg) && allzero (tl (snd kg)))) gs). lia. }
      destruct (ih tails hk hkl) as (c' & hc' & hgood).
      set (bad := map (fun kg : F * list F => opp (fst kg + dot (tl (snd kg)) c') * inv (hd zero (snd kg))) gs).
      assert (hbl : (length bad < length lf)%nat) by (unfold bad; rewrite length_map; exact hlen).
      destruct (@pigeonhole_notin F Fdec lf bad hnd hbl) as (x & _ & hx).
      exists (x :: c'); split; [cbn; lia |].
      intros [k g] hg e. destruct (hgs (k, g) hg) as [hl hnz]. cbn in hl, hnz, e.
      destruct g as [| h t]; [discriminate |]. cbn in e, hl.
      destruct (Fdec h zero) as [hh | hh].
      - subst h. assert (e' : k + dot t c' = zero) by (transitivity (k + (zero * x + dot t c')); [field | exact e]).
        apply (hgood (k, t)); [| exact e'].
        unfold tails. apply in_map_iff; exists (k, zero :: t); split; [reflexivity |].
        apply filter_In; split; [exact hg |]. cbn. unfold isz.
        destruct (Fdec k zero) as [hk0 | hk0]; [| reflexivity]. cbn.
        destruct hnz as [hnz | hnz]; [contradiction |].
        cbn in hnz. destruct (Fdec zero zero) as [_ | nn]; [| contradiction]. cbn in hnz.
        rewrite hnz; reflexivity.
      - apply hx. unfold bad. apply in_map_iff. exists (k, h :: t); split; [| exact hg]. cbn.
        assert (e1 : h * x = opp (k + dot t c')).
        { assert (h1 : h * x = (k + (h * x + dot t c')) - (k + dot t c')) by field. rewrite h1, e; field. }
        rewrite <-e1; field; exact hh.
  Qed.

  (* ------------------------------------------------------------------ *)

  Section Affine.

  Variable lf : list F.
  Hypothesis Hnd : NoDup lf.
  Hypothesis Hall : forall x, In x lf.

  Variables n d e : nat.
  Variable code : (nat -> F) -> Prop.

  Hypothesis code_ext : forall c c', (forall j, (j < n)%nat -> c j = c' j) -> code c -> code c'.
  Hypothesis code_add : forall c1 c2, code c1 -> code c2 -> code (fun j => c1 j + c2 j).
  Hypothesis code_scale : forall t c, code c -> code (fun j => t * c j).
  Hypothesis code_dist : forall c1 c2 (E : list nat), code c1 -> code c2 -> (length E < d)%nat ->
    (forall j, (j < n)%nat -> ~ In j E -> c1 j = c2 j) -> forall j, (j < n)%nat -> c1 j = c2 j.
  Hypothesis He : (2 * e < d)%nat.
  Hypothesis Hq : (e + 1 < length lf)%nat.

  Definition agree_out (E : list nat) (x c : nat -> F) : Prop :=
    forall j, (j < n)%nat -> ~ In j E -> x j = c j.

  Definition close (x : nat -> F) : Prop :=
    exists c E, code c /\ (length E <= e)%nat /\ agree_out E x c.

  Hypothesis LineLemma : forall (x y : nat -> F) (ts : list F),
    NoDup ts -> (e + 1 < length ts)%nat ->
    (forall t, In t ts -> close (fun j => x j + t * y j)) ->
    exists E cx cy, (length E <= e)%nat /\ code cx /\ code cy /\ agree_out E x cx /\ agree_out E y cy.

  Lemma close_ext : forall x x', (forall j, (j < n)%nat -> x j = x' j) -> close x -> close x'.
  Proof.
    intros x x' hx (c & E & hc & hE & ha). exists c, E; split; [exact hc | split; [exact hE |]].
    intros j hj hn; rewrite <-(hx j hj); exact (ha j hj hn).
  Qed.

  Lemma code_unique : forall x c1 c2 E1 E2, code c1 -> code c2 ->
    (length E1 <= e)%nat -> (length E2 <= e)%nat -> agree_out E1 x c1 -> agree_out E2 x c2 ->
    forall j, (j < n)%nat -> c1 j = c2 j.
  Proof.
    intros x c1 c2 E1 E2 h1 h2 l1 l2 a1 a2.
    apply (code_dist c1 c2 (E1 ++ E2) h1 h2); [rewrite length_app; lia |].
    intros j hj hn. rewrite <-(a1 j hj), <-(a2 j hj); [reflexivity | |]; intro i; apply hn, in_or_app; tauto.
  Qed.

  (* The affine combination m + sum_i gamma_i rows_i, column by column. *)
  Definition lin (rows : list (nat -> F)) (g : list F) (j : nat) : F :=
    dot g (map (fun r => r j) rows).

  Definition pi (m : nat -> F) (rows : list (nat -> F)) (g : list F) (j : nat) : F :=
    m j + lin rows g j.

  Lemma lin_shift : forall rows dl t g0 j, length g0 = length dl ->
    lin rows (shift dl t g0) j = lin rows g0 j + t * lin rows dl j.
  Proof.
    intros rows dl t g0 j hl. unfold lin.
    rewrite (dot_comm (shift dl t g0)), dot_shift by exact hl.
    rewrite (dot_comm g0), (dot_comm dl). field.
  Qed.

  Lemma code_pi : forall cs cm g, code cm -> Forall code cs -> code (pi cm cs g).
  Proof.
    induction cs as [| c cs ih]; intros cm g hcm hcs.
    + apply (code_ext cm); [| exact hcm]. intros j _. unfold pi, lin. destruct g; cbn; field.
    + inversion hcs as [| ? ? hc hcs']; subst. destruct g as [| x g].
      - apply (code_ext cm); [| exact hcm]. intros j _. unfold pi, lin. cbn; field.
      - apply (code_ext (pi (fun j => cm j + x * c j) cs g)).
        * intros j _. unfold pi, lin. cbn. field.
        * apply ih; [| exact hcs']. apply code_add; [exact hcm | apply code_scale; exact hc].
  Qed.

  (* Step 1: every point of the affine space is close. *)
  Lemma all_close : forall (m : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close (pi m rows g)) ->
    ((e + 2) * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    forall g0, length g0 = length rows -> close (pi m rows g0).
  Proof.
    intros m rows cl hcl hmany g0 hg0.
    set (R := length rows) in *.
    set (X := all_lists lf R).
    set (lt := filter (fun t => if Fdec t zero then false else true) lf).
    set (cnt := length (filter cl X)) in *.
    assert (hlt : (length lf <= S (length lt))%nat).
    { apply (NoDup_incl_length (l' := zero :: lt) Hnd).
      intros x _. destruct (Fdec x zero) as [-> | hx]; [left; reflexivity | right].
      apply filter_In; split; [apply Hall | destruct (Fdec x zero); [contradiction | reflexivity]]. }
    assert (hltnz : forall t, In t lt -> t <> zero).
    { intros t ht. apply filter_In in ht; destruct ht as [_ ht].
      destruct (Fdec t zero); [discriminate | assumption]. }
    set (gcount := fun dl => length (filter (fun t => cl (shift dl t g0)) lt)).
    assert (hsum : nsum (map gcount X) = (cnt * length lt)%nat).
    { unfold gcount. rewrite (count_swap (fun dl t => cl (shift dl t g0)) X lt).
      rewrite <-(nsum_map_const cnt lt).
      apply nsum_map_ext; intros t ht. unfold cnt.
      rewrite <-(filter_map_length cl (fun dl => shift dl t g0) X).
      apply filter_length_perm, map_self_perm.
      + apply all_lists_NoDup; exact Hnd.
      + intros x hx. apply all_lists_In in hx; destruct hx as [hx _].
        apply all_lists_In; split; [rewrite shift_length; lia |].
        apply Forall_forall; intros y _; apply Hall.
      + intros x y hx hy exy.
        apply all_lists_In in hx; destruct hx as [hx _].
        apply all_lists_In in hy; destruct hy as [hy _].
        apply (shift_dir_inj t (hltnz t ht) g0); [lia | lia | exact exy]. }
    (* some direction has at least e + 2 close points *)
    assert (hdir : exists dl, In dl X /\ (e + 2 <= gcount dl)%nat).
    { destruct (Exists_dec (fun dl => (e + 2 <= gcount dl)%nat) X) as [h | h].
      + intro dl; destruct (le_dec (e + 2) (gcount dl)); [left | right]; assumption.
      + apply Exists_exists in h; exact h.
      + exfalso.
        assert (hle : (nsum (map gcount X) <= (e + 1) * length X)%nat).
        { apply nsum_map_le; intros dl hdl.
          destruct (le_dec (e + 2) (gcount dl)) as [h2 | h2]; [| lia].
          exfalso; apply h; apply Exists_exists; exists dl; split; assumption. }
        rewrite hsum in hle. unfold X in hle. rewrite all_lists_length in hle.
        set (q := length lf) in *. set (P := (q ^ R)%nat) in *.
        assert (hq1 : (cnt * q <= cnt * length lt + cnt)%nat) by nia.
        assert (hcnt : (cnt <= P)%nat).
        { unfold cnt, P, q, X. rewrite <-(all_lists_length lf R). apply filter_length_le. }
        (* (e+2) P < cnt q <= (e+1) P + cnt <= (e+1) P + P *)
        fold X in hmany. fold cnt in hmany. fold q in hmany. fold P in hmany.
        lia. }
    destruct hdir as (dl & hdl & hcount).
    apply all_lists_In in hdl; destruct hdl as [hdl _].
    destruct (LineLemma (pi m rows g0) (lin rows dl) (filter (fun t => cl (shift dl t g0)) lt))
      as (E & cx & cy & hE & hcx & _ & hax & _).
    + apply NoDup_filter, NoDup_filter; exact Hnd.
    + unfold gcount in hcount; lia.
    + intros t ht. apply filter_In in ht; destruct ht as [_ ht].
      apply (close_ext (pi m rows (shift dl t g0))); [| apply hcl; exact ht].
      intros j _. unfold pi. rewrite lin_shift by lia. field.
    + exists cx, E; tauto.
  Qed.

  (* Step 2: decoding is affine. *)
  Lemma affine_decode : forall (rows : list (nat -> F)) (m : nat -> F),
    (forall g, length g = length rows -> close (pi m rows g)) ->
    exists cm cs, code cm /\ Forall code cs /\ length cs = length rows /\
      forall g, length g = length rows ->
        exists E, (length E <= e)%nat /\ agree_out E (pi m rows g) (pi cm cs g).
  Proof.
    induction rows as [| r rows ih]; intros m hall.
    + destruct (hall [] eq_refl) as (c & E & hc & hE & ha).
      exists c, []; split; [exact hc | split; [constructor | split; [reflexivity |]]].
      intros g hg. destruct g; [| discriminate]. exists E; split; [exact hE |].
      intros j hj hn. specialize (ha j hj hn). unfold pi, lin in ha |- *. cbn in ha |- *.
      rewrite ha; field.
    + assert (hall' : forall g, length g = length rows -> close (pi m rows g)).
      { intros g hg. apply (close_ext (pi m (r :: rows) (zero :: g))); [| apply hall; cbn; lia].
        intros j _. unfold pi, lin. cbn. field. }
      destruct (ih m hall') as (cm & cs & hcm & hcs & hcl & hdec).
      (* the line through m + lin rows g with direction r *)
      assert (hline : forall g, length g = length rows ->
        exists E cx cy, (length E <= e)%nat /\ code cx /\ code cy /\
          agree_out E (pi m rows g) cx /\ agree_out E r cy).
      { intros g hg. apply (LineLemma (pi m rows g) r lf Hnd Hq).
        intros t _. apply (close_ext (pi m (r :: rows) (t :: g))); [| apply hall; cbn; lia].
        intros j _. unfold pi, lin. cbn. field. }
      destruct (hline (repeat zero (length rows)) (repeat_length _ _)) as (E0 & _ & cr & hE0 & _ & hcr & _ & har).
      exists cm, (cr :: cs). split; [exact hcm | split; [constructor; assumption | split; [cbn; lia |]]].
      intros g hg. destruct g as [| x g]; [discriminate |]. cbn in hg.
      assert (hg' : length g = length rows) by lia.
      destruct (hline g hg') as (E & cx & cy & hE & hcx & hcy & hax & hay).
      destruct (hdec g hg') as (E1 & hE1 & ha1).
      assert (ex : forall j, (j < n)%nat -> cx j = pi cm cs g j).
      { apply (code_unique (pi m rows g) cx (pi cm cs g) E E1); try assumption.
        apply code_pi; assumption. }
      assert (ey : forall j, (j < n)%nat -> cy j = cr j).
      { apply (code_unique r cy cr E E0); assumption. }
      exists E; split; [exact hE |].
      intros j hj hn. specialize (hax j hj hn). specialize (hay j hj hn).
      specialize (ex j hj). specialize (ey j hj).
      unfold pi, lin in *. cbn.
      assert (h1 : m j + (x * r j + dot g (map (fun r0 => r0 j) rows))
                   = (m j + dot g (map (fun r0 => r0 j) rows)) + x * r j) by field.
      rewrite h1, hax, hay, ex, ey. field.
  Qed.

  Lemma rows_agree : forall (E : list nat) (rows cs : list (nat -> F)),
    length rows = length cs -> Forall code cs ->
    (forall j, (j < n)%nat -> ~ In j E -> map (fun r => r j) rows = map (fun c => c j) cs) ->
    Forall2 (fun r c => code c /\ agree_out E r c) rows cs.
  Proof.
    intros E; induction rows as [| r rows ih]; intros cs hl hcs hmap; destruct cs as [| c cs]; cbn in hl; try lia.
    + constructor.
    + inversion hcs as [| ? ? hc hcs']; subst. constructor.
      - split; [exact hc |]. intros j hj hn. specialize (hmap j hj hn). cbn in hmap. inversion hmap; reflexivity.
      - apply ih; [lia | exact hcs' |]. intros j hj hn. specialize (hmap j hj hn). cbn in hmap. inversion hmap; reflexivity.
  Qed.

  (* Lemma 4.2, regime Delta = 3, contrapositive form. *)
  Theorem prox_affine : forall (m : nat -> F) (rows : list (nat -> F)) (cl : list F -> bool),
    (forall g, cl g = true -> close (pi m rows g)) ->
    ((e + 2) * length lf ^ length rows < length (filter cl (all_lists lf (length rows))) * length lf)%nat ->
    exists (E : list nat) (cm : nat -> F) (cs : list (nat -> F)),
      (length E <= e)%nat /\ code cm /\ agree_out E m cm /\
      Forall2 (fun r c => code c /\ agree_out E r c) rows cs.
  Proof.
    intros m rows cl hcl hmany.
    pose proof (all_close m rows cl hcl hmany) as hclose.
    destruct (affine_decode rows m hclose) as (cm & cs & hcm & hcs & hlen & hdec).
    set (kj := fun j => m j - cm j).
    set (gj := fun j => vsub (map (fun r => r j) rows) (map (fun c => c j) cs)).
    set (isz := fun k : F => if Fdec k zero then true else false).
    set (J := filter (fun j => negb (isz (kj j) && allzero (gj j))) (seq 0 n)).
    assert (hJnd : NoDup J) by (apply NoDup_filter, seq_NoDup).
    assert (hgl : forall j, length (gj j) = length rows).
    { intro j. unfold gj. rewrite vsub_length; rewrite !length_map; lia. }
    assert (hform : forall g j, length g = length rows ->
      pi m rows g j - pi cm cs g j = kj j + dot (gj j) g).
    { intros g j hg. unfold pi, lin, kj, gj.
      rewrite dot_vsub by (rewrite !length_map; lia).
      rewrite (dot_comm g (map (fun r => r j) rows)), (dot_comm g (map (fun c => c j) cs)). field. }
    assert (hJle : (length J <= e)%nat).
    { destruct (le_dec (length J) e) as [h | h]; [exact h | exfalso].
      set (J1 := firstn (e + 1) J).
      assert (hJ1len : length J1 = (e + 1)%nat) by (unfold J1; rewrite length_firstn; lia).
      assert (hJ1nd : NoDup J1) by (unfold J1; apply (NoDup_app_remove_r _ (skipn (e + 1) J)); rewrite firstn_skipn; exact hJnd).
      assert (hJ1in : forall j, In j J1 -> In j J) by (intros j hj; rewrite <-(firstn_skipn (e + 1) J); apply in_or_app; left; exact hj).
      set (gs := map (fun j => (kj j, gj j)) J1).
      assert (hgs : forall kg, In kg gs ->
        length (snd kg) = length rows /\ (fst kg <> zero \/ allzero (snd kg) = false)).
      { intros kg hkg. apply in_map_iff in hkg; destruct hkg as (j & <- & hj). cbn.
        split; [apply hgl |].
        apply hJ1in, filter_In in hj; destruct hj as [_ hj]. unfold isz in hj.
        destruct (Fdec (kj j) zero) as [e0 | e0]; [right | left; exact e0].
        cbn in hj. destruct (allzero (gj j)) eqn:ea; [discriminate | exact ea]. }
      assert (hgslen : (length gs < length lf)%nat) by (unfold gs; rewrite length_map; lia).
      destruct (affine_common_nonzero lf Hnd (length rows) gs hgs hgslen) as (g & hg & hnz).
      destruct (hdec g hg) as (E & hE & ha).
      assert (hincl : incl J1 E).
      { intros j hj. destruct (in_dec Nat.eq_dec j E) as [i | i]; [exact i | exfalso].
        assert (hjn : (j < n)%nat).
        { apply hJ1in, filter_In in hj; destruct hj as [hj _]. apply in_seq in hj; lia. }
        apply (hnz (kj j, gj j)); [unfold gs; apply in_map_iff; exists j; split; [reflexivity | exact hj] |].
        cbn. rewrite <-(hform g j hg), (ha j hjn i). field. }
      pose proof (NoDup_incl_length hJ1nd hincl). lia. }
    exists J, cm, cs. split; [exact hJle | split; [exact hcm |]].
    assert (hout : forall j, (j < n)%nat -> ~ In j J ->
      kj j = zero /\ map (fun r => r j) rows = map (fun c => c j) cs).
    { intros j hj hn.
      assert (hb : negb (isz (kj j) && allzero (gj j)) = false).
      { destruct (negb (isz (kj j) && allzero (gj j))) eqn:eb; [| reflexivity].
        exfalso; apply hn. apply filter_In; split; [apply in_seq; lia | exact eb]. }
      apply negb_false_iff, andb_true_iff in hb; destruct hb as [hk hg].
      unfold isz in hk. destruct (Fdec (kj j) zero) as [e0 | e0]; [| discriminate].
      split; [exact e0 |].
      apply vsub_allzero_eq; [rewrite !length_map; lia | exact hg]. }
    split.
    + intros j hj hn. destruct (hout j hj hn) as [hk _]. unfold kj in hk.
      assert (h : m j = (m j - cm j) + cm j) by field. rewrite h, hk; field.
    + apply rows_agree; [lia | exact hcs |]. intros j hj hn. exact (proj2 (hout j hj hn)).
  Qed.

  End Affine.

  Section Columns.

  Variables n d : nat.
  Variable code : (nat -> F) -> Prop.
  Hypothesis code_dist : forall c1 c2 (E : list nat), code c1 -> code c2 -> (length E < d)%nat ->
    (forall j, (j < n)%nat -> ~ In j E -> c1 j = c2 j) -> forall j, (j < n)%nat -> c1 j = c2 j.

  (* Lemma 4.3 (consistency). Let the committed combination x agree with the
     codeword cdec outside E, and let the prover send a different codeword
     cu. Then the columns j < n at which cu passes the check cu j = x j
     number at most n - d + |E|: a random column passes with probability
     at most 1 - (d - |E|)/n. *)
  Theorem consistency : forall (x cu cdec : nat -> F) (E : list nat),
    code cu -> code cdec -> agree_out n E x cdec ->
    (exists j, (j < n)%nat /\ cu j <> cdec j) ->
    (length (filter (fun j => feqb (cu j) (x j)) (seq 0 n)) + d <= n + length E)%nat.
  Proof.
    intros x cu cdec E hcu hcdec hagree (j0 & hj0 & hne).
    set (pass := fun j => feqb (cu j) (x j)).
    set (D := filter (fun j => negb (feqb (cu j) (cdec j))) (seq 0 n)).
    assert (hDd : (d <= length D)%nat).
    { destruct (le_dec d (length D)) as [h | h]; [exact h | exfalso].
      apply hne. apply (code_dist cu cdec D hcu hcdec ltac:(lia)); [| exact hj0].
      intros j hj hn.
      destruct (Fdec (cu j) (cdec j)) as [e0 | e0]; [exact e0 | exfalso].
      apply hn. apply filter_In; split; [apply in_seq; lia |].
      destruct (feqb (cu j) (cdec j)) eqn:eb; [apply feqb_true in eb; contradiction | reflexivity]. }
    assert (hincl : incl D (filter (fun j => negb (pass j)) (seq 0 n) ++ E)).
    { intros j hj. apply filter_In in hj; destruct hj as [hjs hjd].
      apply in_or_app.
      destruct (pass j) eqn:ep.
      + right. destruct (in_dec Nat.eq_dec j E) as [i | i]; [exact i | exfalso].
        apply in_seq in hjs. unfold pass in ep. apply feqb_true in ep.
        assert (e1 : cu j = cdec j) by (rewrite ep; apply hagree; [lia | exact i]).
        apply feqb_true in e1. rewrite e1 in hjd. discriminate.
      + left. apply filter_In; split; [exact hjs | rewrite ep; reflexivity]. }
    assert (hDnd : NoDup D) by (apply NoDup_filter, seq_NoDup).
    pose proof (NoDup_incl_length hDnd hincl) as hlen. rewrite length_app in hlen.
    pose proof (filter_partition_length pass (seq 0 n)) as hpart. rewrite length_seq in hpart.
    fold pass. lia.
  Qed.

  (* If the committed word is not within distance e of the code, any
     codeword the prover sends agrees with it on fewer than n - e columns. *)
  Theorem far_few_pass : forall (e : nat) (x cu : nat -> F),
    ~ close n e code x -> code cu ->
    (length (filter (fun j => feqb (cu j) (x j)) (seq 0 n)) + e < n)%nat.
  Proof.
    intros e x cu hfar hcu.
    set (pass := fun j => feqb (cu j) (x j)).
    destruct (lt_dec (length (filter pass (seq 0 n)) + e) n) as [h | h]; [exact h | exfalso].
    apply hfar. exists cu, (filter (fun j => negb (pass j)) (seq 0 n)).
    split; [exact hcu | split].
    + pose proof (filter_partition_length pass (seq 0 n)) as hp. rewrite length_seq in hp. lia.
    + intros j hj hn. unfold pass in hn.
      destruct (feqb (cu j) (x j)) eqn:eb.
      - apply feqb_true in eb. symmetry; exact eb.
      - exfalso; apply hn. apply filter_In; split; [apply in_seq; lia | rewrite eb; reflexivity].
  Qed.

  End Columns.

End Proximity.
