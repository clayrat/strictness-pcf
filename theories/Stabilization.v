(** * Stabilization: finite-order theory instantiated for abstract PCF values

    The abstract fixpoint algorithm relies on the fact that the
    iteration [a₀ = ⊥, a_{k+1} = F♯(a_k)] has stabilized after [dsize A]
    steps. [FiniteOrder.v] proves the representation-independent order
    theory; this file proves that the concrete [aval] tables satisfy its
    interfaces and exposes the resulting PCF-specific theorems:

    - [afix_receipt]: for every functional [F] in the enumerated (hence
      monotone) carrier, [afix_approx A F (dsize A)] is a genuine fixpoint
      of [aapply F];
    - [afix_least]: it is the *least* one — the analysis computes lfp(F♯),
      not merely some fixpoint;
    - [ajoin_left], [ajoin_right], and [ajoin_least] characterize [ajoin]
      as the carrier's least upper bound; closure, monotonicity,
      associativity, commutativity, idempotence, and the bottom laws follow;
    - the hypothesis [In F (enum (A ⇒ A))] is exactly what Tests.v's
      [not_table] lacks: on that non-monotone table the iteration provably
      oscillates, so the receipt is sharp.

    The generic proof is the finite measure argument: [upper_size a] counts
    the carrier elements above [a]; a monotone step either fixes [a] or
    strictly shrinks the count. Here [upsize] specializes that measure and
    [enum_le_dsize] supplies the analyser's deliberately loose budget.

    This layer deliberately stops before operational semantics. The next,
    [AnalysisCorrectness.v], proves mutually for the bidirectional judgments
    that [aeval] returns carrier values and is monotone in ordered abstract
    environments. In particular, the receipt above applies to every [F] a
    checked program's [fix] actually produces.

    What remains unproved is operational semantic soundness — "if
    [f♯(⊥) = ⊥] then [f · u] diverges for every diverging [u]" — which
      needs a logical relation between [aval] and
      terms, indexed by [evalFuel]'s step budget to handle [fix] (the
      step-index replaces domain-theoretic admissibility, so no CPO library
      is needed). That remains a substantial separate development; Tests.v
      certifies the current examples operationally instead. *)

From Stdlib Require Import String Bool List Arith Lia.
From Equations Require Import Equations.
Import ListNotations.
From PCF Require Import Ty Strictness FiniteOrder.

Open Scope ty_scope.

(** ** Boolean equality is equality *)

Lemma aval_eqb_refl : forall A (v : aval A), aval_eqb v v = true.
Proof.
  induction A as [| A1 IH1 A2 IH2]; intros v; dependent elimination v.
  - destruct b; reflexivity.
  - simp aval_eqb.
    induction l as [| [a b] tbl IHt]; [reflexivity |].
    simpl. rewrite IH1, IH2, IHt. reflexivity.
Qed.

Lemma aval_eqb_eq : forall A (v w : aval A), aval_eqb v w = true -> v = w.
Proof.
  induction A as [| A1 IH1 A2 IH2]; intros v w E;
    dependent elimination v; dependent elimination w; simp aval_eqb in E.
  - destruct b, b0; simpl in E; congruence.
  - f_equal. revert l0 E.
    induction l as [| [a b] ts IHt]; intros [| [a' b'] us] E;
      try discriminate; [reflexivity |].
    apply andb_prop in E as [E1 E3]. apply andb_prop in E1 as [E1 E2].
    rewrite (IH1 _ _ E1), (IH2 _ _ E2). f_equal.
    apply IHt, E3.
Qed.

(** ** The pointwise order: preorder in general *)

Lemma aleb_refl : forall A (v : aval A), aleb v v = true.
Proof.
  induction A as [| A1 IH1 A2 IH2]; intros v; dependent elimination v.
  - destruct b; reflexivity.
  - simp aleb.
    induction l as [| [a b] tbl IHt]; [reflexivity |].
    simpl. rewrite IH2, IHt. reflexivity.
Qed.

Lemma aleb_trans : forall A (u v w : aval A),
  aleb u v = true -> aleb v w = true -> aleb u w = true.
Proof.
  induction A as [| A1 IH1 A2 IH2]; intros u v w E1 E2;
    dependent elimination u; dependent elimination v; dependent elimination w;
    simp aleb in *; auto.
  - destruct b, b0, b1; simpl in *; congruence.
  - assert (Key : forall (ts us vs : list (aval A * aval B)),
        table_leb (@aleb B) ts us = true ->
        table_leb (@aleb B) us vs = true ->
        table_leb (@aleb B) ts vs = true).
    { clear -IH2. induction ts as [| [a b] ts' IHt]; intros us vs E1 E2.
      - destruct us as [| p us]; simpl in *; [| discriminate].
        destruct vs as [| q vs]; simpl in *; [reflexivity | discriminate].
      - destruct us as [| [a2 b2] us]; simpl in *; [discriminate |].
        destruct vs as [| [a3 b3] vs]; simpl in *; [discriminate |].
        apply andb_prop in E1 as [E1a E1b].
        apply andb_prop in E2 as [E2a E2b].
        apply andb_true_intro. split.
        + exact (IH2 _ _ _ E1a E2a).
        + exact (IHt us vs E1b E2b). }
    exact (Key l l0 l1 E1 E2).
Qed.

(** ** The canonical carrier

    Inversion of membership in [enum]: at ℕ the two points, at an arrow a
    monotone table whose keys are exactly [enum A₁] and whose outputs live
    in [enum A₂]. Antisymmetry holds *on the carrier* (in general [aleb]
    ignores keys, so it is only a preorder). *)

Lemma all_tables_keys : forall (I O : Type) (ins : list I) (outs : list O)
  (tbl : list (I * O)),
  In tbl (all_tables ins outs) -> map fst tbl = ins.
Proof.
  intros I O. induction ins as [| i ins' IH]; intros outs tbl Hin; simpl in Hin.
  - destruct Hin as [<- | []]. reflexivity.
  - apply in_flat_map in Hin as (o & _ & Hin).
    apply in_map_iff in Hin as (tbl' & <- & Hin').
    simpl. f_equal. eauto.
Qed.

Lemma all_tables_outs : forall (I O : Type) (ins : list I) (outs : list O)
  (tbl : list (I * O)),
  In tbl (all_tables ins outs) ->
  forall a b, In (a, b) tbl -> In b outs.
Proof.
  intros I O. induction ins as [| i ins' IH];
    intros outs tbl Hin a b Hab; simpl in Hin.
  - destruct Hin as [<- | []]. destruct Hab.
  - apply in_flat_map in Hin as (o & Ho & Hin).
    apply in_map_iff in Hin as (tbl' & <- & Hin').
    destruct Hab as [E | Hab].
    + injection E as <- <-. exact Ho.
    + eauto.
Qed.

(** The converse used by lambda tabulation: one carrier-valued output for
    every input is one of the tables generated by [all_tables]. *)
Lemma all_tables_complete : forall (I O : Type) (ins : list I) (outs : list O)
  (tbl : list (I * O)),
  map fst tbl = ins ->
  (forall a b, In (a, b) tbl -> In b outs) ->
  In tbl (all_tables ins outs).
Proof.
  intros I O. induction ins as [| i ins IH]; intros outs tbl K Hout.
  - destruct tbl as [| [a b] tbl]; simpl in K; [simpl; auto | discriminate].
  - destruct tbl as [| [a b] tbl]; simpl in K; [discriminate |].
    injection K as <- K.
    simpl. apply in_flat_map. exists b. split.
    + apply (Hout a b). left. reflexivity.
    + apply in_map_iff. exists tbl. split; [reflexivity |].
      apply IH; [exact K |].
      intros a' b' Hin. eapply Hout. right. exact Hin.
Qed.

(** Zipping aligned canonical tables preserves their keys, and every result
    row comes from joining the two rows at the same position. *)
Lemma join_tables_keys : forall (I O : Type) (joinO : O -> O -> O)
  (ts us : list (I * O)),
  map fst ts = map fst us ->
  map fst (join_tables joinO ts us) = map fst ts.
Proof.
  intros I O joinO. induction ts as [| [a b] ts IH];
    intros [| [a' b'] us] K; simpl in *; try discriminate; [reflexivity |].
  injection K as <- K. simpl. f_equal. apply IH, K.
Qed.

Lemma join_tables_row : forall (I O : Type) (joinO : O -> O -> O)
  (ts us : list (I * O)) a d,
  map fst ts = map fst us ->
  In (a, d) (join_tables joinO ts us) ->
  exists b c,
    In (a, b) ts /\ In (a, c) us /\ d = joinO b c.
Proof.
  intros I O joinO. induction ts as [| [i b] ts IH];
    intros [| [i' c] us] a d K Hin; simpl in *; try discriminate;
    [destruct Hin |].
  injection K as <- K. destruct Hin as [E | Hin].
  - injection E as <- <-. exists b, c. repeat split; auto.
  - destruct (IH us a d K Hin) as (b' & c' & Hb & Hc & ->).
    exists b', c'. repeat split; auto.
Qed.

Lemma enum_arrow_inv : forall A1 A2 (F : aval (A1 ⇒ A2)),
  In F (enum (A1 ⇒ A2)) ->
  exists (tbl : list (aval A1 * aval A2)), F = AF tbl
    /\ map fst tbl = enum A1
    /\ (forall a b, In (a, b) tbl -> In b (enum A2))
    /\ monotone_tbl tbl = true.
Proof.
  intros A1 A2 F Hin. simpl in Hin.
  apply in_map_iff in Hin as (tbl & <- & Hin).
  apply filter_In in Hin as [Hin Hmono].
  exists tbl. repeat split; eauto using all_tables_keys, all_tables_outs.
Qed.

Lemma enum_nat_inv : forall (v : aval ℕ),
  In v (enum ℕ) -> v = AN false \/ v = AN true.
Proof. intros v [<- | [<- | []]]; auto. Qed.

Lemma aleb_antisym_enum : forall A (u v : aval A),
  In u (enum A) -> In v (enum A) ->
  aleb u v = true -> aleb v u = true -> u = v.
Proof.
  induction A as [| A1 _ A2 IH2]; intros u v Hu Hv E1 E2.
  - destruct (enum_nat_inv _ Hu) as [-> | ->];
      destruct (enum_nat_inv _ Hv) as [-> | ->].
    + reflexivity.
    + change (false = true) in E2. discriminate.
    + change (false = true) in E1. discriminate.
    + reflexivity.
  - destruct (enum_arrow_inv _ _ _ Hu) as (ts & -> & Ku & Ou & _).
    destruct (enum_arrow_inv _ _ _ Hv) as (us & -> & Kv & Ov & _).
    f_equal.
    assert (K : map fst ts = map fst us) by congruence.
    clear Hu Hv Ku Kv.
    revert us K Ov E1 E2.
    induction ts as [| [a b] ts' IHt];
      intros [| [a' b'] us] K Ov E1 E2; simp aleb in *;
      try discriminate; [reflexivity |].
    injection K as <- K.
    apply andb_prop in E1 as [E1h E1t]. apply andb_prop in E2 as [E2h E2t].
    assert (Hb : In b (enum A2)) by (eapply Ou; left; reflexivity).
    assert (Hb' : In b' (enum A2)) by (eapply Ov; left; reflexivity).
    rewrite (IH2 b b' Hb Hb' E1h E2h).
    f_equal. apply IHt; eauto using in_cons.
Qed.

(** The abstract domain at each PCF type, viewed through the generic finite
    order interface. The rest of this file proves that its concrete table
    operations inhabit the corresponding join and iteration structures. *)
Definition aval_finite_poset (A : ty) : finite_poset (aval A).
Proof.
  refine {| finite_carrier := enum A;
            finite_eqb := aval_eqb;
            finite_leb := aleb |}.
  - apply aval_eqb_refl.
  - intros. eapply aval_eqb_eq; eauto.
  - apply aleb_refl.
  - intros. eapply aleb_trans; eauto.
  - intros. eapply aleb_antisym_enum; eauto.
Defined.

Definition aval_poset (A : ty) : carrier_poset (aval A) :=
  finite_carrier_poset (aval_finite_poset A).

(** ** Application on the carrier: total, closed, monotone *)

Lemma find_key : forall A B (tbl : list (aval A * aval B)) (v : aval A),
  In v (map fst tbl) ->
  exists o, find (fun p : aval A * aval B => aval_eqb (fst p) v) tbl
            = Some (v, o)
            /\ In (v, o) tbl.
Proof.
  intros A B. induction tbl as [| [a b] tbl' IH]; intros v Hin;
    [destruct Hin |].
  simpl in *. destruct (aval_eqb a v) eqn:E.
  - apply aval_eqb_eq in E as <-. eauto.
  - destruct Hin as [<- | Hin].
    + rewrite aval_eqb_refl in E. discriminate.
    + destruct (IH _ Hin) as (o & Hf & Ho). eauto.
Qed.

Lemma aapply_row : forall A B (tbl : list (aval A * aval B)) (v : aval A),
  In v (map fst tbl) -> In (v, aapply (AF tbl) v) tbl.
Proof.
  intros A B tbl v Hin.
  destruct (find_key A B tbl v Hin) as (o & Hf & Ho).
  simp aapply. rewrite Hf. exact Ho.
Qed.

Lemma aapply_enum : forall A B (F : aval (A ⇒ B)) (v : aval A),
  In F (enum (A ⇒ B)) -> In v (enum A) -> In (aapply F v) (enum B).
Proof.
  intros A B F v HF Hv.
  destruct (enum_arrow_inv _ _ _ HF) as (tbl & -> & K & O & _).
  eapply O, aapply_row. rewrite K. exact Hv.
Qed.

Lemma aapply_mono : forall A B (F : aval (A ⇒ B)) (u v : aval A),
  In F (enum (A ⇒ B)) -> In u (enum A) -> In v (enum A) ->
  aleb u v = true ->
  aleb (aapply F u) (aapply F v) = true.
Proof.
  intros A B F u v HF Hu Hv Huv.
  destruct (enum_arrow_inv _ _ _ HF) as (tbl & -> & K & _ & M).
  assert (Ru : In (u, aapply (AF tbl) u) tbl)
    by (apply aapply_row; rewrite K; exact Hu).
  assert (Rv : In (v, aapply (AF tbl) v) tbl)
    by (apply aapply_row; rewrite K; exact Hv).
  unfold monotone_tbl in M.
  rewrite forallb_forall in M.
  specialize (M _ Ru). rewrite forallb_forall in M.
  specialize (M _ Rv). simpl in M. rewrite Huv in M. exact M.
Qed.

(** Application is also monotone in the function table itself. *)
Lemma aapply_fun_mono : forall A B (F G : aval (A ⇒ B)) (v : aval A),
  In F (enum (A ⇒ B)) -> In G (enum (A ⇒ B)) ->
  In v (enum A) -> aleb F G = true ->
  aleb (aapply F v) (aapply G v) = true.
Proof.
  intros A B F G v HF HG Hv EFG.
  destruct (enum_arrow_inv _ _ _ HF) as (ts & -> & Kt & _ & _).
  destruct (enum_arrow_inv _ _ _ HG) as (us & -> & Ku & _ & _).
  assert (K : map fst ts = map fst us) by congruence.
  rewrite <- Kt in Hv. simp aleb in EFG. clear HF HG Kt Ku.
  revert us v Hv K EFG. induction ts as [| [a b] ts IH];
    intros [| [a' b'] us] v Hv K EFG; simpl in *; try discriminate.
  - destruct Hv.
  - injection K as <- K. apply andb_prop in EFG as [Ehead Etail].
    simp aapply. destruct (aval_eqb a v) eqn:Eav.
    + cbn [find]. simpl. rewrite Eav. exact Ehead.
    + cbn [find]. simpl. rewrite Eav.
      change (aleb (aapply (AF ts) v) (aapply (AF us) v) = true).
      apply IH with (us := us); try assumption.
      destruct Hv as [<- | Hv].
      * rewrite aval_eqb_refl in Eav. discriminate.
      * exact Hv.
Qed.

(** ** ⊥ is in the carrier and below it *)

Lemma const_in_all_tables : forall (I O : Type) (ins : list I)
  (outs : list O) (o : O),
  In o outs -> In (map (fun i => (i, o)) ins) (all_tables ins outs).
Proof.
  intros I O. induction ins as [| i ins' IH]; intros outs o Ho; simpl; [auto |].
  apply in_flat_map. exists o. split; [exact Ho |].
  apply in_map_iff. eauto.
Qed.

Lemma abot_enum : forall A, In (abot A) (enum A).
Proof.
  induction A as [| A1 _ A2 IH2]; simpl; [auto |].
  apply in_map_iff. exists (map (fun i => (i, abot A2)) (enum A1)).
  split; [reflexivity |].
  apply filter_In. split; [apply const_in_all_tables, IH2 |].
  unfold monotone_tbl. rewrite forallb_forall. intros [a b] Hab.
  rewrite forallb_forall. intros [a' b'] Hab'.
  apply in_map_iff in Hab as (i & E & _). injection E as <- <-.
  apply in_map_iff in Hab' as (i' & E' & _). injection E' as <- <-.
  simpl. destruct (aleb i i'); [apply aleb_refl | reflexivity].
Qed.

Lemma abot_least : forall A (v : aval A),
  In v (enum A) -> aleb (abot A) v = true.
Proof.
  induction A as [| A1 _ A2 IH2]; intros v Hv.
  - destruct (enum_nat_inv _ Hv) as [-> | ->]; reflexivity.
  - destruct (enum_arrow_inv _ _ _ Hv) as (tbl & -> & K & O & _).
    cbn [abot]. simp aleb. rewrite <- K. clear Hv K.
    induction tbl as [| [a b] tbl' IHt]; [reflexivity |].
    simpl. rewrite IH2; [| eapply O; left; reflexivity]. simpl.
    apply IHt. intros a' b' Hin. eapply O. right. exact Hin.
Qed.

(** ** Join on the carrier

    [ajoin] is pointwise join on canonical tables. The carrier hypotheses are
    essential: outside [enum], tables need not have aligned rows. *)

Lemma ajoin_left : forall A (u v : aval A),
  In u (enum A) -> In v (enum A) -> aleb u (ajoin u v) = true.
Proof.
  induction A as [| A1 _ A2 IH2]; intros u v Hu Hv.
  - destruct (enum_nat_inv _ Hu) as [-> | ->];
      destruct (enum_nat_inv _ Hv) as [-> | ->]; reflexivity.
  - destruct (enum_arrow_inv _ _ _ Hu) as (ts & -> & Kt & Ot & _).
    destruct (enum_arrow_inv _ _ _ Hv) as (us & -> & Ku & Ou & _).
    simp ajoin aleb. assert (K : map fst ts = map fst us) by congruence.
    clear Hu Hv Kt Ku.
    revert us K Ou. induction ts as [| [a b] ts IH];
      intros [| [a' b'] us] K Ou; simpl in *; try discriminate;
      [reflexivity |].
    injection K as <- K. apply andb_true_intro. split.
    + apply IH2; [eapply Ot; left; reflexivity | eapply Ou; left; reflexivity].
    + apply IH.
      * intros a' b'' Hin. eapply Ot. right. exact Hin.
      * exact K.
      * intros a' b'' Hin. eapply Ou. right. exact Hin.
Qed.

Lemma ajoin_right : forall A (u v : aval A),
  In u (enum A) -> In v (enum A) -> aleb v (ajoin u v) = true.
Proof.
  induction A as [| A1 _ A2 IH2]; intros u v Hu Hv.
  - destruct (enum_nat_inv _ Hu) as [-> | ->];
      destruct (enum_nat_inv _ Hv) as [-> | ->]; reflexivity.
  - destruct (enum_arrow_inv _ _ _ Hu) as (ts & -> & Kt & Ot & _).
    destruct (enum_arrow_inv _ _ _ Hv) as (us & -> & Ku & Ou & _).
    simp ajoin aleb. assert (K : map fst ts = map fst us) by congruence.
    clear Hu Hv Kt Ku.
    revert us K Ou. induction ts as [| [a b] ts IH];
      intros [| [a' b'] us] K Ou; simpl in *; try discriminate;
      [reflexivity |].
    injection K as <- K. apply andb_true_intro. split.
    + apply IH2; [eapply Ot; left; reflexivity | eapply Ou; left; reflexivity].
    + apply IH.
      * intros a' b'' Hin. eapply Ot. right. exact Hin.
      * exact K.
      * intros a' b'' Hin. eapply Ou. right. exact Hin.
Qed.

Lemma ajoin_least : forall A (u v w : aval A),
  In u (enum A) -> In v (enum A) -> In w (enum A) ->
  aleb u w = true -> aleb v w = true -> aleb (ajoin u v) w = true.
Proof.
  induction A as [| A1 _ A2 IH2]; intros u v w Hu Hv Hw Euw Evw.
  - dependent elimination u. dependent elimination v. dependent elimination w.
    simp ajoin aleb in *. destruct b, b0, b1; simpl in *; congruence.
  - destruct (enum_arrow_inv _ _ _ Hu) as (ts & -> & Kt & Ot & _).
    destruct (enum_arrow_inv _ _ _ Hv) as (us & -> & Ku & Ou & _).
    destruct (enum_arrow_inv _ _ _ Hw) as (ws & -> & Kw & Ow & _).
    simp ajoin aleb in *. assert (Ktu : map fst ts = map fst us) by congruence.
    assert (Ktw : map fst ts = map fst ws) by congruence.
    clear Hu Hv Hw Kt Ku Kw.
    revert us ws Ktu Ktw Ou Ow Euw Evw.
    induction ts as [| [a b] ts IH];
      intros [| [a' b'] us] [| [a'' c] ws] Ktu Ktw Ou Ow Euw Evw;
      simpl in *; try discriminate; [reflexivity |].
    injection Ktu as <- Ktu. injection Ktw as <- Ktw.
    apply andb_prop in Euw as [Euw Euwt].
    apply andb_prop in Evw as [Evw Evwt].
    apply andb_true_intro. split.
    + apply IH2 with (w := c); try assumption.
      * eapply Ot; left; reflexivity.
      * eapply Ou; left; reflexivity.
      * eapply Ow; left; reflexivity.
    + apply IH.
      * intros a' d Hin. eapply Ot. right. exact Hin.
      * exact Ktu.
      * exact Ktw.
      * intros a' d Hin. eapply Ou. right. exact Hin.
      * intros a' d Hin. eapply Ow. right. exact Hin.
      * exact Euwt.
      * exact Evwt.
Qed.

(** The representation-specific simultaneous argument used to establish
    closure at arrow types. Once closure is known, the public monotonicity
    theorem below is an instance of generic join theory. *)
Local Lemma ajoin_mono_rows : forall A (u1 u2 v1 v2 : aval A),
  In u1 (enum A) -> In u2 (enum A) ->
  In v1 (enum A) -> In v2 (enum A) ->
  aleb u1 u2 = true -> aleb v1 v2 = true ->
  aleb (ajoin u1 v1) (ajoin u2 v2) = true.
Proof.
  induction A as [| A1 _ A2 IH2];
    intros u1 u2 v1 v2 Hu1 Hu2 Hv1 Hv2 Eu Ev.
  - dependent elimination u1. dependent elimination u2.
    dependent elimination v1. dependent elimination v2.
    simp ajoin aleb in *. destruct b, b0, b1, b2; simpl in *; congruence.
  - destruct (enum_arrow_inv _ _ _ Hu1) as (ts1 & -> & Kt1 & Ot1 & _).
    destruct (enum_arrow_inv _ _ _ Hu2) as (ts2 & -> & Kt2 & Ot2 & _).
    destruct (enum_arrow_inv _ _ _ Hv1) as (us1 & -> & Ku1 & Ou1 & _).
    destruct (enum_arrow_inv _ _ _ Hv2) as (us2 & -> & Ku2 & Ou2 & _).
    simp ajoin aleb in *.
    assert (K1 : map fst ts1 = map fst us1) by congruence.
    assert (K2 : map fst ts2 = map fst us2) by congruence.
    assert (K12 : map fst ts1 = map fst ts2) by congruence.
    clear Hu1 Hu2 Hv1 Hv2 Kt1 Kt2 Ku1 Ku2.
    revert ts2 us1 us2 K1 K2 K12 Ot2 Ou1 Ou2 Eu Ev.
    induction ts1 as [| [a b1] ts1 IH];
      intros [| [a2 b2] ts2] [| [a1 c1] us1] [| [a3 c2] us2]
        K1 K2 K12 Ot2 Ou1 Ou2 Eu Ev;
      simpl in *; try discriminate; [reflexivity |].
    injection K1 as <- K1. injection K2 as <- K2. injection K12 as <- K12.
    apply andb_prop in Eu as [Eu Eut]. apply andb_prop in Ev as [Ev Evt].
    apply andb_true_intro. split.
    + apply IH2; try assumption.
      * eapply Ot1; left; reflexivity.
      * eapply Ot2; left; reflexivity.
      * eapply Ou1; left; reflexivity.
      * eapply Ou2; left; reflexivity.
    + apply IH.
      * intros a' d Hin. eapply Ot1. right. exact Hin.
      * exact K1.
      * exact K2.
      * exact K12.
      * intros a' d Hin. eapply Ot2. right. exact Hin.
      * intros a' d Hin. eapply Ou1. right. exact Hin.
      * intros a' d Hin. eapply Ou2. right. exact Hin.
      * exact Eut.
      * exact Evt.
Qed.

Lemma ajoin_enum : forall A (u v : aval A),
  In u (enum A) -> In v (enum A) -> In (ajoin u v) (enum A).
Proof.
  induction A as [| A1 _ A2 IH2]; intros u v Hu Hv.
  - destruct (enum_nat_inv _ Hu) as [-> | ->];
      destruct (enum_nat_inv _ Hv) as [-> | ->]; simpl; auto.
  - destruct (enum_arrow_inv _ _ _ Hu) as (ts & -> & Kt & Ot & Mt).
    destruct (enum_arrow_inv _ _ _ Hv) as (us & -> & Ku & Ou & Mu).
    assert (K : map fst ts = map fst us) by congruence.
    simp ajoin. apply in_map_iff. exists (join_tables (@ajoin A2) ts us).
    split; [reflexivity |]. apply filter_In. split.
    + apply all_tables_complete.
      * rewrite join_tables_keys; [exact Kt | exact K].
      * intros a d Hin.
        destruct (join_tables_row _ _ _ ts us a d K Hin)
          as (b & c & Hb & Hc & ->).
        apply IH2; eauto.
    + unfold monotone_tbl. rewrite forallb_forall. intros [a d] Hd.
      rewrite forallb_forall. intros [a' d'] Hd'.
      destruct (join_tables_row _ _ _ ts us a d K Hd)
        as (b & c & Hb & Hc & ->).
      destruct (join_tables_row _ _ _ ts us a' d' K Hd')
        as (b' & c' & Hb' & Hc' & ->).
      simpl. destruct (aleb a a') eqn:Eaa; [| reflexivity].
      apply (ajoin_mono_rows A2 b b' c c'); try eauto.
      * unfold monotone_tbl in Mt. rewrite forallb_forall in Mt.
        specialize (Mt _ Hb). rewrite forallb_forall in Mt.
        specialize (Mt _ Hb'). simpl in Mt. rewrite Eaa in Mt. exact Mt.
      * unfold monotone_tbl in Mu. rewrite forallb_forall in Mu.
        specialize (Mu _ Hc). rewrite forallb_forall in Mu.
        specialize (Mu _ Hc'). simpl in Mu. rewrite Eaa in Mu. exact Mu.
Qed.

(** Having discharged the table representation obligations, package [ajoin]
    once. All laws below are specializations of FiniteOrder.v. *)
Definition aval_join_semilat (A : ty) : join_semilat (aval A).
Proof.
  refine {| join_base := aval_poset A; join_op := ajoin |}; cbn.
  - apply ajoin_enum.
  - apply ajoin_left.
  - apply ajoin_right.
  - apply ajoin_least.
Defined.

Definition aval_bounded_join_semilat (A : ty) : bounded_join_semilat (aval A).
Proof.
  refine {| bounded_join_base := aval_join_semilat A;
            order_bottom := abot A |}; cbn.
  - apply abot_enum.
  - apply abot_least.
Defined.

Lemma ajoin_mono : forall A (u1 u2 v1 v2 : aval A),
  In u1 (enum A) -> In u2 (enum A) ->
  In v1 (enum A) -> In v2 (enum A) ->
  aleb u1 u2 = true -> aleb v1 v2 = true ->
  aleb (ajoin u1 v1) (ajoin u2 v2) = true.
Proof.
  intros A u1 u2 v1 v2 Hu1 Hu2 Hv1 Hv2 Eu Ev.
  exact (join_mono _ (aval_join_semilat A) _ _ _ _
    Hu1 Hu2 Hv1 Hv2 Eu Ev).
Qed.

(** These equations are carrier-scoped: arbitrary raw function tables need
    not have aligned keys. *)
Lemma ajoin_le_iff : forall A (u v w : aval A),
  In u (enum A) -> In v (enum A) -> In w (enum A) ->
  aleb (ajoin u v) w = true <->
    aleb u w = true /\ aleb v w = true.
Proof.
  intros A u v w Hu Hv Hw.
  exact (join_le_iff _ (aval_join_semilat A) _ _ _ Hu Hv Hw).
Qed.

Lemma ajoin_idem : forall A (u : aval A),
  In u (enum A) -> ajoin u u = u.
Proof.
  intros A u Hu. exact (join_idem _ (aval_join_semilat A) _ Hu).
Qed.

Lemma ajoin_comm : forall A (u v : aval A),
  In u (enum A) -> In v (enum A) -> ajoin u v = ajoin v u.
Proof.
  intros A u v Hu Hv. exact (join_comm _ (aval_join_semilat A) _ _ Hu Hv).
Qed.

Lemma ajoin_assoc : forall A (u v w : aval A),
  In u (enum A) -> In v (enum A) -> In w (enum A) ->
  ajoin (ajoin u v) w = ajoin u (ajoin v w).
Proof.
  intros A u v w Hu Hv Hw.
  exact (join_assoc _ (aval_join_semilat A) _ _ _ Hu Hv Hw).
Qed.

Lemma ajoin_bot_l : forall A (u : aval A),
  In u (enum A) -> ajoin (abot A) u = u.
Proof.
  intros A u Hu.
  exact (join_bottom_l _ (aval_bounded_join_semilat A) _ Hu).
Qed.

Lemma ajoin_bot_r : forall A (u : aval A),
  In u (enum A) -> ajoin u (abot A) = u.
Proof.
  intros A u Hu.
  exact (join_bottom_r _ (aval_bounded_join_semilat A) _ Hu).
Qed.

(** ** The carrier is no bigger than the budget *)

Lemma flat_map_const_length : forall (X Y : Type) (f : X -> list Y) l n,
  (forall x, In x l -> length (f x) = n) ->
  length (flat_map f l) = length l * n.
Proof.
  induction l as [| h t IH]; intros n Hn; simpl; [reflexivity |].
  rewrite length_app, (Hn h (or_introl eq_refl)), (IH n); auto.
  intros x Hx. apply Hn. right. exact Hx.
Qed.

Lemma all_tables_length : forall (I O : Type) (ins : list I) (outs : list O),
  length (all_tables ins outs) = length outs ^ length ins.
Proof.
  intros I O. induction ins as [| i ins' IH]; intros outs; simpl; [reflexivity |].
  rewrite (flat_map_const_length _ _ _ _ (length (all_tables ins' outs)));
    [| intros; apply length_map].
  rewrite IH. reflexivity.
Qed.

Lemma enum_nonempty : forall A, enum A <> [].
Proof.
  intros A E. pose proof (abot_enum A) as H. rewrite E in H. exact H.
Qed.

Lemma enum_le_dsize : forall A, length (enum A) <= dsize A.
Proof.
  induction A as [| A1 IH1 A2 IH2]; simpl; [lia |].
  rewrite length_map.
  eapply Nat.le_trans; [apply filter_length_le |].
  rewrite all_tables_length.
  apply Nat.pow_le_mono; [| exact IH2 | exact IH1].
  pose proof (enum_nonempty A2).
  destruct (enum A2); [congruence | simpl; lia].
Qed.

(** ** The measure: how much room is left above [a] *)

Definition upsize (A : ty) (a : aval A) : nat :=
  upper_size (aval_finite_poset A) a.

Lemma upsize_le : forall A (a : aval A), upsize A a <= dsize A.
Proof.
  intros. eapply Nat.le_trans; [apply upper_size_le | apply enum_le_dsize].
Qed.

Lemma upsize_pos : forall A (a : aval A),
  In a (enum A) -> 1 <= upsize A a.
Proof.
  intros A a Ha. exact (upper_size_pos _ (aval_finite_poset A) _ Ha).
Qed.

(** A strict rise strictly shrinks the room above. *)
Lemma upsize_strict : forall A (a b : aval A),
  In a (enum A) -> In b (enum A) ->
  aleb a b = true -> a <> b ->
  upsize A b < upsize A a.
Proof.
  intros A a b Ha Hb Hab Hne.
  exact (upper_size_strict _ (aval_finite_poset A) _ _ Ha Hb Hab Hne).
Qed.

(** ** Stabilization *)

(** The engine: from any point of the carrier sitting below its own image,
    with [n] at least the room above it, [n] more steps reach a fixpoint.
    A step either already fixes the point or strictly shrinks the room. *)
Lemma chain_stab : forall n A (F : aval (A ⇒ A)) (a : aval A),
  In F (enum (A ⇒ A)) -> In a (enum A) ->
  aleb a (aapply F a) = true ->
  upsize A a <= n ->
  Nat.iter (S n) (aapply F) a = Nat.iter n (aapply F) a.
Proof.
  intros n A F a HF Ha Hrise Hup.
  apply (finite_chain_stab _ (aval_finite_poset A) n (aapply F) a).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - exact Ha.
  - exact Hrise.
  - exact Hup.
Qed.

(** *** The receipt

    For every functional in the carrier, [dsize A] iterations produce a
    genuine fixpoint. The hypothesis is exactly what [Tests.not_table]
    lacks — on that non-monotone table the iteration provably oscillates —
    so the theorem is sharp. *)

Theorem afix_receipt : forall A (F : aval (A ⇒ A)),
  In F (enum (A ⇒ A)) ->
  aapply F (afix_approx A F (dsize A)) = afix_approx A F (dsize A).
Proof.
  intros A F HF.
  unfold afix_approx.
  apply (finite_iter_receipt _ (aval_finite_poset A)
    (aapply F) (abot A) (dsize A)).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - apply abot_enum.
  - apply abot_least.
  - apply enum_le_dsize.
Qed.

(** Once fixed, forever fixed: any budget beyond [dsize A] returns the
    same answer. *)
Corollary afix_stable : forall A (F : aval (A ⇒ A)) k,
  In F (enum (A ⇒ A)) -> dsize A <= k ->
  afix_approx A F k = afix_approx A F (dsize A).
Proof.
  intros A F k HF Hk. induction k as [| k IH].
  - assert (dsize A = 0) by lia. congruence.
  - destruct (Nat.eq_dec (dsize A) (S k)) as [-> | Hne]; [reflexivity |].
    simpl. rewrite IH; [| lia]. apply afix_receipt, HF.
Qed.

(** The iterates never leave the carrier... *)
Lemma afix_approx_enum : forall A (F : aval (A ⇒ A)) k,
  In F (enum (A ⇒ A)) -> In (afix_approx A F k) (enum A).
Proof.
  intros A F k HF. unfold afix_approx.
  apply (iter_closed _ (aval_finite_poset A) (aapply F) (abot A) k).
  - intros x Hx. apply aapply_enum; assumption.
  - apply abot_enum.
Qed.

(** Pointwise larger functionals have pointwise larger approximants. *)
Lemma afix_approx_mono : forall A (F G : aval (A ⇒ A)),
  In F (enum (A ⇒ A)) -> In G (enum (A ⇒ A)) ->
  aleb F G = true -> forall k,
  aleb (afix_approx A F k) (afix_approx A G k) = true.
Proof.
  intros A F G HF HG HFG k. unfold afix_approx.
  apply (finite_iter_mono _ (aval_finite_poset A)
    (aapply F) (aapply G) (abot A) k).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - intros x Hx. apply aapply_fun_mono; assumption.
  - apply abot_enum.
Qed.

(** *** ...and the answer is the least fixpoint

    Not just *a* fixpoint: anything in the carrier that [F] fixes sits
    above the analysis' answer. The abstract [fix] really is lfp — the
    computable finite shadow of ⊔ fⁿ(⊥), now as a theorem. *)

Theorem afix_least : forall A (F : aval (A ⇒ A)) (b : aval A),
  In F (enum (A ⇒ A)) -> In b (enum A) ->
  aapply F b = b ->
  aleb (afix_approx A F (dsize A)) b = true.
Proof.
  intros A F b HF Hb Hfix. unfold afix_approx.
  apply (finite_iter_least _ (aval_finite_poset A)
    (aapply F) (abot A) (dsize A) b).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - apply abot_enum.
  - apply abot_least.
  - exact Hb.
  - exact Hfix.
Qed.

(** ** The canonical, proof-facing domain

    The index of [aval A] rules out values of the wrong PCF type; membership
    in [enum A] additionally records the semantic carrier invariant: canonical
    keys, carrier-valued rows, and monotonicity. Proofs live in [Prop], so this
    wrapper erases to the underlying [aval] if it is ever extracted. *)

Record cval (A : ty) : Type := {
  cval_raw : aval A;
  cval_in_enum : In cval_raw (enum A)
}.

Arguments cval_raw {A} _.
Arguments cval_in_enum {A} _.

Definition cbot (A : ty) : cval A.
Proof.
  refine {| cval_raw := abot A; cval_in_enum := abot_enum A |}.
Defined.

Definition capply {A B} (f : cval (A ⇒ B)) (v : cval A) : cval B.
Proof.
  refine {| cval_raw := aapply (cval_raw f) (cval_raw v) |}.
  apply aapply_enum; apply cval_in_enum.
Defined.

Definition cjoin {A} (u v : cval A) : cval A.
Proof.
  refine {| cval_raw := ajoin (cval_raw u) (cval_raw v) |}.
  apply ajoin_enum; apply cval_in_enum.
Defined.

Definition cfix {A} (F : cval (A ⇒ A)) : cval A.
Proof.
  refine {| cval_raw := afix_approx A (cval_raw F) (dsize A) |}.
  apply afix_approx_enum, cval_in_enum.
Defined.

Definition cle {A} (u v : cval A) : Prop :=
  aleb (cval_raw u) (cval_raw v) = true.
