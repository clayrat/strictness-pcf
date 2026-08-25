(** * A step-indexed logical relation for abstract definedness

    This file provides the operational interface needed by a soundness proof
    for the strictness analyser.  It relates a finite abstract value [a : aval
    A] to a concrete PCF term [t] for a bounded number of observations.

    The relation is deliberately cumulative.  Index zero observes nothing.
    At index [S k] it retains the relation at [k] and adds one obligation:

    - [AN false] must take another step and remain related to bottom;
    - [AN true] must be a numeral or take another related step;
    - [AF tbl] must be a lambda whose body maps related closed arguments to
      the corresponding table result, or take another related step.

    The function clause is call-by-name: its concrete argument is substituted
    unevaluated. Requiring the argument to be closed is the exact condition
    under which Subst.v's non-renaming substitution is sound.

    Cumulativity makes downward closure immediate and keeps every recursive
    occurrence structurally below [S k].  It also gives the intended
    interpretation of natural bottom:

        (forall k, term_rel k (AN false) t)  <->  diverges t.

    AnalysisSoundness.v combines this interface with the analyser's carrier
    and monotonicity properties. Its fundamental theorem relates checked terms
    to their [aeval] results and derives [certified_strict_sound] for the public
    Boolean API. *)

From Stdlib Require Import String List Arith.
From Equations Require Import Equations.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing Subst OperationalSemantics
                        Strictness Stabilization.

Open Scope string_scope.
Open Scope ty_scope.
Open Scope pcf_scope.

(** ** The relation *)

Fixpoint term_rel (k : nat) {A : ty} (a : aval A) (t : term) : Prop :=
  match k with
  | 0 => True
  | S k' =>
      term_rel k' a t /\
      match a with
      | AN false =>
          exists u, t --> u /\ term_rel k' (AN false) u
      | AN true =>
          (exists n, t = # n)
          \/ (exists u, t --> u /\ term_rel k' (AN true) u)
      | @AF A1 A2 tbl =>
          (exists x body,
              t = (λ x, body)
              /\ forall (d : aval A1) u,
                   In d (enum A1) ->
                   closed u ->
                   term_rel k' d u ->
                   term_rel k' (aapply (AF tbl) d) (<[ x := u ]> body))
          \/ (exists u, t --> u /\ term_rel k' (AF tbl) u)
      end
  end.

Definition semantic_rel {A : ty} (a : aval A) (t : term) : Prop :=
  forall k, term_rel k a t.

(** The value shapes admitted by a successful observation at a type.  This is
    intentionally operational and does not duplicate the typing judgment. *)
Inductive value_at : ty -> term -> Prop :=
| VA_Num : forall n, value_at ℕ (# n)
| VA_Lam : forall A B x body, value_at (A ⇒ B) (λ x, body).

#[export] Hint Constructors value_at : pcf.

(** ** Cumulativity and operational closure *)

Lemma term_rel_zero : forall A (a : aval A) t, term_rel 0 a t.
Proof. reflexivity. Qed.

Lemma term_rel_down1 : forall k A (a : aval A) t,
  term_rel (S k) a t -> term_rel k a t.
Proof. intros k A a t H. exact (proj1 H). Qed.

Lemma term_rel_down : forall k j A (a : aval A) t,
  j <= k -> term_rel k a t -> term_rel j a t.
Proof.
  intros k j A a t Hle. induction Hle; intros H; [exact H |].
  apply IHHle, term_rel_down1, H.
Qed.

(** Expansion along a concrete step does not consume logical precision. *)
Lemma term_rel_step_back : forall k A (a : aval A) t u,
  t --> u -> term_rel k a u -> term_rel k a t.
Proof.
  induction k as [| k IH]; intros A a t u Hstep Hu; [exact I |].
  split.
  - apply IH with (u := u); [exact Hstep | apply term_rel_down1, Hu].
  - destruct a as [b | A1 A2 tbl].
    + destruct b.
      * right. exists u. split; [exact Hstep | apply term_rel_down1, Hu].
      * exists u. split; [exact Hstep | apply term_rel_down1, Hu].
    + right. exists u. split; [exact Hstep | apply term_rel_down1, Hu].
Qed.

(** Conversely, one step can be exposed by spending one index. *)
Lemma term_rel_step_later : forall k A (a : aval A) t u,
  t --> u -> term_rel k a u -> term_rel (S k) a t.
Proof.
  intros k A a t u Hstep Hu. split.
  - eapply term_rel_step_back; eassumption.
  - destruct a as [b | A1 A2 tbl].
    + destruct b.
      * right. eauto.
      * eauto.
    + right. eauto.
Qed.

(** A related term that actually steps exposes a related successor one index
    down.  Determinism identifies the step required by the relation with the
    supplied operational step. *)
Lemma term_rel_step_forward : forall k A (a : aval A) t u,
  term_rel (S k) a t -> t --> u -> term_rel k a u.
Proof.
  intros k A a t u Hrel Hstep. destruct Hrel as [_ Hnow].
  destruct a as [b | A1 A2 tbl].
  - destruct b.
    + destruct Hnow as [(n & ->) | (u' & Hstep' & Hu')].
      * exfalso. eapply value_no_step; [constructor | exact Hstep].
      * rewrite (cbn_deterministic _ _ _ Hstep' Hstep) in Hu'. exact Hu'.
    + destruct Hnow as (u' & Hstep' & Hu').
      rewrite (cbn_deterministic _ _ _ Hstep' Hstep) in Hu'. exact Hu'.
  - destruct Hnow as [(x & body & -> & _) | (u' & Hstep' & Hu')].
    + exfalso. eapply value_no_step; [constructor | exact Hstep].
    + rewrite (cbn_deterministic _ _ _ Hstep' Hstep) in Hu'. exact Hu'.
Qed.

(** ** What a finite observation guarantees *)

Theorem term_rel_eval : forall k A (a : aval A) t,
  term_rel k a t ->
  evalFuel k t = Timeout
  \/ exists v, evalFuel k t = Value v /\ value_at A v.
Proof.
  induction k as [| k IH]; intros A a t Hrel; [left; reflexivity |].
  destruct Hrel as [_ Hnow]. destruct a as [b | A1 A2 tbl].
  - destruct b.
    + destruct Hnow as [(n & ->) | (u & Hstep & Hu)].
      * right. exists (# n). split; [reflexivity | constructor].
      * rewrite (evalFuel_step k _ _ Hstep). exact (IH _ _ _ Hu).
    + destruct Hnow as (u & Hstep & Hu).
      rewrite (evalFuel_step k _ _ Hstep). exact (IH _ _ _ Hu).
  - destruct Hnow as [(x & body & -> & _) | (u & Hstep & Hu)].
    + right. exists (λ x, body). split; [reflexivity | constructor].
    + rewrite (evalFuel_step k _ _ Hstep). exact (IH _ _ _ Hu).
Qed.

Corollary term_rel_no_stuck : forall k A (a : aval A) t s,
  term_rel k a t -> evalFuel k t <> Stuck s.
Proof.
  intros k A a t s Hrel Hstuck.
  destruct (term_rel_eval _ _ _ _ Hrel) as [H | (v & H & _)]; congruence.
Qed.

(** Bottom at natural type admits no value observation. *)
Lemma term_rel_nat_bottom_timeout : forall k t,
  term_rel k (AN false) t -> evalFuel k t = Timeout.
Proof.
  induction k as [| k IH]; intros t Hrel; [reflexivity |].
  destruct Hrel as [_ (u & Hstep & Hu)].
  rewrite (evalFuel_step k _ _ Hstep). apply IH, Hu.
Qed.

(** Divergence is related to every abstract value: a computation that never
    returns cannot contradict any finite definedness approximation. *)
Lemma diverges_term_rel : forall t,
  diverges t -> forall k A (a : aval A), term_rel k a t.
Proof.
  intros t Hdiv k. revert t Hdiv. induction k as [| k IH];
    intros t Hdiv A a; [exact I |].
  destruct (diverges_next _ Hdiv) as (u & Hstep & Hdivu).
  split.
  - apply IH, Hdiv.
  - destruct a as [b | A1 A2 tbl].
    + destruct b.
      * right. exists u. split; [exact Hstep | apply IH, Hdivu].
      * exists u. split; [exact Hstep | apply IH, Hdivu].
    + right. exists u. split; [exact Hstep | apply IH, Hdivu].
Qed.

Theorem semantic_nat_bottom_iff : forall t,
  semantic_rel (AN false) t <-> diverges t.
Proof.
  intros t. split.
  - intros Hrel k. apply term_rel_nat_bottom_timeout, Hrel.
  - intros Hdiv k. apply diverges_term_rel, Hdiv.
Qed.

(** The next few lemmas are the *interface* of the relation — sanity facts
    a reader (or a later development) should be able to invoke, not
    ingredients of the fundamental theorem: semantic relatedness is
    invariant along reduction, λ has its canonical introduction, and a
    related term never gets stuck ([term_rel_no_stuck] above) — the last
    being an independent, typing-free echo of Safety.v. *)
Lemma semantic_rel_step_iff : forall A (a : aval A) t u,
  t --> u -> (semantic_rel a t <-> semantic_rel a u).
Proof.
  intros A a t u Hstep. split.
  - intros Hrel k. apply term_rel_step_forward with (t := t).
    + apply Hrel.
    + exact Hstep.
  - intros Hrel k. eapply term_rel_step_back; [exact Hstep | apply Hrel].
Qed.

Lemma semantic_rel_num : forall n, semantic_rel (AN true) (# n).
Proof.
  intros n k. induction k as [| k IH]; [exact I |].
  split; [exact IH |]. left. eauto.
Qed.

Lemma semantic_rel_lam : forall A B (F : aval (A ⇒ B)) x body,
  (forall k (d : aval A) u,
      In d (enum A) -> closed u -> term_rel k d u ->
      term_rel k (aapply F d) (<[ x := u ]> body)) ->
  semantic_rel F (λ x, body).
Proof.
  intros A B F x body Hbody k. dependent elimination F.
  induction k as [| k IH]; [exact I |]. split; [exact IH |].
  left. exists x, body. split; [reflexivity |]. apply Hbody.
Qed.

(** Strict numeric primitives preserve the definedness abstraction. *)
Lemma term_rel_succ : forall k (a : aval ℕ) t,
  term_rel k a t -> term_rel k a (tsucc t).
Proof.
  induction k as [| k IH]; intros a t Hrel; [exact I |].
  dependent elimination a. destruct Hrel as [Hprev Hnow]. split.
  - apply IH, Hprev.
  - destruct b.
    + destruct Hnow as [(n & ->) | (u & Hstep & Hu)].
      * right. exists (# (S n)). split; [apply S_SuccN | apply semantic_rel_num].
      * right. exists (tsucc u). split; [apply S_Succ1, Hstep | apply IH, Hu].
    + destruct Hnow as (u & Hstep & Hu).
      exists (tsucc u). split; [apply S_Succ1, Hstep | apply IH, Hu].
Qed.

Lemma term_rel_pred : forall k (a : aval ℕ) t,
  term_rel k a t -> term_rel k a (tpred t).
Proof.
  induction k as [| k IH]; intros a t Hrel; [exact I |].
  dependent elimination a. destruct Hrel as [Hprev Hnow]. split.
  - apply IH, Hprev.
  - destruct b.
    + destruct Hnow as [(n & ->) | (u & Hstep & Hu)].
      * right. exists (# (Nat.pred n)). split;
          [apply S_PredN | apply semantic_rel_num].
      * right. exists (tpred u). split; [apply S_Pred1, Hstep | apply IH, Hu].
    + destruct Hnow as (u & Hstep & Hu).
      exists (tpred u). split; [apply S_Pred1, Hstep | apply IH, Hu].
Qed.

(** ** Monotonicity in abstract information *)

Theorem term_rel_mono : forall k A (a b : aval A) t,
  In a (enum A) -> In b (enum A) -> aleb a b = true ->
  term_rel k a t -> term_rel k b t.
Proof.
  induction k as [| k IH]; intros A a b t Ha Hb Hab Hrel; [exact I |].
  split.
  - apply IH with (a := a); try assumption. apply term_rel_down1, Hrel.
  - destruct A as [| A1 A2].
    + dependent elimination a. dependent elimination b.
      destruct b0, b; simpl in Hab; try discriminate.
      * destruct Hrel as [_ Hnow]. exact Hnow.
      * destruct Hrel as [_ (u & Hstep & Hu)].
        right. exists u. split; [exact Hstep |].
        apply IH with (a := AN false); simpl; auto.
      * destruct Hrel as [_ Hnow]. exact Hnow.
    + dependent elimination a. dependent elimination b.
      destruct Hrel as [_ Hnow].
      destruct Hnow as [(x & body & -> & Hbody) | (u & Hstep & Hu)].
      * left. exists x, body. split; [reflexivity |].
        intros d v Hd Hty Hdv.
        apply IH with (a := aapply (AF l) d).
        -- eapply aapply_enum; eassumption.
        -- eapply aapply_enum; eassumption.
        -- eapply aapply_fun_mono; eassumption.
        -- apply Hbody; assumption.
      * right. exists u. split; [exact Hstep |].
        apply IH with (a := AF l); assumption.
Qed.

Corollary semantic_rel_mono : forall A (a b : aval A) t,
  In a (enum A) -> In b (enum A) -> aleb a b = true ->
  semantic_rel a t -> semantic_rel b t.
Proof.
  intros A a b t Ha Hb Hab Hrel k.
  apply term_rel_mono with (a := a); auto.
Qed.

(** The abstract conditional gates on the condition and joins its branches.
    If the condition is bottom, concrete evaluation can only follow it. If it
    is defined, the selected concrete branch lies below the abstract join. *)
Lemma term_rel_ifz : forall k A (c : aval ℕ) (a b : aval A) ct t u,
  In a (enum A) -> In b (enum A) ->
  term_rel k c ct -> term_rel k a t -> term_rel k b u ->
  term_rel k
    (if an_defined c then ajoin a b else abot A)
    (ifz ct then t else u).
Proof.
  induction k as [| k IH]; intros A c a b ct t u Ha Hb Hc Ht Hu;
    [exact I |].
  dependent elimination c. simp an_defined.
  destruct b0.
  - destruct Hc as [_ Hnow].
    destruct Hnow as [(n & ->) | (ct' & Hstep & Hct')].
    + destruct n.
      * eapply term_rel_step_back; [apply S_IfzZ |].
        eapply term_rel_mono with (a := a); eauto using ajoin_enum, ajoin_left.
      * eapply term_rel_step_back; [apply S_IfzS |].
        eapply term_rel_mono with (a := b); eauto using ajoin_enum, ajoin_right.
    + apply term_rel_step_later with (u := ifz ct' then t else u).
      * apply S_Ifz1, Hstep.
      * specialize (IH A (AN true) a b ct' t u Ha Hb Hct'
          (term_rel_down1 _ _ _ _ Ht) (term_rel_down1 _ _ _ _ Hu)).
        simp an_defined in IH.
  - destruct Hc as [_ (ct' & Hstep & Hct')].
    apply term_rel_step_later with (u := ifz ct' then t else u).
    + apply S_Ifz1, Hstep.
    + specialize (IH A (AN false) a b ct' t u Ha Hb Hct'
        (term_rel_down1 _ _ _ _ Ht) (term_rel_down1 _ _ _ _ Hu)).
      simp an_defined in IH.
Qed.

(** ** Call-by-name application *)

Lemma term_rel_app : forall k A B (F : aval (A ⇒ B)) f
    (d : aval A) u,
  In d (enum A) -> closed u ->
  term_rel k F f -> term_rel k d u ->
  term_rel k (aapply F d) (f · u).
Proof.
  induction k as [| k IH]; intros A B F f d u Hd Hclosed Hf Hu; [exact I |].
  destruct Hf as [_ Hnow].
  dependent elimination F.
  destruct Hnow as [(x & body & -> & Hbody) | (f' & Hstep & Hf')].
  - apply term_rel_step_later with (u := <[ x := u ]> body).
    + apply S_Beta.
    + apply Hbody; [exact Hd | exact Hclosed | apply term_rel_down1, Hu].
  - apply term_rel_step_later with (u := f' · u).
    + apply S_App1, Hstep.
    + apply IH; try assumption. apply term_rel_down1, Hu.
Qed.

Theorem semantic_rel_app : forall A B (F : aval (A ⇒ B)) f
    (d : aval A) u,
  In d (enum A) -> closed u ->
  semantic_rel F f -> semantic_rel d u ->
  semantic_rel (aapply F d) (f · u).
Proof.
  intros A B F f d u Hd Hclosed HF Hu k.
  eapply term_rel_app; eauto.
Qed.

Lemma semantic_rel_ann : forall A (a : aval A) t B,
  semantic_rel a t -> semantic_rel a (t ∷ B).
Proof.
  intros A a t B Hrel k. eapply term_rel_step_back; [apply S_Ann | apply Hrel].
Qed.

(** Concrete unfolding meets the abstract fixpoint theorem here. The logical
    index justifies the recursive use, while [afix_approx_is_fixpoint] rewrites
    the table result back to the analyser's chosen least fixpoint. *)
Lemma term_rel_fix : forall k A (F : aval (A ⇒ A)) f,
  In F (enum (A ⇒ A)) -> closed f -> term_rel k F f ->
  term_rel k (afix_approx A F (dsize A)) (tfix A f).
Proof.
  induction k as [| k IH]; intros A F f HF Hclosed Hrel; [exact I |].
  apply term_rel_step_later with (u := f · tfix A f); [apply S_Fix |].
  assert (Hfix_closed : closed (tfix A f)).
  { intros x Hfree. inversion Hfree; subst. eapply Hclosed; eassumption. }
  assert (Hf : term_rel k F f) by (apply term_rel_down1, Hrel).
  assert (Hfix : term_rel k (afix_approx A F (dsize A)) (tfix A f))
    by (apply IH; assumption).
  assert (Happ : term_rel k
      (aapply F (afix_approx A F (dsize A))) (f · tfix A f)).
  { apply term_rel_app; try assumption. apply afix_approx_enum, HF. }
  rewrite (afix_approx_is_fixpoint A F HF) in Happ. exact Happ.
Qed.

Corollary semantic_rel_fix : forall A (F : aval (A ⇒ A)) f,
  In F (enum (A ⇒ A)) -> closed f -> semantic_rel F f ->
  semantic_rel (afix_approx A F (dsize A)) (tfix A f).
Proof.
  intros A F f HF Hclosed Hsem k. apply term_rel_fix; auto.
Qed.

(** This semantic bridge turns a related abstract bottom row into operational
    strictness. AnalysisSoundness.v supplies its [semantic_rel] premise for
    every checked analyser input. *)
Theorem semantic_strict_nat : forall (F : aval (ℕ ⇒ ℕ)) f,
  In F (enum (ℕ ⇒ ℕ)) ->
  semantic_rel F f ->
  aapply F (AN false) = AN false ->
  forall u, [] ⊢ u ∈ ℕ -> diverges u -> diverges (f · u).
Proof.
  intros F f HF Hsem Hbot u Hty Hdiv.
  apply semantic_nat_bottom_iff. rewrite <- Hbot.
  eapply semantic_rel_app with (F := F) (d := AN false).
  - simpl. auto.
  - eauto using typable_empty_closed.
  - exact Hsem.
  - intros k. apply diverges_term_rel, Hdiv.
Qed.

(** ** Related concrete and abstract environments

    These lists deliberately mirror [ctx] and [aenv].  The relation records
    the carrier invariant required by table lookup, the closedness invariant
    required by substitution, and the logical relation itself. *)

Definition cenv : Type := list (string * term).

Fixpoint clookup (γ : cenv) (x : string) : option term :=
  match γ with
  | [] => None
  | (y, u) :: γ' => if String.eqb x y then Some u else clookup γ' x
  end.

(** Remove every binding for a name.  Instantiation uses this operation below
    a lambda, where the binder shadows the concrete environment. *)
Fixpoint cremove (x : string) (γ : cenv) : cenv :=
  match γ with
  | [] => []
  | (y, u) :: γ' =>
      if String.eqb y x then cremove x γ' else (y, u) :: cremove x γ'
  end.

Definition cenv_closed (γ : cenv) : Prop :=
  forall x u, In (x, u) γ -> closed u.

Lemma clookup_cremove_eq : forall γ x,
  clookup (cremove x γ) x = None.
Proof.
  induction γ as [| [y u] γ IH]; intros x; [reflexivity |].
  simpl. destruct (String.eqb_spec y x) as [-> | Hyx].
  - apply IH.
  - simpl. destruct (String.eqb_spec x y); [congruence | apply IH].
Qed.

Lemma clookup_cremove_neq : forall γ x y,
  x <> y -> clookup (cremove x γ) y = clookup γ y.
Proof.
  induction γ as [| [z u] γ IH]; intros x y Hxy; [reflexivity |].
  simpl. destruct (String.eqb_spec z x) as [-> | Hzx].
  - destruct (String.eqb_spec y x); [congruence | apply IH, Hxy].
  - simpl. destruct (String.eqb_spec y z) as [-> | Hyz]; [reflexivity |].
    apply IH, Hxy.
Qed.

Lemma cremove_idem : forall γ x,
  cremove x (cremove x γ) = cremove x γ.
Proof.
  induction γ as [| [y u] γ IH]; intros x; [reflexivity |].
  simpl. destruct (String.eqb y x) eqn:E; simpl; rewrite ?E, IH; reflexivity.
Qed.

Lemma cremove_comm : forall γ x y,
  x <> y -> cremove x (cremove y γ) = cremove y (cremove x γ).
Proof.
  induction γ as [| [z u] γ IH]; intros x y Hxy; [reflexivity |].
  simpl. destruct (String.eqb z y) eqn:Ezy;
    destruct (String.eqb z x) eqn:Ezx; simpl; rewrite ?Ezy, ?Ezx.
  - apply String.eqb_eq in Ezy. apply String.eqb_eq in Ezx. subst. congruence.
  - apply IH, Hxy.
  - apply IH, Hxy.
  - f_equal. apply IH, Hxy.
Qed.

Lemma cenv_closed_remove : forall γ x,
  cenv_closed γ -> cenv_closed (cremove x γ).
Proof.
  induction γ as [| [z v] γ IH]; intros x Hclosed y u Hin;
    simpl in Hin; [contradiction |].
  destruct (String.eqb z x) eqn:E.
  - assert (Htail : cenv_closed γ).
    { intros q w Hqw. apply Hclosed with (x := q). right. exact Hqw. }
    exact (IH x Htail y u Hin).
  - destruct Hin as [Heq | Hin].
    + injection Heq as <- <-. apply Hclosed with (x := z). left. reflexivity.
    + assert (Htail : cenv_closed γ).
      { intros q w Hqw. apply Hclosed with (x := q). right. exact Hqw. }
      exact (IH x Htail y u Hin).
Qed.

Lemma cenv_closed_lookup : forall γ,
  cenv_closed γ -> forall x u, clookup γ x = Some u -> closed u.
Proof.
  induction γ as [| [y v] γ IH]; intros Hclosed x u Hlookup;
    simpl in Hlookup; [discriminate |].
  destruct (String.eqb x y) eqn:E.
  - injection Hlookup as <-. apply Hclosed with (x := y). left. reflexivity.
  - assert (Htail : cenv_closed γ).
    { intros z w Hin. apply Hclosed with (x := z). right. exact Hin. }
    exact (IH Htail x u Hlookup).
Qed.

(** Simultaneous, capture-safe instantiation by *closed* terms.  A missing
    variable is left untouched.  Under a binder its name is removed from the
    environment, so shadowing agrees with [lookup], [alookup], and [subst]. *)
Fixpoint instantiate (γ : cenv) (t : term) : term :=
  match t with
  | tvar x =>
      match clookup γ x with
      | Some u => u
      | None => tvar x
      end
  | λ x, body => λ x, instantiate (cremove x γ) body
  | f · u => instantiate γ f · instantiate γ u
  | # n => # n
  | tsucc u => tsucc (instantiate γ u)
  | tpred u => tpred (instantiate γ u)
  | ifz c then t1 else t2 =>
      ifz instantiate γ c then instantiate γ t1 else instantiate γ t2
  | tfix A u => tfix A (instantiate γ u)
  | u ∷ A => instantiate γ u ∷ A
  end.

Lemma instantiate_nil : forall t, instantiate [] t = t.
Proof.
  induction t as [x | x body IH | f IHf u IHu | n | u IH | u IH
                 | c IHc t1 IH1 t2 IH2 | A u IH | u IH A];
    simpl; rewrite ?IH, ?IHf, ?IHu, ?IHc, ?IH1, ?IH2; reflexivity.
Qed.

(** Extending a closing environment agrees with one ordinary substitution,
    after older bindings for the extended name have been masked.  This is the
    beta/lambda equation used by the fundamental theorem. *)
Lemma instantiate_cons : forall t γ x u,
  cenv_closed γ -> closed u ->
  instantiate ((x, u) :: γ) t =
  <[ x := u ]> instantiate (cremove x γ) t.
Proof.
  induction t as [y | y body IH | f IHf v IHv | n | v IH | v IH
                 | c IHc t1 IH1 t2 IH2 | A v IH | v IH A];
    intros γ x u Hγ Hu; simpl.
  - destruct (String.eqb_spec y x) as [-> | Hyx].
    + rewrite clookup_cremove_eq. simpl. rewrite String.eqb_refl. reflexivity.
    + destruct (String.eqb y x) eqn:E; [apply String.eqb_eq in E; congruence |].
      rewrite (clookup_cremove_neq γ x y); [| congruence].
      destruct (clookup γ y) eqn:Hlookup; simpl.
      * symmetry. apply subst_closed. eapply cenv_closed_lookup; eassumption.
      * destruct (String.eqb_spec y x); [congruence | reflexivity].
  - destruct (String.eqb_spec y x) as [-> | Hyx].
    + rewrite String.eqb_refl, !cremove_idem. reflexivity.
    + assert (Exy : String.eqb x y = false)
        by (apply String.eqb_neq; congruence).
      rewrite Exy.
      f_equal. rewrite IH; [| apply cenv_closed_remove, Hγ | exact Hu].
      rewrite (cremove_comm γ x y); [reflexivity | congruence].
  - rewrite IHf, IHv; auto.
  - reflexivity.
  - rewrite IH; auto.
  - rewrite IH; auto.
  - rewrite IHc, IH1, IH2; auto.
  - rewrite IH; auto.
  - rewrite IH; auto.
Qed.

(** A free variable after instantiation was already free in the source and
    was not supplied by the environment. Environment images contribute no
    free variables because they are closed. *)
Lemma afi_instantiate_inv : forall t γ x,
  cenv_closed γ -> afi x (instantiate γ t) ->
  afi x t /\ clookup γ x = None.
Proof.
  induction t as [y | y body IH | f IHf u IHu | n | u IH | u IH
                 | c IHc t1 IH1 t2 IH2 | A u IH | u IH A];
    intros γ x Hclosed Hfree; simpl in Hfree.
  - destruct (clookup γ y) eqn:Hlookup.
    + exfalso. exact ((cenv_closed_lookup γ Hclosed y t Hlookup) x Hfree).
    + inversion Hfree; subst. split; [constructor | exact Hlookup].
  - inversion Hfree; subst.
    match goal with
    | Hbodyfree : afi x (instantiate (cremove y γ) body) |- _ =>
        destruct (IH (cremove y γ) x (cenv_closed_remove _ _ Hclosed)
          Hbodyfree) as [Hbody Hnone]
    end.
    split; [constructor; assumption |].
    rewrite (clookup_cremove_neq γ y x) in Hnone by congruence. exact Hnone.
  - inversion Hfree; subst.
    + match goal with
      | Hsub : afi x (instantiate γ f) |- _ =>
          destruct (IHf γ x Hclosed Hsub) as [Hsrc Hnone]
      end.
      split; [constructor; exact Hsrc | exact Hnone].
    + match goal with
      | Hsub : afi x (instantiate γ u) |- _ =>
          destruct (IHu γ x Hclosed Hsub) as [Hsrc Hnone]
      end.
      split; [apply afi_app_r; exact Hsrc | exact Hnone].
  - inversion Hfree.
  - inversion Hfree; subst.
    match goal with
    | Hsub : afi x (instantiate γ u) |- _ =>
        destruct (IH γ x Hclosed Hsub) as [Hsrc Hnone]
    end.
    split; [constructor; exact Hsrc | exact Hnone].
  - inversion Hfree; subst.
    match goal with
    | Hsub : afi x (instantiate γ u) |- _ =>
        destruct (IH γ x Hclosed Hsub) as [Hsrc Hnone]
    end.
    split; [constructor; exact Hsrc | exact Hnone].
  - inversion Hfree; subst.
    + match goal with
      | Hsub : afi x (instantiate γ c) |- _ =>
          destruct (IHc γ x Hclosed Hsub) as [Hsrc Hnone]
      end.
      split; [constructor; exact Hsrc | exact Hnone].
    + match goal with
      | Hsub : afi x (instantiate γ t1) |- _ =>
          destruct (IH1 γ x Hclosed Hsub) as [Hsrc Hnone]
      end.
      split; [apply afi_ifz_t; exact Hsrc | exact Hnone].
    + match goal with
      | Hsub : afi x (instantiate γ t2) |- _ =>
          destruct (IH2 γ x Hclosed Hsub) as [Hsrc Hnone]
      end.
      split; [apply afi_ifz_e; exact Hsrc | exact Hnone].
  - inversion Hfree; subst.
    match goal with
    | Hsub : afi x (instantiate γ u) |- _ =>
        destruct (IH γ x Hclosed Hsub) as [Hsrc Hnone]
    end.
    split; [constructor; exact Hsrc | exact Hnone].
  - inversion Hfree; subst.
    match goal with
    | Hsub : afi x (instantiate γ u) |- _ =>
        destruct (IH γ x Hclosed Hsub) as [Hsrc Hnone]
    end.
    split; [constructor; exact Hsrc | exact Hnone].
Qed.

Inductive cenv_rel (k : nat) : ctx -> aenv -> cenv -> Prop :=
| CEnvRel_nil : cenv_rel k [] [] []
| CEnvRel_cons : forall Γ ρ γ x A (a : aval A) u,
    In a (enum A) ->
    closed u ->
    term_rel k a u ->
    cenv_rel k Γ ρ γ ->
    cenv_rel k ((x, A) :: Γ)
      ((x, PackAval a) :: ρ) ((x, u) :: γ).

#[export] Hint Constructors cenv_rel : pcf.

Lemma cenv_rel_closed : forall k Γ ρ γ,
  cenv_rel k Γ ρ γ -> cenv_closed γ.
Proof.
  intros k Γ ρ γ Henv. induction Henv; intros y v Hin; [contradiction |].
  destruct Hin as [E | Hin].
  - injection E as <- <-. assumption.
  - apply IHHenv with (x := y). exact Hin.
Qed.

Lemma cenv_rel_down : forall k j Γ ρ γ,
  j <= k -> cenv_rel k Γ ρ γ -> cenv_rel j Γ ρ γ.
Proof.
  intros k j Γ ρ γ Hle Henv. induction Henv; constructor; auto.
  eapply term_rel_down; eassumption.
Qed.

Lemma cenv_lookup_rel : forall k Γ ρ γ,
  cenv_rel k Γ ρ γ ->
  forall x A, lookup Γ x = Some A ->
  exists (a : aval A) u,
    alookup ρ x = Some (PackAval a)
    /\ clookup γ x = Some u
    /\ In a (enum A)
    /\ closed u
    /\ term_rel k a u.
Proof.
  intros k Γ ρ γ Henv. induction Henv;
    intros y B Hlookup; simpl in Hlookup; [discriminate |].
  simpl. destruct (String.eqb y x) eqn:E.
  - injection Hlookup as <-. exists a, u. repeat split; assumption.
  - apply IHHenv in Hlookup as (b & v & Hb & Hv & Hcb & Htv & Hrel).
    exists b, v. repeat split; assumption.
Qed.

(** Instantiating every context variable with its related closed term closes
    any term typable in that context. *)
Lemma instantiate_closed_of_typing : forall k Γ ρ γ t A,
  cenv_rel k Γ ρ γ -> Γ ⊢ t ∈ A -> closed (instantiate γ t).
Proof.
  intros k Γ ρ γ t A Henv Hty x Hfree.
  destruct (afi_instantiate_inv t γ x (cenv_rel_closed _ _ _ _ Henv) Hfree)
    as [Hsource Hnone].
  destruct (free_in_ctx _ _ _ _ Hsource Hty) as [B Hlookup].
  destruct (cenv_lookup_rel _ _ _ _ Henv _ _ Hlookup)
    as (a & u & _ & Hconcrete & _).
  rewrite Hconcrete in Hnone. discriminate.
Qed.

(** The open-term conclusion used by the analyser soundness theorem. *)
Definition open_term_rel (Γ : ctx) (ρ : aenv) (γ : cenv)
    (t : term) (A : ty) : Prop :=
  forall k, cenv_rel k Γ ρ γ ->
    term_rel k (aeval Γ ρ t A) (instantiate γ t).
