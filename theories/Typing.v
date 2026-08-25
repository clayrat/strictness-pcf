(** * Typing: the extrinsic judgment Γ ⊢ t ∈ A

    This is the file that replaces the *absence* of a typing judgment in the
    System T development. There, the rules of Fig. 2.1 were absorbed into the
    constructors of [tm]; here they are an inductive predicate over raw terms,
    and every later algorithm is measured against it:

    - the bidirectional checker is a decision procedure whose success implies
      this judgment;
    - the evaluator does not get stuck on terms this judgment accepts;
    - the strictness analyser only runs on such terms.

    The rules are the usual simply-typed ones plus [T_Fix]. Note what typing
    does *not* say: nothing here rules out divergence. [T_Fix] happily types
    [fix_ℕ (λx. x)] at ℕ (Examples.v). Typing excludes *stuck* terms like
    [tsucc (λx. x)], not *diverging* ones. *)

From Stdlib Require Import String List.
Import ListNotations.
From PCF Require Import Ty Syntax Context.

Reserved Notation "Γ '⊢' t '∈' A" (at level 40, t at level 99, A at level 60).

Inductive has_type : ctx -> term -> ty -> Prop :=
| T_Var : forall Γ x A,
    lookup Γ x = Some A ->
    Γ ⊢ tvar x ∈ A
| T_Lam : forall Γ x t A B,
    ((x, A) :: Γ) ⊢ t ∈ B ->
    Γ ⊢ (λ x, t) ∈ A ⇒ B
| T_App : forall Γ t u A B,
    Γ ⊢ t ∈ A ⇒ B ->
    Γ ⊢ u ∈ A ->
    Γ ⊢ t · u ∈ B
| T_Num : forall Γ n,
    Γ ⊢ # n ∈ ℕ
| T_Succ : forall Γ t,
    Γ ⊢ t ∈ ℕ ->
    Γ ⊢ tsucc t ∈ ℕ
| T_Pred : forall Γ t,
    Γ ⊢ t ∈ ℕ ->
    Γ ⊢ tpred t ∈ ℕ
| T_IfZ : forall Γ c t u A,
    Γ ⊢ c ∈ ℕ ->
    Γ ⊢ t ∈ A ->
    Γ ⊢ u ∈ A ->
    Γ ⊢ (ifz c then t else u) ∈ A
(** The replacement for System T's primitive recursion. [trec] could only build
    a value by consuming a numeral, so every System T program terminated;
    [tfix] has no such fuel, and this single rule is the whole difference
    between a total language and one that can diverge. *)
| T_Fix : forall Γ t A,
    Γ ⊢ t ∈ A ⇒ A ->
    Γ ⊢ tfix A t ∈ A
| T_Ann : forall Γ t A,
    Γ ⊢ t ∈ A ->
    Γ ⊢ (t ∷ A) ∈ A

where "Γ '⊢' t '∈' A" := (has_type Γ t A).

#[export] Hint Constructors has_type : pcf.

(** A goal [Γ ⊢ t ∈ A] with [A] fully given is solved by structural search; the
    only leaves needing computation are the [lookup] side conditions of
    [T_Var]. Used throughout Examples.v. *)
Ltac typecheck :=
  repeat (
    match goal with
    | |- has_type _ (tvar _) _ => eapply T_Var; simpl; reflexivity
    | |- has_type _ _ _ => econstructor
    end).

(** ** Inversion

    Stated once as lemmas rather than invoked as the [inversion] tactic: the
    untypability proofs below chain several of them, and named lemmas keep
    those proofs readable. *)

Lemma inv_var : forall Γ x A, Γ ⊢ tvar x ∈ A -> lookup Γ x = Some A.
Proof. inversion 1; auto. Qed.

Lemma inv_lam : forall Γ x t C,
  Γ ⊢ (λ x, t) ∈ C -> exists A B, C = A ⇒ B /\ ((x, A) :: Γ) ⊢ t ∈ B.
Proof. inversion 1; subst; eauto. Qed.

Lemma inv_app : forall Γ t u B,
  Γ ⊢ t · u ∈ B -> exists A, Γ ⊢ t ∈ A ⇒ B /\ Γ ⊢ u ∈ A.
Proof. inversion 1; subst; eauto. Qed.

Lemma inv_num : forall Γ n A, Γ ⊢ # n ∈ A -> A = ℕ.
Proof. inversion 1; auto. Qed.

Lemma inv_succ : forall Γ t A, Γ ⊢ tsucc t ∈ A -> A = ℕ /\ Γ ⊢ t ∈ ℕ.
Proof. inversion 1; auto. Qed.

Lemma inv_pred : forall Γ t A, Γ ⊢ tpred t ∈ A -> A = ℕ /\ Γ ⊢ t ∈ ℕ.
Proof. inversion 1; auto. Qed.

Lemma inv_ifz : forall Γ c t u A,
  Γ ⊢ (ifz c then t else u) ∈ A -> Γ ⊢ c ∈ ℕ /\ Γ ⊢ t ∈ A /\ Γ ⊢ u ∈ A.
Proof. inversion 1; auto. Qed.

Lemma inv_fix : forall Γ t A C, Γ ⊢ tfix A t ∈ C -> C = A /\ Γ ⊢ t ∈ A ⇒ A.
Proof. inversion 1; auto. Qed.

Lemma inv_ann : forall Γ t A C, Γ ⊢ (t ∷ A) ∈ C -> C = A /\ Γ ⊢ t ∈ A.
Proof. inversion 1; auto. Qed.

(** ** Types are not unique

    Worth stating explicitly, because it is the difference from both the
    intrinsic System T syntax (where the type is an index) and from the
    annotated-λ presentations, and because it is the reason the checker needs
    *two*
    judgments instead of one.

    The culprit is [T_Lam], which guesses the domain: nothing in [λ x, # 0]
    determines what [x] ranges over. *)

Example lam_type_not_unique : forall A, [] ⊢ (λ "x", # 0) ∈ A ⇒ ℕ.
Proof. intros A. typecheck. Qed.

(** Variables are the opposite case: their type is read off the context, so it
    *is* unique. Everything below rests on this. *)
Lemma var_type_unique : forall Γ x A B,
  Γ ⊢ tvar x ∈ A -> Γ ⊢ tvar x ∈ B -> A = B.
Proof.
  intros Γ x A B H1 H2.
  eauto using lookup_unique, inv_var.
Qed.

(** ** Weakening *)

Lemma weakening : forall Γ t A, Γ ⊢ t ∈ A -> forall Δ, Γ ⊆ Δ -> Δ ⊢ t ∈ A.
Proof.
  induction 1; intros Δ Hsub; eauto using has_type, incl_ext.
Qed.

Lemma weakening_nil : forall t A Γ, [] ⊢ t ∈ A -> Γ ⊢ t ∈ A.
Proof. intros. eauto using weakening, incl_nil. Qed.

(** ** Well-typed in the empty context implies closed

    The evaluator's precondition: [evalFuel] runs closed programs, and this is what
    guarantees the type checker only hands it such. The work is in
    [free_in_ctx] — a free occurrence must have been justified by a binding. *)

Lemma free_in_ctx : forall x t Γ A,
  afi x t -> Γ ⊢ t ∈ A -> exists B, lookup Γ x = Some B.
Proof.
  intros x t Γ A Hafi. generalize dependent A. generalize dependent Γ.
  induction Hafi; intros Γ C Hty.
  - eauto using inv_var.
  - apply inv_lam in Hty as (A & B & _ & Hbody).
    destruct (IHHafi _ _ Hbody) as [D HD].
    rewrite lookup_neq in HD by assumption. eauto.
  - apply inv_app in Hty as (A & Ht & _). eauto.
  - apply inv_app in Hty as (A & _ & Hu). eauto.
  - apply inv_succ in Hty as [_ Ht]. eauto.
  - apply inv_pred in Hty as [_ Ht]. eauto.
  - apply inv_ifz in Hty as (Hc & _ & _). eauto.
  - apply inv_ifz in Hty as (_ & Ht & _). eauto.
  - apply inv_ifz in Hty as (_ & _ & Hu). eauto.
  - apply inv_fix in Hty as [_ Ht]. eauto.
  - apply inv_ann in Hty as [_ Ht]. eauto.
Qed.

Theorem typable_empty_closed : forall t A, [] ⊢ t ∈ A -> closed t.
Proof.
  intros t A Hty x Hafi.
  destruct (free_in_ctx _ _ _ _ Hafi Hty) as [B HB].
  rewrite lookup_nil in HB. discriminate.
Qed.
