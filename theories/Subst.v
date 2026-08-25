(** * Subst: substitution of closed terms

    The β-rule is [(λ x, t) · u --> [x := u] t], so the evaluator needs
    substitution — and substitution over named syntax has exactly one famous
    failure mode: *capture*. Substituting a term with a free [y] under a
    binder for [y] silently changes what that [y] means:

        [x := y] (λ y, x)  =  λ y, y

    The left side is the constant function returning the ambient [y]; the
    right side is the identity. The α-correct answer renames the binder
    first — [λ y', y] — and textbook capture-avoiding substitution does
    exactly that. The [subst] below deliberately does not: it walks the
    term, stops at a binder that shadows [x], and renames nothing.

    Naive substitution is nevertheless correct on every term the evaluator
    ever builds, by three facts working together:

    - **programs start closed.** The checker hands the evaluator terms typable in the
      empty context ([check_program]), and such terms have no free variables
      ([typable_empty_closed]);

    - **reduction is weak.** No rule of Semantics.v steps under a binder:
      the contexts the relation descends through — the head of an
      application, the operand of [succ]/[pred], the scrutinee of [ifz] —
      bind nothing. A free variable of a redex is therefore free in the
      whole program, so in a closed program the argument [u] of every β that
      ever fires is itself closed — and a closed argument has no free
      variable to capture;

    - **closedness survives.** Preservation keeps the program typable in
      [[]], hence closed, so the two facts above hold at every step of the
      run, not only the first.

    The typing side of the same story is [subst_typing] below, which demands
    the substituted term typed in the *empty* context. The hypothesis earns
    its keep in the variable case: a closed [s] weakens into any context
    ([weakening_nil]) — in particular past binders that would have changed
    the meaning of an open term's free variables. That failure of weakening
    for open terms *is* capture, seen from the typing side, and it is not
    hypothetical: in a non-empty context preservation is simply false —
    with [y : ℕ] in scope, the well-typed

        (λ x, λ y, x) · y  ∈  (ℕ ⇒ ℕ) ⇒ ℕ

    β-steps by capture to [λ y, y], which does not have that type. Tests.v
    freezes both the capture and the broken preservation
    ([capture_breaks_preservation]). Every theorem of Semantics.v and
    Safety.v is therefore stated in the empty context — the only case the
    evaluator's contract covers anyway.

    What the trade buys, and what the alternatives would cost:

    - capture-avoiding substitution is not structurally recursive (the
      renamed body [[y := y'] b] has the same size, so recursion needs a
      size measure), wants a fresh-name supply, and drags α-equivalence
      through every statement about terms — a heavy price for a generality
      the evaluator cannot observe. This is the same trade Software
      Foundations makes for the same reason;
    - de Bruijn indices dissolve capture by construction, but this development
      uses names so the checker can say "unbound variable x" and the extracted
      OCaml reads like an interpreter;
    - the place a development *must* pay for renaming (or indices) is any
      reduction that goes under binders and hence meets open terms — e.g.
      a normalizer that reduces under lambdas. Weak reduction is
      what makes the naive definition sound here, not anything about PCF
      itself.

    The one subtle clause is the binder: [subst] stops at a λ that rebinds
    [x]. This is shadowing again, the same leftmost-wins convention as
    [lookup], and the two conventions meet in the λ-case of [subst_typing],
    which is discharged by [incl_shadow] / [incl_swap] — the two context
    rearrangements Context.v provides. *)

From Stdlib Require Import String List.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing.

Open Scope string_scope.
Open Scope pcf_scope.

Fixpoint subst (x : string) (s : term) (t : term) : term :=
  match t with
  | tvar y   => if String.eqb y x then s else t
  | λ y, b   => if String.eqb y x then t else λ y, subst x s b
  | f · u    => subst x s f · subst x s u
  | # n      => # n
  | tsucc u  => tsucc (subst x s u)
  | tpred u  => tpred (subst x s u)
  | ifz c then a else b =>
      ifz subst x s c then subst x s a else subst x s b
  | tfix A u => tfix A (subst x s u)
  | u ∷ A    => subst x s u ∷ A
  end.

(** The notation is [<[ x := s ]> t] rather than [[x := s] t]
    only because square brackets already belong to lists ([[]] is the empty
    context all over this development). *)
Notation "'<[' x ':=' s ']>' t" := (subst x s t) (at level 20) : pcf_scope.

(** Substitution has no effect when its variable is not free.  The closed
    instance is useful when reducing nested named lambdas: after the outer
    beta-step has installed a closed argument, later substitutions cannot
    capture or otherwise change it. *)
Lemma subst_not_free : forall t x s, ~ afi x t -> subst x s t = t.
Proof.
  induction t as [y | y b IH | f IHf a IHa | n | u IH | u IH
                 | c IHc t1 IHt1 t2 IHt2 | A u IH | u IH A];
    intros x s Hfree; simpl.
  - destruct (String.eqb_spec y x) as [-> | Hne].
    + exfalso. apply Hfree, afi_var.
    + reflexivity.
  - destruct (String.eqb_spec y x) as [-> | Hne]; [reflexivity |].
    f_equal. apply IH. intros Hx. apply Hfree. apply afi_lam.
    + intros E. apply Hne. symmetry. exact E.
    + exact Hx.
  - f_equal.
    + apply IHf. intros Hx. apply Hfree. apply afi_app_l. exact Hx.
    + apply IHa. intros Hx. apply Hfree. apply afi_app_r. exact Hx.
  - reflexivity.
  - f_equal. apply IH. intros Hx. apply Hfree. apply afi_succ. exact Hx.
  - f_equal. apply IH. intros Hx. apply Hfree. apply afi_pred. exact Hx.
  - f_equal.
    + apply IHc. intros Hx. apply Hfree. apply afi_ifz_c. exact Hx.
    + apply IHt1. intros Hx. apply Hfree. apply afi_ifz_t. exact Hx.
    + apply IHt2. intros Hx. apply Hfree. apply afi_ifz_e. exact Hx.
  - f_equal. apply IH. intros Hx. apply Hfree. apply afi_fix. exact Hx.
  - f_equal. apply IH. intros Hx. apply Hfree. apply afi_ann. exact Hx.
Qed.

Corollary subst_closed : forall t x s, closed t -> subst x s t = t.
Proof. intros t x s Hclosed. apply subst_not_free, Hclosed. Qed.

(** ** Substitution preserves typing

    If [t] is typed under an assumption [x : A] and [s] is a *closed* term of
    type [A], then [[x := s] t] is typed without the assumption. The proof is
    induction on [t]; the two λ-subcases are where the shadowing conventions
    of [subst] and [lookup] have to agree:

    - the binder rebinds [x]: [subst] stopped, and [incl_shadow] discards the
      now-invisible assumption;
    - the binder is some other [y]: [incl_swap] commutes it past [x : A] so
      the induction hypothesis applies. *)

Lemma subst_typing : forall t Γ x A s B,
  ((x, A) :: Γ) ⊢ t ∈ B ->
  [] ⊢ s ∈ A ->
  Γ ⊢ <[ x := s ]> t ∈ B.
Proof.
  induction t as [ y | y b IH | f IHf a IHa | n | u IH | u IH
                 | c IHc t1 IHt1 t2 IHt2 | A0 u IH | u IH A0 ];
    intros Γ x A s B Ht Hs; simpl.
  - (* tvar y *)
    apply inv_var in Ht. simpl in Ht.
    destruct (String.eqb y x) eqn:E.
    + injection Ht as <-. apply weakening_nil, Hs.
    + apply T_Var, Ht.
  - (* λ y, b *)
    apply inv_lam in Ht as (A1 & B1 & -> & Hb).
    destruct (String.eqb_spec y x) as [-> | Hne].
    + (* the binder shadows x: substitution stopped *)
      apply T_Lam. eapply weakening; [exact Hb | apply incl_shadow].
    + apply T_Lam. eapply IH; [| exact Hs].
      eapply weakening; [exact Hb | apply incl_swap; auto].
  - (* application *)
    apply inv_app in Ht as (A1 & Hf & Ha). eauto using has_type.
  - (* numeral *)
    apply inv_num in Ht as ->. apply T_Num.
  - (* succ *)
    apply inv_succ in Ht as [-> Hu]. eauto using has_type.
  - (* pred *)
    apply inv_pred in Ht as [-> Hu]. eauto using has_type.
  - (* ifz *)
    apply inv_ifz in Ht as (Hc & H1 & H2). eauto using has_type.
  - (* fix *)
    apply inv_fix in Ht as [-> Hu]. eauto using has_type.
  - (* annotation *)
    apply inv_ann in Ht as [-> Hu]. eauto using has_type.
Qed.
