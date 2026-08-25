(** * Examples: representative PCF programs

    The programs used throughout the development are defined once here,
    together with their typing or untypability proofs. Evaluation and analysis
    are then applied to these same terms.

    The pair to keep in view is the two Ωs:

      - [omega_untyped = (λx. x x)(λx. x x)], which no PCF type accepts;
      - [omega = fix_ℕ (λx. x)], which is a perfectly legal program of type ℕ
        and diverges.

    "The same" idea of divergence is rejected in one guise and accepted in the
    other. Typing rules out getting *stuck*; it does not rule out *looping*. *)

From Stdlib Require Import String List.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Arithmetic

    PCF has only [tsucc], [tpred] and [tifz] as numeric primitives, so addition
    and multiplication are *programs*, written with [tfix]. In System T they
    would have been [trec]; the difference is that nothing in the types below
    records that these particular recursions happen to terminate. *)

(** [add = fix (λf m n. ifz m then n else succ (f (pred m) n))]. The body is
    named separately so its abstract functional and fixpoint approximants can
    be inspected directly. *)
Definition add_body : term :=
  λ "f", λ "m", λ "n",
    ifz tvar "m"
    then tvar "n"
    else tsucc (tvar "f" · tpred (tvar "m") · tvar "n").

Definition add : term := tfix (ℕ ⇒ ℕ ⇒ ℕ) add_body.

(** [mul = fix (λf m n. ifz m then 0 else add n (f (pred m) n))] *)
Definition mul : term :=
  tfix (ℕ ⇒ ℕ ⇒ ℕ)
    (λ "f", λ "m", λ "n",
       ifz tvar "m"
       then # 0
       else add · tvar "n" · (tvar "f" · tpred (tvar "m") · tvar "n")).

(** [fact = fix (λf n. ifz n then 1 else mul n (f (pred n)))] — recursive
    factorial, used both for concrete evaluation and approximation.

    The body gets a name of its own: [fact_approx] below is [fact_body]^k
    applied to Ω, while the analyser iterates its abstract shadow. The same
    [F] drives both the concrete approximation table and the abstract fixpoint
    computation. *)
Definition fact_body : term :=
  λ "f", λ "n",
    ifz tvar "n"
    then # 1
    else mul · tvar "n" · (tvar "f" · tpred (tvar "n")).

Definition fact : term := tfix (ℕ ⇒ ℕ) fact_body.

Lemma add_typed : forall Γ, Γ ⊢ add ∈ ℕ ⇒ ℕ ⇒ ℕ.
Proof. intros Γ. unfold add, add_body. typecheck. Qed.

Lemma mul_typed : forall Γ, Γ ⊢ mul ∈ ℕ ⇒ ℕ ⇒ ℕ.
Proof. intros Γ. unfold mul. typecheck. Qed.

Lemma fact_body_typed : forall Γ, Γ ⊢ fact_body ∈ (ℕ ⇒ ℕ) ⇒ ℕ ⇒ ℕ.
Proof. intros Γ. unfold fact_body. typecheck. Qed.

Theorem fact_typed : [] ⊢ fact ∈ ℕ ⇒ ℕ.
Proof. apply T_Fix, fact_body_typed. Qed.

(** Being typable in the empty context, [fact] is closed — the evaluator's
    precondition. *)
Corollary fact_closed : closed fact.
Proof. eapply typable_empty_closed, fact_typed. Qed.

(** ** The typed Ω: divergence the type system admits

    [tfix] asks for a function [A ⇒ A] and returns an [A]; the identity is such
    a function at every [A], so every type has a canonical diverging
    inhabitant. Nothing in the typing derivation notices. *)

Definition omega_at (A : ty) : term := tfix A (λ "x", tvar "x").
Definition omega : term := omega_at ℕ.

Theorem omega_at_typed : forall Γ A, Γ ⊢ omega_at A ∈ A.
Proof. intros Γ A. unfold omega_at. typecheck. Qed.

Theorem omega_typed : [] ⊢ omega ∈ ℕ.
Proof. apply omega_at_typed. Qed.

(** ** A fixpoint approximation table, as a family of programs

    The development deliberately builds no denotational semantics in Rocq — no
    CPO and no compositional ⟦-⟧. The approximation chain

        f⁰(⊥) ⊑ f¹(⊥) ⊑ f²(⊥) ⊑ …   with   fix f = ⊔ fⁿ(⊥),

    nevertheless has an exact *syntactic* shadow: Ω inhabits every type and
    operationally represents ⊥, so the k-th approximant of a fixpoint is
    a PCF program — the body applied to itself k times with Ω plugged in
    for the rest of the recursion:

        fact_approx 0 = Ω_{ℕ⇒ℕ}
        fact_approx (k+1) = fact_body · fact_approx k

    Each approximant is a well-typed program that the evaluator can run.
    Tests.v proves the general divergent half of the table
    ([fact_approx_diverges]: row [k] is undefined at every [n >= k]) and
    runs selected factorial cells below the diagonal. It does not claim that
    those selected runs prove the general factorial equation for all
    [n < k]. The limit ⊔ fⁿ(⊥) is the one thing the evaluator cannot produce,
    and [fact] itself — [fix] instead of an Ω cut-off — stands in for it. *)

Fixpoint fact_approx (k : nat) : term :=
  match k with
  | 0 => omega_at (ℕ ⇒ ℕ)
  | S k' => fact_body · fact_approx k'
  end.

(** Every row of the table is a program of the same type as [fact]. *)
Lemma fact_approx_typed : forall k, [] ⊢ fact_approx k ∈ ℕ ⇒ ℕ.
Proof.
  induction k as [| k IH]; simpl.
  - apply omega_at_typed.
  - eapply T_App; [apply fact_body_typed | exact IH].
Qed.

(** ** The untyped Ω: divergence the type system rejects

    [delta = λx. x x] and [omega_untyped = delta delta]. The obstruction is
    entirely in [delta], and it is not a missing annotation: for [x x] to type,
    the single binding of [x] would have to be read both as [A ⇒ B] and as [A],
    and no simple type satisfies [A = A ⇒ B] (Ty.[tarr_neq_dom]). *)

Definition delta : term := λ "x", tvar "x" · tvar "x".
Definition omega_untyped : term := delta · delta.

(** The heart of the matter: a variable applied to itself. [lookup] is a
    function, so both occurrences get the *same* type from the context. *)
Lemma self_app_untypable : forall Γ x B, ~ (Γ ⊢ (tvar x · tvar x) ∈ B).
Proof.
  intros Γ x B H.
  apply inv_app in H as (A & Hfun & Harg).
  assert (E : A ⇒ B = A) by eauto using var_type_unique.
  exact (tarr_neq_dom A B (eq_sym E)).
Qed.

Theorem delta_untypable : forall Γ C, ~ (Γ ⊢ delta ∈ C).
Proof.
  intros Γ C H. unfold delta in H.
  apply inv_lam in H as (A & B & _ & Hbody).
  exact (self_app_untypable _ _ _ Hbody).
Qed.

Theorem omega_untyped_untypable : forall Γ C, ~ (Γ ⊢ omega_untyped ∈ C).
Proof.
  intros Γ C H. unfold omega_untyped in H.
  apply inv_app in H as (A & Hfun & _).
  exact (delta_untypable _ _ Hfun).
Qed.

(** No annotation repairs it. [delta_untypable] quantifies over *every* [C], so
    there is nothing to annotate with — in contrast to [λx. x], which is
    untypable only in a *synthesizing* position and is fixed by [(λx. x : ℕ ⇒ ℕ)]
    (see [id_annotated_typed] below). *)
Corollary delta_annotated_untypable : forall Γ A C, ~ (Γ ⊢ (delta ∷ A) ∈ C).
Proof.
  intros Γ A C H. apply inv_ann in H as [_ Hd].
  exact (delta_untypable _ _ Hd).
Qed.

Example id_annotated_typed : [] ⊢ ((λ "x", tvar "x") ∷ ℕ ⇒ ℕ) ∈ ℕ ⇒ ℕ.
Proof. typecheck. Qed.

(** ** The other way to fail: getting stuck

    [tsucc (λx. x)] is not a loop and not an annotation problem — it is a term
    whose numeric primitive is handed a function. The evaluator would report it
    as [Stuck]; typing rejects it here, before it ever runs. *)

Definition stuck_succ : term := tsucc (λ "x", tvar "x").

Theorem stuck_succ_untypable : forall Γ C, ~ (Γ ⊢ stuck_succ ∈ C).
Proof.
  intros Γ C H. unfold stuck_succ in H.
  apply inv_succ in H as [_ Hlam].
  apply inv_lam in Hlam as (A & B & Habs & _).
  exact (tnat_neq_tarr A B Habs).
Qed.

(** ** Terms whose fate is decided later

    Typing has nothing more to say about these; they are named for the
    operational and abstract analyses that follow.

    [cbn_flagship = (λx. 0) Ω] is well typed at ℕ. Under call-by-name it
    evaluates to [0]; under call-by-value it would diverge. The typing
    derivation is the same either way — the evaluation strategy, not the type
    system, decides. *)

Definition cbn_flagship : term := (λ "x", # 0) · omega.

Theorem cbn_flagship_typed : [] ⊢ cbn_flagship ∈ ℕ.
Proof. unfold cbn_flagship. eapply T_App; [typecheck | apply omega_typed]. Qed.

(** Its head is a bare λ, so it is typable but not *checkable as written*: the
    algorithm cannot synthesize a type for the function of an application. The
    annotated variant is the form the checker accepts — and the form the
    checker-to-evaluator chain will run. Its typing derivation is obtained in
    Tests.v from a checker run, not rebuilt by hand here. *)
Definition cbn_flagship_ann : term := ((λ "x", # 0) ∷ ℕ ⇒ ℕ) · omega.

(** [loop = fix (λg n. ifz n then g 0 else 0)] — an example of conservative
    strictness analysis. It is a well-typed [ℕ ⇒ ℕ] whose call [loop 0]
    diverges while [loop (n+1)] returns [0]. *)
Definition loop : term :=
  tfix (ℕ ⇒ ℕ)
    (λ "g", λ "n", ifz tvar "n" then tvar "g" · # 0 else # 0).

Theorem loop_typed : [] ⊢ loop ∈ ℕ ⇒ ℕ.
Proof. unfold loop. typecheck. Qed.

(** [blind = λx. loop 0] — the contrasting conservativity example, one
    term away from [loop]. It ignores its argument and runs the diverging
    call [loop 0], so its denotation sends *every* argument — ⊥ included —
    to ⊥: an everywhere-diverging function is strict *by definition*, even
    though it never evaluates its argument. The analysis certifies [loop]
    strict (correctly) yet answers "unknown" for [blind]: the two-point
    domain has already merged 0 with the other defined numbers, so the
    abstract [ifz] cannot see that [loop 0] takes the diverging branch. The
    difference isolates exactly the information lost by the abstraction.
    Tests.v proves the blindness is only the analysis's: [loop · # 0] really
    diverges. *)
Definition blind : term := λ "x", loop · # 0.

Theorem blind_typed : [] ⊢ blind ∈ ℕ ⇒ ℕ.
Proof.
  unfold blind. apply T_Lam. eapply T_App; [| apply T_Num].
  apply weakening_nil, loop_typed.
Qed.

(** A slow but total program, indistinguishable from [omega] by a run whose
    fuel is too small: [slow n] counts down from [n] and returns [0]. *)
Definition slow : term :=
  tfix (ℕ ⇒ ℕ)
    (λ "f", λ "n", ifz tvar "n" then # 0 else tvar "f" · tpred (tvar "n")).

Theorem slow_typed : [] ⊢ slow ∈ ℕ ⇒ ℕ.
Proof. unfold slow. typecheck. Qed.

(** Two first-order functions used to contrast analyser results:
    [λx. succ x] is strict, [λx. 0] is not. Both are typable, and typing cannot
    tell them apart. *)

Definition strict_succ : term := λ "x", tsucc (tvar "x").
Definition const_zero  : term := λ "x", # 0.

Theorem strict_succ_typed : [] ⊢ strict_succ ∈ ℕ ⇒ ℕ.
Proof. unfold strict_succ. typecheck. Qed.

Theorem const_zero_typed : [] ⊢ const_zero ∈ ℕ ⇒ ℕ.
Proof. unfold const_zero. typecheck. Qed.
