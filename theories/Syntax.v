(** * Syntax: raw, extrinsically typed PCF terms

    In the NbE development for System T the syntax was an inductive *family*
    [tm : cxt -> ty -> Type]: ill-typed terms did not exist, so there was no
    typing judgment to formalize and nothing for a type checker to do. Here the
    terms form an ordinary inductive *type*: [term] contains [tsucc (λx. x)]
    just as happily as [tsucc (tnum 3)], and it is the separate judgment
    [Γ ⊢ t ∈ A] of Typing.v that rules the first one out.

    Two reasons for the switch, both about the algorithms this development is
    building towards:

    - a type checker needs ill-typed input to reject; with intrinsic syntax the
      only inhabitants of [tm] are already well-typed, and the "checker" would
      be the identity;

    - extraction. Intrinsic indices survive extraction as ordinary runtime
      fields and can force casts into type-directed code; the extracted OCaml
      here is an ordinary variant type over strings, [nat] and [ty].

    Variables are strings, not de Bruijn indices, for the same reason: the type
    checker does a *lookup by name* in a context, and its error messages
    can name the offending variable. Nothing below depends on names being
    distinct — the context is an association list and lookup takes the leftmost
    binding, so shadowing works by construction.

    Numerals are literals [tnum n] rather than [zero]/[succ] chains. This is the
    operational convention made structural: the values of type ℕ are exactly the
    numerals, and [tsucc]/[tpred]/[tifz] are strict operations that must first
    reduce their numeric argument to one. The design note below records why. *)

(** ** Design note: why [tnum] + [ifz] + [tpred]

    Two independent axes were on the table: numerals as literals [tnum n] or as
    unary [tzero]/[tsucc], and the eliminator as the non-binding [ifz] (with
    [tpred] primitive) or as a binding [casez t of zero ⇒ u | succ x ⇒ v] (with
    [tpred] derived). All four combinations are coherent.

    The denotational account and strictness analysis are indifferent to both
    axes. The abstract clauses
    coincide — [succ♯] = [pred♯] = id, every numeral ↦ ⊤, and [casez]'s binder
    would receive exactly the scrutinee's [c♯], so no precision is lost either
    way; the abstract fixpoint iteration for [add] is the same table in every
    variant ([a₀] = λm n. ⊥, then [a₁] = m ⊓ n, stable from there); and the
    [loop] conservativity demo yields [loop♯] = λn. n in every variant. The
    decision therefore falls to operational simplicity and the clarity of the
    concrete-to-abstract comparison.

    [ifz] makes the concrete clause and its abstract shadow directly
    comparable:

        ⟦ifz c then t else u⟧ ρ = ⊥ / ⟦t⟧ρ / ⟦u⟧ρ    (by the value of c)
        ⟦ifz c then t else u⟧♯ρ = c♯ ⊓ (t♯ ⊔ u♯)

    where the test collapses to a meet and the two branches to a join. [casez]
    carries a ρ[x ↦ c♯] into the abstract line and blurs that parallel; it would
    also add an unused binder to [loop], obscuring the direct comparison between
    the successful and inconclusive analysis results.

    [tnum] wins operationally and denotationally: "the values of ℕ are exactly
    the numerals" stays
    structural instead of becoming a recursive predicate threaded through
    [value], [step] and progress; a numeral is built in O(1) and extracts to an
    OCaml [int]; and the flat domain becomes a literal bijection, one syntactic
    node per element of ℕ_⊥ \ {⊥}.

    The price is cosmetic: [add]/[mul]/[fact] descend via [tpred] instead of by
    structural recursion on a [casez] binder, and we forgo a second place where
    the analysis's information loss shows for free ([casez]'s binder abstracts
    to ⊤ whatever was matched). In exchange [tpred] is genuinely primitive: no
    term over [tzero], [tsucc], [ifz] and [tfix] defines it, by the admissible
    relation n R m iff (n = 0 ↔ m = 0), which all of them preserve while
    1 R 2 yet pred 1 = 0 and pred 2 = 1. This is the analyser's loss-of-
    precision argument one abstraction finer, already visible in the syntax. *)

From Stdlib Require Import String.
From PCF Require Import Ty.

Open Scope string_scope.

(** Without this, the printer shows a variable name as a chain of
    [String.String (Ascii.Ascii ...)] constructors: [Require Import String]
    binds no scope to the type [string], so the [string] arguments of [tvar]
    and [tlam] are not printed in [string_scope]. *)
Bind Scope string_scope with string.

(** ** Terms

    Two constructors carry a type, and both are there for the bidirectional
    bidirectional checker rather than for the declarative typing judgment:

    - [tann t A] is the annotation [(t : A)], the one way to put a checked term
      into a synthesizing position;

    - [tfix A t] is [fix_A t]. Recursion has no argument to synthesize from —
      [fix] applied to [λx. x] can produce a value of *any* type [A] — so the
      operator therefore carries its result type, [fix_A : (A → A) → A].

    λ-abstraction, by contrast, is deliberately *not* annotated. Its domain is
    guessed by the declarative rule [T_Lam], which is exactly what makes typing
    non-unique (Typing.v, [lam_type_not_unique]) and forces the checker to
    receive the domain from an expected type instead of synthesizing it. *)

Inductive term : Type :=
| tvar  : string -> term
| tlam  : string -> term -> term
| tapp  : term -> term -> term
| tnum  : nat -> term
| tsucc : term -> term
| tpred : term -> term
| tifz  : term -> term -> term -> term
| tfix  : ty -> term -> term
| tann  : term -> ty -> term.

Declare Scope pcf_scope.
Delimit Scope pcf_scope with pcf.
Bind Scope pcf_scope with term.

(** Compact surface notations. [tsucc]/[tpred]/[tfix]
    are written out; only the noisy formers get sugar. *)

Notation "'λ' x , t" := (tlam x t)
  (at level 200, x at level 0, t at level 200, right associativity) : pcf_scope.
Notation "t · u" := (tapp t u)
  (at level 65, left associativity) : pcf_scope.
Notation "'ifz' c 'then' t 'else' u" := (tifz c t u)
  (at level 200, c at level 99, t at level 99, u at level 200) : pcf_scope.
Notation "t ∷ A" := (tann t A)
  (at level 100, A at level 60) : pcf_scope.
Notation "'#' n" := (tnum n)
  (at level 0, n at level 0) : pcf_scope.

Open Scope pcf_scope.

(** ** Free variables

    [afi x t] ("[x] appears free in [t]") is the standard inductive
    characterization; note the side condition [x <> y] in [afi_lam], the one
    place where names are not inert. It is used in Typing.v to show that a term
    typable in the empty context is closed, which is the precondition every
    program run by the evaluator must satisfy. *)

Inductive afi (x : string) : term -> Prop :=
| afi_var   : afi x (tvar x)
| afi_lam   : forall y t, x <> y -> afi x t -> afi x (λ y, t)
| afi_app_l : forall t u, afi x t -> afi x (t · u)
| afi_app_r : forall t u, afi x u -> afi x (t · u)
| afi_succ  : forall t, afi x t -> afi x (tsucc t)
| afi_pred  : forall t, afi x t -> afi x (tpred t)
| afi_ifz_c : forall c t u, afi x c -> afi x (ifz c then t else u)
| afi_ifz_t : forall c t u, afi x t -> afi x (ifz c then t else u)
| afi_ifz_e : forall c t u, afi x u -> afi x (ifz c then t else u)
| afi_fix   : forall A t, afi x t -> afi x (tfix A t)
| afi_ann   : forall t A, afi x t -> afi x (t ∷ A).

#[export] Hint Constructors afi : pcf.

Definition closed (t : term) : Prop := forall x, ~ afi x t.

(** ** Decidable equality

    Not needed by the typing judgment, but the evaluator's test suite compares
    terms, and a raw syntax tree with no indices makes this a one-liner. *)

Definition term_eq_dec : forall t u : term, {t = u} + {t <> u}.
Proof.
  decide equality; auto using ty_eq_dec, string_dec, PeanoNat.Nat.eq_dec.
Defined.
