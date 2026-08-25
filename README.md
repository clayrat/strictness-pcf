# Strictness analysis for PCF, in Rocq

A standalone Rocq development of the simply typed λ-calculus with natural
numbers and **general recursion**. It centers on three executable algorithms:
a bidirectional type checker, a call-by-name evaluator, and a finite-domain
strictness analyser.

Unlike an intrinsically typed presentation of a total calculus such as System
T, PCF admits divergence and this development keeps its *terms* extrinsic. The
finite abstract values are indexed by PCF type and their dependent eliminations
use the Equations plugin. The development is tested with Rocq 9.1 and every
result below is proved **axiom-free** (`Print Assumptions` reports "Closed under
the global context").

## Status

The executable checker, evaluator, and analyser are formalized together with
their correctness properties. Operational approximation results connect
evaluation to the intended denotational reading, and the strictness analyser
has an end-to-end operational soundness theorem. A separate compositional
denotational semantics and adequacy theorem remain future work.

| Component | Status |
|---|---|
| raw syntax and declarative typing `Γ ⊢ t ∈ A` | formalized |
| bidirectional `infer` / `check` and OCaml extraction | formalized |
| CBN small-step `step`, `evalFuel`, and type safety | formalized |
| operational approximations and observations | formalized |
| compositional denotational semantics and adequacy | described, not mechanized |
| finite strictness domains, order theory, and analyser monotonicity | formalized |
| step-indexed operational relation and strictness bridge | formalized |
| fundamental theorem and `certified_strict` soundness | formalized |

## Building

```sh
opam install rocq-equations                  # once, in the active Rocq switch
coq_makefile -f _CoqProject -o Makefile   # once
make                                       # builds everything
make -C extraction                         # extract and run the executable examples
```

`_CoqProject` maps `theories/` to the `PCF` logical prefix (`-Q theories PCF`)
and lists the files in dependency order. The `extraction/` directory is
deliberately *not* part of that build: it is a standalone driver that runs
`coqc` itself and then `dune` (see below).

## Files

| File | What's in it |
|------|--------------|
| `Ty.v` | The two type formers, `A, B ::= ℕ \| A ⇒ B`. Decidable equality in both flavours (`ty_eq_dec` for proofs, `ty_eqb` for the extracted checker) and `tarr_neq_dom : A <> A ⇒ B`, the size argument behind the untyped Ω. |
| `Syntax.v` | Raw terms over string names, surface notations, free variables (`afi`, `closed`), `term_eq_dec`. |
| `Context.v` | Contexts as association lists, `lookup`, and the inclusion relation `Γ ⊆ Δ` used for weakening. |
| `Typing.v` | The judgment `Γ ⊢ t ∈ A`, named inversion lemmas, the `typecheck` tactic, weakening, and `typable_empty_closed`. |
| `Checker.v` | The two judgments `Γ ⊢ t ⇑ A` / `Γ ⊢ t ⇓ A`, the mutually recursive `infer` / `check` with their error type, and the metatheory: soundness against `has_type`, soundness and completeness for the bidirectional judgments, uniqueness of synthesis, decidability, and `check_incomplete` for declarative typing. |
| `Subst.v` | Non-renaming substitution `<[ x := s ]> t` (correct because the evaluator only ever substitutes closed arguments), the no-op lemmas for absent/closed terms, and `subst_typing`. |
| `OperationalSemantics.v` | Values, the CBN relation `t --> u`, `-->*` with its congruences, the functions `step` / `evalFuel`, soundness + completeness, determinism, value monotonicity, and the operational `diverges` predicate with closure through strict contexts. |
| `Safety.v` | Canonical forms, `progress`, `preservation`, `eval_safe` / `eval_no_stuck` / `eval_nat_numeral`, and `check_eval_contract`, which connects successful checking to safe evaluation. |
| `Strictness.v` | The type-indexed finite domains `aval A` as *monotone* tables (`enum` filters by `monotone_tbl` — load-bearing: a non-monotone table oscillates under iteration, see `Tests.not_table_oscillates`), `abot` / `dsize`, the checking-mode abstract interpreter `aeval` with the `fix` iteration `afix_approx`, and the API `analyse` / `certified_strict`. |
| `FiniteOrder.v` | Representation-independent order theory: carrier-scoped posets and bounded join-semilattices, the derived join algebra, and stabilization/leastness/monotonicity of finite monotone iteration. It has no dependency on PCF. |
| `AbstractDomain.v` | The order theory of `aval A`: on the enumerated carrier, `aleb` is a decidable partial order (a mere preorder on raw tables), `aapply` is closed and monotone, `abot` least, `ajoin` the least upper bound with its derived algebra; instantiates `FiniteOrder.v`'s interfaces (`aval_finite_poset`, `aval_join_semilat`) and establishes `enum ≤ dsize`. |
| `Stabilization.v` | The bounded-iteration fixpoint theorem on top of `AbstractDomain.v` (which it re-exports): `afix_approx_is_fixpoint`, `afix_stable`, `afix_approx_enum`/`_mono`, and the least-fixpoint theorem `afix_least`. `cval A` packages a value with its carrier proof. |
| `AnalysisProperties.v` | The mutual carrier/monotonicity theorem for synthesis and checking derivations: under carrier-valued pointwise-ordered environments, `aeval` returns carrier values and is monotone. Thus every checked `fix` functional satisfies the stabilization theorem's premise (`checked_fix_is_fixpoint`). |
| `LogicalRelation.v` | The cumulative step-indexed relation between `aval A` and concrete terms, its operational and order closure laws, compatibility lemmas, simultaneous closing substitutions and related environments, and natural bottom as divergence. |
| `AnalysisSoundness.v` | The mutual `logical_fundamental` theorem connecting checked terms to `aeval`, its closed-term specialization, and the end-to-end `certified_strict_sound` theorem for the public Boolean query. |
| `Examples.v` | `add`, `mul`, `fact` (with `fact_body` named), both Ωs, `loop`, `slow`, the approximant family `fact_approx k = fact_body^k(Ω)`, and the typing / untypability theorems about them. |
| `Tests.v` | Executable checker, evaluator, and analyser cases frozen as `reflexivity`, plus inductive totality/divergence proofs that no finite run could establish: the factorial-approximant region and operational witnesses for every positive strictness claim. |
| `extraction/Extract.v` | Extraction driver: `nat` ↦ `int`, `string` ↦ native OCaml strings, then `Extraction "checker.ml" infer check subst step evalFuel analyse certified_strict …`. |
| `extraction/main.ml` | The OCaml demo: pretty-printers and result tables for the checker, evaluator, and strictness analyser. Ends in `assert`s that agree with `Tests.v`, including rejection of a wrong-typed strictness query. |

## Three core design decisions

### 1. Typing is a judgment, not an index

System T's `tm : cxt -> ty -> Type` made ill-typed terms non-existent, so there
was no typing judgment, no type checker to write, and no subject reduction to
prove. PCF here uses raw syntax plus a separate

```coq
Inductive has_type : ctx -> term -> ty -> Prop
```

for three reasons, all about what comes next:

- **a type checker needs ill-typed input to reject.** With intrinsic syntax the
  checker would be the identity function on `tm`;
- **extraction stays readable.** Intrinsic indices survive extraction as runtime
  fields and can force casts into type-directed code; the extracted OCaml here
  is an ordinary variant type over strings, `int` and `ty`;
- **the evaluator needs no types at run time at all**, unlike NbE — and the
  abstract interpreter consults them only where its *domain* is
  type-indexed: tabulating a λ means enumerating the finite 𝔻 of its
  argument's type, and bounding the `fix` iteration means measuring 𝔻. What
  neither algorithm needs is intrinsic term indices.

There is deliberately no `intrinsify` pass turning derivations back into
intrinsic terms.

The choice of the *numeric* fragment — `tnum n` with `ifz` and a primitive
`tpred`, rather than unary `tzero`/`tsucc` or a binding `casez` — is argued in
the design note at the top of `Syntax.v`, which also records why the
denotational model and strictness analysis are indifferent to it.

### 2. Names, not de Bruijn indices

A context is a `list (string * ty)` and `lookup` takes the leftmost binding, so
shadowing works with no freshness side conditions. This buys two things: the
checker performs a genuine *lookup by name* and can name the variable in its
error messages, and the extracted OCaml reads like an ordinary interpreter.

The one place names are not inert is the binder case of `afi`, which carries
`x <> y`.

### 3. `fix` is annotated, λ is not

`tfix A t` represents `fix_A : (A → A) → A` and `tann t A` is the
annotation `(t : A)`. λ-abstraction carries no annotation, so the declarative
rule has to *guess* the domain:

```coq
| T_Lam : forall Γ x t A B, ((x, A) :: Γ) ⊢ t ∈ B -> Γ ⊢ (λ x, t) ∈ A ⇒ B
```

which is exactly why types are **not unique**:

```coq
Example lam_type_not_unique : forall A, [] ⊢ (λ "x", # 0) ∈ A ⇒ ℕ.
```

That failure of uniqueness motivates the bidirectional mode split: a λ cannot
synthesize a type, only check against one. Variables, by contrast, read their
type off the context, so `var_type_unique` holds — and that tiny fact is what
makes the untyped Ω untypable.

## Declarative typing: what it proves

The central distinction is that the two ways a program can fail to produce a
value are independent, and typing catches exactly one of them.

**Typing rules out getting stuck.** `succ (λx. x)` is not a loop; it is a
numeric primitive handed a function, and no type accepts it:

```coq
Theorem stuck_succ_untypable : forall Γ C, ~ (Γ ⊢ tsucc (λ "x", tvar "x") ∈ C).
```

**Typing does not rule out looping.** `fix` types at every `A` via the identity,
so every type has a canonical diverging inhabitant, and the derivation notices
nothing:

```coq
Theorem omega_at_typed : forall Γ A, Γ ⊢ tfix A (λ "x", tvar "x") ∈ A.
```

**The two Ωs.** `(λx. x x)(λx. x x)` is rejected; `fix_ℕ (λx. x)` is accepted and
diverges. The same idea of divergence, rejected in one guise and accepted in the
other:

```coq
Theorem omega_untyped_untypable : forall Γ C, ~ (Γ ⊢ delta · delta ∈ C).
Theorem omega_typed            : [] ⊢ tfix ℕ (λ "x", tvar "x") ∈ ℕ.
```

**The obstruction is not a missing annotation.** The whole difficulty sits in
`delta = λx. x x`: `lookup` is a function, so both occurrences of `x` receive
the *same* type `A` from the context, and `x x` would need `A = A ⇒ B` —
impossible by a size argument (`Ty.tarr_neq_dom`). Since `delta_untypable`
quantifies over *every* type, there is nothing to annotate with:

```coq
Corollary delta_annotated_untypable : forall Γ A C, ~ (Γ ⊢ (delta ∷ A) ∈ C).
```

Contrast `λx. x`, which is untypable only in a *synthesizing* position and is
repaired by `(λx. x : ℕ ⇒ ℕ)` — the distinction made precise by the
bidirectional checker.

## The bidirectional checker

The declarative judgment is not an algorithm, and `lam_type_not_unique` says
why: `T_Lam` guesses the domain of a λ, and there is no canonical guess. The
checker splits the judgment by the *direction information flows*,

```coq
Γ ⊢ t ⇑ A     (synthesis: A is an output)
Γ ⊢ t ⇓ A     (checking:  A is an input)
```

and assigns every term former to one mode. Variables, numerals, `succ`/`pred`, the
annotated `fix_A` and the annotation `(t : A)` **synthesize**; λ and `ifz`
**check**. The two modes meet exactly twice:

- `I_App` synthesizes the function first and *uses* the domain it obtains as the
  expected type of the argument. That is why a bad argument is reported at the
  argument;
- `C_Switch` is the mode switch — a term that synthesizes `A` checks against
  `A`. It is the only rule that consumes `ty_eqb`, and the only source of an
  "expected X, got Y" message.

### The algorithm

```coq
Fixpoint infer (G : ctx) (t : term) : result ty
with     check (G : ctx) (t : term) (B : ty) : result unit
```

`result` carries an `error` rather than a `bool`, because the failure location
is part of the checker's API: `E_Unbound`, `E_NoSynth`, `E_NotFun`,
`E_LamNotFun` and `E_Mismatch` each name the offending subterm.

One wrinkle worth knowing before reading the code: `check`'s last seven branches
look like a copy of `infer`. Morally they are the single equation

```coq
Lemma check_switch : synthesizing t = true -> check G t B = switch t B (infer G t).
```

which cannot be *written* as the definition, because the guard condition rejects
a mutual call `infer G t` on the very argument `check` recurses on. So the
branches call `infer` only on the strict subterm of an application, and the
intended equation is recovered as a lemma — which every proof afterwards uses,
so the duplication is discharged once.

The duplication is avoidable, but only by moving the mode discipline out of the
functions and into the datatype: split raw terms into checkable `val` and
synthesizable `neu` joined by `emb : neu -> val` and the cut. `Checker.v` writes
that variant out in full after `check_switch`. It also deletes `E_NoSynth` (a λ
in synthesizing position stops being a *typing* error and becomes an
unrepresentable term) and the annotation on `fix` (a checkable former needs
none). A further variation annotates the λ itself as a separate synthesizing
form, so only the *head* λ of an application spine carries a type. What the
split costs is the uniform raw syntax and, more concretely, closure under
substitution: β-reduction would need a type at every step.

### What is proved

| Theorem | Statement |
|---|---|
| `bidir_sound` | both judgments imply `Γ ⊢ t ∈ A` — nothing untypable is ever accepted |
| `algo_sound` | `infer G t = Ok A` ⟹ `Γ ⊢ t ⇑ A`, and `check G t A = Ok tt` ⟹ `Γ ⊢ t ⇓ A` |
| `algo_complete` | completeness for the bidirectional judgments: the functions find whatever the `⇑` / `⇓` rules derive |
| `synth_unique` | synthesized types are unique, although declarative types are not |
| `synth_dec`, `check_dec` | the judgments are decidable — unlike evaluation, the checker answers on every input |
| `check_program` | `check [] t A = Ok tt` ⟹ `[] ⊢ t ∈ A` **and** `closed t`, the evaluator's precondition |
| `check_incomplete` | the converse of soundness **fails**, by design |

Thus `algo_complete` is deliberately not completeness for the declarative
judgment `Γ ⊢ t ∈ A`. The last row is the witness: `(λx. x) 0` is typable by
the declarative rules but the checker rejects it, pointing at the λ:

```coq
Example id_applied_rejected : infer [] id_applied = Err (E_NoSynth (λ "x", tvar "x")).
Theorem check_incomplete : exists t A, [] ⊢ t ∈ A /\ check [] t A <> Ok tt.
```

An annotation repairs it — and that is the difference from `delta = λx. x x`,
which no annotation repairs (`delta_annotated_untypable`). The two failures
look alike on the surface and are not the same failure: one is the mode
discipline asking for information, the other is the type system refusing.

The central call-by-name example, `(λx. 0) Ω`, is in the first class: it is
well typed but not checkable, because its head is a bare λ in a synthesizing
position. `Tests.v` therefore defines `cbn_flagship_ann = ((λx. 0) : ℕ ⇒ ℕ) Ω`,
which synthesizes ℕ while still containing a diverging subterm.

### Extraction

Because the syntax is extrinsic, `term` extracts to an ordinary variant over
`string`, `int` and `ty`, and the checker becomes two mutually recursive
functions over it, with no `Obj.magic` or residual index fields.

```ocaml
let rec infer g t = match t with
| Tvar x -> lookup_ty g x
| Tapp (f, u) -> apply_to f (infer g f) (check g u)
| Tnum _ -> Ok Tnat
| Tsucc u -> after (check g u Tnat) Tnat
| Tpred u -> after (check g u Tnat) Tnat
| Tfix (a, u) -> after (check g u (Tarr (a, a))) a
| Tann (u, a) -> after (check g u a) a
| _ -> Err (E_NoSynth t)
```

`make -C extraction` regenerates `checker.ml` and runs `main.ml`, which prints
the checker results: `fact` checks, Ω synthesizes ℕ, the untyped Ω is rejected with
*cannot synthesize a type for δ*, `succ (λx. x)` with *λx. x is a function, but ℕ
was expected*, and `(λf. f 0 : (ℕ → ℕ) → ℕ) 3` with *3: expected ℕ → ℕ, got ℕ* —
the argument blamed, not the application. There is no parser: the driver builds
terms with the extracted constructors, which is also a small demonstration that
the extracted API is usable OCaml.

Every line the driver prints is frozen independently in `Tests.v` as a
kernel-checked `reflexivity`, error messages included.

## Call-by-name evaluation and type safety

The step relation is call-by-name, and the convention is stated once: the
β-rule substitutes the argument **unevaluated** (there is no congruence rule
for the argument of an application), while `succ`, `pred` and `ifz` are strict
— each drives its numeric operand to a numeral first. The values of type ℕ are
exactly the numerals; the flat domain ℕ⊥ is this convention's denotational
shadow. `fix` takes one unconditional unfolding `fix_A t --> t (fix_A t)` — the
whole difference from System T's `trec`, which consumed a numeral per unfolding
and therefore had to stop.

Substitution is the naive, non-renaming one. `Subst.v`'s header lays out the
three-fact argument that makes it sound — programs start closed, reduction is
weak (no rule steps under a binder, so every β-argument that ever fires is
closed), and preservation keeps the program closed — and `Tests.v` freezes the
boundary: on an *open* term substitution really captures, and preservation in
a non-empty context is really false (`capture_breaks_preservation`). Every
safety theorem is stated in the empty context, which is the only case the
evaluator's contract covers.

The relation is the specification and a function decides one step of it:

```coq
step     : term -> step_result     (* SNext t' | SValue | SStuck s *)
evalFuel : nat -> term -> eval_result   (* Value v | Timeout | Stuck s *)
```

`SStuck`/`Stuck` carry the inner redex to blame, in the same spirit as the
checker's errors. Soundness and completeness connect `step` to the relation,
and determinism falls out as a two-line corollary — the function *is* the proof
that at most one rule applies. A small technical note: the proofs go through
four explicit one-layer unfolding equations (`step_app_eq` etc.) because
`simpl` is too eager on the nested `match`es of the extracted-style definition.

### Safety

`Safety.v` divides type safety into the standard pieces: `progress` (a
well-typed closed term is a value or steps),
`preservation` (via `subst_typing` — the β-case substitutes a *closed*
argument, which under CBN may be a whole unevaluated computation like Ω), and
their iteration down a run:

```coq
Theorem eval_safe : forall n t A, [] ⊢ t ∈ A ->
  (exists v, evalFuel n t = Value v /\ [] ⊢ v ∈ A /\ value v)
  \/ evalFuel n t = Timeout.

Theorem check_eval_contract : forall t A n, check [] t A = Ok tt ->
  (exists v, evalFuel n t = Value v) \/ evalFuel n t = Timeout.
```

The second connects the checker and evaluator: a checked program never returns
`Stuck`. At type ℕ the value is moreover a numeral (`eval_nat_numeral`).
Nothing rules out `Timeout` forever — `omega` is well typed and diverges;
safety promises it diverges politely.

### The runs (frozen in `Tests.v`, printed by `extraction/main.ml`)

| Run | Answer | The point |
|---|---|---|
| `evalFuel 5000 (fact · 3)` | `Value 6` | ~3600 CBN steps; slow but safe |
| `evalFuel 5000 Ω` | `Timeout` | a timeout confirms nothing |
| `evalFuel 2 ((λx. 0) Ω)` | `Value 0` | the flagship: fuel **two** — Ω never touched; CBV would loop |
| `evalFuel 10 (succ (λx. x))` | `Stuck (succ (λx. x))` | unchecked and stuck, with the redex named |
| `evalFuel 10 (slow · 5)` vs `evalFuel 10 Ω` | `Timeout` / `Timeout` | literally the same observation |
| `evalFuel 50 (slow · 5)` | `Value 0` | more fuel separates them — in one direction only |
| `evalFuel 100 ((λx. x x)(λx. x x))` | `Timeout` | untypable yet not stuck: typing is conservative |

Several statements in `Tests.v` are deliberately **not** runs, because no
finite run could establish them. They include `omega_diverges : forall n,
evalFuel n omega = Timeout` (an induction riding the loop Ω --> (λx. x) Ω -->
Ω), its untyped twin `omega_untyped_diverges`, and the totality theorem on the
other side of the same asymmetry,

```coq
Theorem slow_total : forall k, slow · # k -->* # 0.
Corollary slow_total_fuel : forall k, exists fuel, evalFuel fuel (slow · # k) = Value (# 0).
```

proved by induction on `k` and transferred to the evaluator by
`evalFuel_complete` (with `evalFuel_value_sound`, the fuelled function
computes exactly `-->*` — fuel changes what we can see, never what is
there). Two things about that proof are important: it is an
*external* induction about one particular program — typing derives the same
`ℕ ⇒ ℕ` for `slow` and for a diverging term of that type, and records
nothing of it — and it only goes through *strengthened* to any argument
that evaluates to the right numeral (`a -->* # k -> slow · a -->* # 0`),
because under CBN the recursive call receives the unevaluated `tpred a`.
That strengthening is Tait-style computability at ℕ, in the small: what
proved all of System T total survives here for one program whose recursion
happens to consume its input. Divergence is provable but not observable;
totality is provable but not observable; a finite run shows neither. The
run-level half of the asymmetry is `evalFuel_value_mono`: a `Value` verdict
is permanent under more fuel, which is why `Tests.v` freezes
`evalFuel 5000 (slow · 5)` by applying the lemma to the fuel-50 run instead
of re-running.

## Operational approximations and the denotational boundary

This development does not define a CPO library or a compositional ⟦-⟧
interpretation in Rocq. It does mechanize the corresponding operational
observations, including facts that require proofs rather than finite runs:

| Concept | Mechanized anchor |
|---|---|
| the flat domain ℕ⊥ | `Safety.eval_nat_numeral` + `eval_no_stuck`: a checked closed ℕ-program has exactly the fates {⊥, 0, 1, …}; `Stuck` has no point in the domain because typing removed it. The flat *order* is `evalFuel`'s knowledge order (`evalFuel_value_mono` + determinism) |
| the approximation table of `fact` | `Examples.fact_approx k = fact_body^k(Ω)` — Ω plays ⊥. `Tests.fact_approx_diverges` proves, independently of fuel, that row *k* diverges at every input `n ≥ k`. The frozen rows `fact_approx_row0…3` and `fact_approx_agrees` demonstrate selected defined cells below the diagonal and agreement with `fact`; they do not constitute a general factorial-correctness proof for every `n < k` |
| ⟦Ω⟧ = ⊥, at every stage | `omega_diverges` (the limit is ⊥) and `omega_approx_flat` / `omega_loop` (every row is ⊥) |
| adequacy | for a closed `t` with `[] ⊢ t ∈ ℕ`, obs(t) = n iff `t -->* # n`, and obs(t) = ⊥ on divergence. This restriction excludes `Stuck`, which would otherwise be conflated with ⊥. The observation is well-defined by `cbn_deterministic` + `eval_nat_numeral`; its numeral outcomes are detected exactly by `evalFuel` (`evalFuel_value_sound` / `evalFuel_complete`), while ⊥ is only approximated by finite timeouts. A full denotational account would add the compositional ⟦-⟧ interpretation and prove adequacy |
| approximable, not decidable | n ↦ `evalFuel n t` is a computable monotone chain in ℕ⊥ whose limit is the intended denotation; deciding whether the limit stays ⊥ is the halting problem. The `slow`-versus-Ω pair gives the finite observations, while `slow_total` and `omega_diverges` give the two provable but unobservable answers. This motivates the finite abstraction below |
| fuel-bounded NbE | not implemented; as `Subst.v` explains, reduction under binders would be the first part of this development to require genuinely capture-avoiding substitution |

## Finite strictness analysis

The third algorithm never runs the program on a concrete input, and — unlike
`evalFuel` — needs no fuel and no apology: it always terminates, visibly. The
price is fixed in advance: ℕ⊥ collapses to the two-point domain
𝔻 = {⊥ ≤ ⊤} ("surely undefined" ≤ "don't know"), and function types become
finite tables of **monotone** maps — `enum` generates all tables and filters
them through `monotone_tbl`. The filter is load-bearing, not cosmetic: a
non-monotone table like `{⊥↦⊤, ⊤↦⊥}` oscillates under fixpoint iteration
(⊥, ⊤, ⊥, ⊤, …), invalidating the stabilization argument below — frozen as the
negative demo `not_table_oscillates` — and the λ-tabulation would otherwise
feed such tables into bodies, where they can reach an inner `fix`, at higher
order. Nothing is lost by the cut: the abstraction of a concrete function is
always monotone, so a program-computed argument never looks up a dropped
row. 𝔻(ℕ ⇒ ℕ) comes out as exactly the three-element chain
const-⊥ ⊑ id ⊑ const-⊤ (`enum_fun_is_the_three_chain`).

In code (`Strictness.v`):

```coq
Inductive aval : ty -> Type :=
| AN : bool -> aval ℕ
| AF : forall A B, list (aval A * aval B) -> aval (A ⇒ B).

enum  : forall A, list (aval A)  (* the finite domain: monotone tables only *)
abot  : forall A, aval A         (* its least element *)
dsize : ty -> nat           (* iteration budget: counts all maps, so it
                               safely overcounts the monotone carrier *)
aeval : ctx -> aenv -> term -> forall A, aval A
```

`aeval` is a *checking-mode* abstract interpreter — deliberately the same
mode discipline as the checker, and for the same reason: a bare λ does not
carry its domain, and tabulating it means enumerating exactly that domain.
The low-level `analyse t A` assumes that expected type is correct;
`certified_strict` is the guarded public query and first requires
`check [] t (ℕ ⇒ ℕ) = Ok`, so a numeral, Ω at ℕ, or an unbound variable cannot
be certified as a strict function.
The numeric clauses are `Syntax.v`'s design note paying out: `succ♯ = pred♯ =
id`, every numeral ↦ ⊤, and `(ifz c then t else u)♯ = c♯ ⊓ (t♯ ⊔ u♯)`.
Recursion is the finite iteration `a₀ = ⊥, a_{k+1} = F♯(a_k)`, run `dsize A`
times — the computable counterpart of ⊔ fⁿ(⊥), with no convergence test
needed: an ascending chain in the monotone carrier (at most `dsize A`
elements) has stabilized by then. `FiniteOrder.v` factors out the generic join
and finite-iteration theory; `AbstractDomain.v` proves that the concrete
tables satisfy its carrier, order, application, and budget premises;
`Stabilization.v` derives the bounded-iteration fixpoint and least-fixpoint
theorems from the two;
`AnalysisProperties.v` then proves, mutually for synthesis and checking
derivations, that `aeval` stays in that carrier and is monotone in its
abstract environment. Consequently every functional produced at a checked
`fix` satisfies the stabilization theorem's premise. Same iteration shape as
`evalFuel`, opposite epistemic
status: there the domain is infinite and fuel is a confession; here it is
finite and `dsize` is proved sufficient. Extraction stays `Obj.magic`-free — `aval`
is ordinary data, so the demo *prints* abstract functions as tables.

### The verdicts (frozen in `Tests.v`, printed by `extraction/main.ml`)

| Program | `analyse` says | Held to account by |
|---|---|---|
| `λx. succ x` | `{⊥↦⊥, ⊤↦⊤}` — certified strict | `strict_succ_strict_op`: `strict_succ · Ω` provably diverges |
| `λx. 0` | `{⊥↦⊤, ⊤↦⊤}` — unknown | ⊤ is never a verdict of non-strictness |
| `Ω` at ℕ | `⊥` | the analysis computes ⟦Ω⟧♯ — and terminates, in `dsize ℕ = 2` iterations |
| `fact`, `slow` | strict | `fact_strict_op`, `slow_strict_op`: applying either to Ω provably diverges |
| `add` | strict in both arguments | `add_strict_first_op` and the strengthened CBN induction `add_strict_second_computable`; iteration demo: a₀ all-⊥, a₁ already the answer, a₂ = a₁ |
| `mul` | strict in `m` only | `mul_strict_first_op`; but `evalFuel 10 (mul · 0 · Ω) = Value 0`, so the zero branch really does not touch `n` |
| `{⊥↦⊤, ⊤↦⊥}` under `fix` | oscillates: ⊤, ⊥, ⊤, … | the negative demo behind the monotone filter (`not_table_oscillates`, `not_table_excluded`) |
| `λg. fix_ℕ g` at `(ℕ→ℕ)→ℕ` | the abstract lfp operator, tabulated: `{const⊥↦⊥, id↦⊥, const⊤↦⊤}` | higher order works the same and stays finite (`ho_lfp_analysed`) |
| `loop` | `{⊥↦⊥, ⊤↦⊤}` — certified strict | `loop_strict_op`: `loop · Ω` diverges; and `loop · 1 = Value 0`, `loop · 0` diverges (`loop_zero_diverges`) |
| `blind = λx. loop 0` | `{⊥↦⊤, ⊤↦⊤}` — unknown | `blind_strict_op`: `blind · Ω` provably diverges — the function **is** strict |

The last two rows contrast success and blindness one term apart. `loop` is
certified strict, correctly. `blind` is *semantically*
strict — everywhere-diverging, hence sending every argument (⊥ included) to
⊥ by definition — but the abstraction merged `0` with all defined numbers
the moment it was written, so the abstract `ifz` cannot see that `loop ⊤`
takes the diverging branch. The difference between the two verdicts is
exactly the forgotten information: the concrete value `0`. That same loss is
why the analysis terminates — a finite domain is exhaustible, ℕ⊥ is not —
and explains both its termination and its incompleteness.

Operational soundness follows by composing the following proved results.
`Stabilization.v` shows that on the enumerated carrier the budgeted iteration
provably reaches the **least fixpoint** (`afix_approx_is_fixpoint`,
`afix_least`) — the
"terminates because the domain is finite" slogan as a theorem, with
`not_table` marking the exact edge of its hypothesis.
`AnalysisProperties.v` proves carrier closure and environment monotonicity of
`aeval`, so the fixpoint theorem applies to every functional produced by a
checked program. `LogicalRelation.v` supplies the cumulative step-indexed relation,
proves that natural bottom is exactly operational divergence, and proves
`semantic_strict_nat`: a semantically related function whose abstract bottom
row is bottom is operationally strict. `AnalysisSoundness.v` proves the mutual
`logical_fundamental` theorem showing that every checked concrete term is
related to the value computed by `aeval`; `certified_strict_sound` combines
these results for the public Boolean query. Every positive example verdict is also
validated at the instance level by an operational divergence proof, while
`certified_strict` first enforces the `ℕ ⇒ ℕ` typing precondition.

### The implemented pipeline

```
check [] t A = Ok  ⟹  ∀n, evalFuel n t ∈ {Value, Timeout}      (check_eval_contract)
program  ⟶ operational approximation                              (fact_approx, evalFuel)
         ⟶ finite abstraction                                     (analyse, certified_strict)
```

## Representative programs

PCF's only numeric primitives are `tsucc`, `tpred` and `tifz`, so arithmetic is
written with `tfix`: `add`, then `mul`, then

```coq
fact = fix (λf n. ifz n then 1 else mul n (f (pred n)))
```

Nothing in `[] ⊢ fact ∈ ℕ ⇒ ℕ` records that this particular recursion happens to
terminate. The other examples expose the same boundary between typing,
execution, and finite abstraction:

- `cbn_flagship = (λx. 0) Ω` — well typed at ℕ; returns `0` under call-by-name,
  would diverge under call-by-value. The typing derivation is the same either
  way;
- `slow` — a slow but total countdown, indistinguishable from `omega` by any
  finite run of `evalFuel`;
- `loop = fix (λg n. ifz n then g 0 else 0)` — an example of a conservative
  analysis: certified strict, yet `loop 0` diverges;
- `strict_succ = λx. succ x` and `const_zero = λx. 0` — a contrasting pair.
  Both are typable, and typing cannot tell them apart.

Because they are typable in the empty context, they are all closed
(`typable_empty_closed`) — the evaluator's precondition.

## Notation

| Rocq | Conventional notation |
|------|---------|
| `ℕ`, `A ⇒ B` | `ℕ`, `A → B` |
| `λ "x", t` | `λx. t` |
| `t · u` | `t u` |
| `# n` | numeral `n` |
| `ifz c then t else u` | `ifz c then t else u` |
| `tfix A t` | `fix_A t` |
| `t ∷ A` | `(t : A)` |
| `Γ ⊢ t ∈ A` | `Γ ⊢ t : A` |
| `Γ ⊢ t ⇑ A` | `Γ ⊢ t ⇒ A` (synthesis) |
| `Γ ⊢ t ⇓ A` | `Γ ⊢ t ⇐ A` (checking) |
| `<[ x := s ]> t` | `t[s/x]` (substitution) |
| `t --> u`, `t -->* u` | small step, its reflexive-transitive closure |
