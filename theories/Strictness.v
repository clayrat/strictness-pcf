(** * Strictness: a finite abstraction for PCF

    This algorithm reasons about a program *statically* — it never runs it on
    a concrete input — and, unlike
    the evaluator, always terminates. The price of that guarantee is set in
    advance: it forgets everything about a computation except whether it is
    defined.

    ** The domain

    The flat domain ℕ_⊥ is collapsed to the two-point domain of definedness

        𝔻 = { ⊥ ≤ ⊤ }

    (⊥ = "surely undefined", ⊤ = "don't know"), and every function type
    becomes the *finite* set of maps between finite domains:

        𝔻(ℕ)      = {⊥, ⊤}                     — [AN false], [AN true]
        𝔻(A ⇒ B)  = tables from 𝔻(A) to 𝔻(B)   — [AF [...]]

    Finiteness at every type is the entire point: it is what a fixpoint
    iteration can exhaust. In Rocq, [aval A] is indexed so an abstract natural
    cannot be mistaken for a function and table rows carry their domain and
    codomain types. Equations handles the dependent eliminations. Extraction
    erases those indices back to first-order data ([bool]s and association
    lists), with no [Obj.magic], so the demo can *print* a function as its
    table.

    The carrier is cut down to the *monotone* tables — [enum] filters with
    [monotone_tbl] — and this is load-bearing, not cosmetic. A non-monotone
    table like {⊥↦⊤, ⊤↦⊥} oscillates under iteration (⊥, ⊤, ⊥, ⊤, …), so
    the [dsize]-step stabilization argument below would be void for it; and
    the λ-clause of [aeval] feeds *every* enumerated value of the argument
    domain into the body, so at higher order such a table would flow into
    inner [fix]es and poison their iterations. Tests.v freezes the
    oscillation as a negative demo. Excluding non-monotone inputs loses no
    information: the abstraction of any concrete function is monotone, so a
    program-computed argument can never look up the rows we dropped.

    ** The interpreter

    [aeval] is a *checking-mode* abstract interpreter, run against an
    expected type — deliberately the same mode discipline as the checker,
    and for the same reason: a bare λ does not carry its domain, and
    tabulating it means enumerating exactly that domain. This is the one
    sense in which the analysis is type-directed: types are consulted
    precisely where the *domain* 𝔻(A) is type-indexed — tabulating a λ,
    reading an application's argument type off [infer], sizing a [fix]
    iteration. No intrinsic term indices anywhere. The low-level [analyse]
    assumes a well-typed input and expected type; the public Boolean
    [certified_strict] enforces that precondition with the checker before it
    is allowed to certify anything.

    The numeric clauses are the design note of Syntax.v paying out:

        succ♯ = pred♯ = id        every numeral ↦ ⊤
        (ifz c then t else u)♯ = c♯ ⊓ (t♯ ⊔ u♯)

    — the test collapses to a gate, the branches to a join. The join of two
    function tables is pointwise; canonical tables share their key order, so
    it is a zip.

    ** Recursion, finitely

    [fix_A] is interpreted by the finite iteration

        a₀ = ⊥_A,   a_{n+1} = F♯(a_n),   answer: a_{dsize A}

    — the computable shadow of ⊔ fⁿ(⊥). No convergence test is needed:
    an ascending chain in the monotone carrier, which has at most [dsize A]
    elements (an overcount — it bounds *all* maps), has stabilized after
    [dsize A] steps. Stabilization.v proves that for every functional in the
    enumerated carrier this bounded iteration returns a genuine fixpoint
    ([afix_approx_is_fixpoint]) and indeed the least one ([afix_least]) — pure
    finite order theory, no semantics.
    [AnalysisProperties.v] proves that [aeval] only ever builds values inside
    the carrier and is monotone in ordered abstract environments.
    [LogicalRelation.v] defines the step-indexed operational relation, while
    [AnalysisSoundness.v] proves the fundamental theorem connecting checked
    terms to the abstract values computed by [aeval] and derives soundness of
    [certified_strict].
    Contrast [evalFuel]:
    same iteration shape, but there the domain is infinite and fuel is a
    confession; here the domain is finite and [dsize] is proved sufficient.

    ** The contract, in its direct form

    If [f♯(⊥) = ⊥] then [f] is strict — the analysis answers ⊥ only when
    it is sure. ⊤ means *unknown*, compatible with both strictness and
    non-strictness. [certified_strict_sound] in AnalysisSoundness.v proves this
    contract for every accepted first-order function. Tests.v also certifies
    the demo instances operationally: the functions the analysis
    calls strict really do diverge on a diverging argument, and the one it
    is blind about ([blind = λx. loop 0]) really is strict — the blindness
    is the abstraction's, not the analyser's bug. The analysis is
    conservative and decides nothing about halting: it is an external
    algorithm about programs, not a Dialectica-style extraction — a
    well-typed PCF term may diverge, so it is not by itself a total
    realizer of anything. *)

From Stdlib Require Import String Bool List Arith.
From Equations Require Import Equations.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing Checker.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Abstract values *)

Inductive aval : ty -> Type :=
| AN : bool -> aval ℕ                    (* 𝔻(ℕ): [false] = ⊥, [true] = ⊤ *)
| AF : forall A B,
    list (aval A * aval B) -> aval (A ⇒ B). (* 𝔻(A ⇒ B): a finite table *)

Arguments AF {A B} _.

(** [Equations] uses these principles to eliminate indexed values without
    casts leaking into the executable definitions. *)
Derive NoConfusion for ty.
Derive Signature NoConfusion NoConfusionHom for aval.

(** Structural equality, used only to look arguments up in tables. *)
Fixpoint table_eqb {I O : Type}
  (eqI : I -> I -> bool) (eqO : O -> O -> bool)
  (ts us : list (I * O)) : bool :=
  match ts, us with
  | [], [] => true
  | (a1, b1) :: ts', (a2, b2) :: us' =>
      eqI a1 a2 && eqO b1 b2 && table_eqb eqI eqO ts' us'
  | _, _ => false
  end.

Equations aval_eqb {A} (v w : aval A) : bool by struct A :=
aval_eqb (A := ℕ) (AN a) (AN b) := Bool.eqb a b;
aval_eqb (A := A1 ⇒ A2) (AF ts) (AF us) :=
  table_eqb (@aval_eqb A1) (@aval_eqb A2) ts us.

(** ** The finite domain of each type

    [enum A] lists 𝔻(A) as finite *monotone* maps: literally all
    tables, then a monotonicity filter. [abot A] is the least element;
    [dsize A] bounds the cardinality (it counts all maps, so it safely
    overcounts the monotone carrier). All three are structural on the type,
    which is what "the domain stays finite at higher types" amounts to in
    code. *)

Fixpoint all_tables {I O : Type} (ins : list I) (outs : list O)
  : list (list (I * O)) :=
  match ins with
  | [] => [[]]
  | i :: ins' =>
      flat_map (fun o => map (fun tbl => (i, o) :: tbl) (all_tables ins' outs))
               outs
  end.

(** Pointwise order on canonical values of a common type. Rows of canonical
    tables are aligned, so the function case is again a zip. *)
Fixpoint table_leb {I O : Type} (leO : O -> O -> bool)
  (ts us : list (I * O)) : bool :=
  match ts, us with
  | [], [] => true
  | (_, b) :: ts', (_, b') :: us' => leO b b' && table_leb leO ts' us'
  | _, _ => false
  end.

Equations aleb {A} (v w : aval A) : bool by struct A :=
aleb (A := ℕ) (AN a) (AN b) := implb a b;
aleb (A := A1 ⇒ A2) (AF ts) (AF us) :=
  table_leb (@aleb A2) ts us.

(** Comparable inputs must go to comparable outputs. *)
Definition monotone_tbl {A B} (tbl : list (aval A * aval B)) : bool :=
  forallb (fun p =>
    forallb (fun q =>
      if aleb (fst p) (fst q) then aleb (snd p) (snd q) else true) tbl) tbl.

Fixpoint enum (A : ty) : list (aval A) :=
  match A as A0 return list (aval A0) with
  | ℕ => [AN false; AN true]
  | A1 ⇒ A2 => map AF (filter monotone_tbl (all_tables (enum A1) (enum A2)))
  end.

Fixpoint abot (A : ty) : aval A :=
  match A as A0 return aval A0 with
  | ℕ => AN false
  | A1 ⇒ A2 => AF (map (fun i => (i, abot A2)) (enum A1))
  end.

Fixpoint dsize (A : ty) : nat :=
  match A with
  | ℕ => 2
  | A1 ⇒ A2 => Nat.pow (dsize A2) (dsize A1)
  end.

(** ** The operations *)

(** Application is table lookup. The default is unreachable on the canonical
    values the interpreter builds (every argument it ever produces is drawn
    from [enum] of the right type); returning ⊥-ish garbage keeps the
    function total on everything else. *)
Equations aapply {A B} (f : aval (A ⇒ B)) (v : aval A) : aval B :=
aapply (AF tbl) v :=
  match find (fun p => aval_eqb (fst p) v) tbl with
  | Some p => snd p
  | None => abot B
  end.

(** Pointwise join. Canonical tables list their keys in [enum] order, so
    the function case is a zip along matching keys. *)
Fixpoint join_tables {I O : Type} (joinO : O -> O -> O)
  (ts us : list (I * O)) : list (I * O) :=
  match ts, us with
  | (a, b) :: ts', (_, b') :: us' =>
      (a, joinO b b') :: join_tables joinO ts' us'
  | _, _ => ts
  end.

Equations ajoin {A} (v w : aval A) : aval A by struct A :=
ajoin (A := ℕ) (AN a) (AN b) := AN (a || b);
ajoin (A := A1 ⇒ A2) (AF ts) (AF us) :=
  AF (join_tables (@ajoin A2) ts us).

(** Observe the definedness bit of a natural abstract value. Keeping this
    elimination separate gives extraction a uniform Boolean result for the
    impossible function-valued branch erased from the index. *)
Equations an_defined (v : aval ℕ) : bool :=
an_defined (AN b) := b.

(** The k-th abstract approximant of a fixpoint — exposed separately so the
    demo can show the iteration itself, row by row, before quoting its
    stabilized value ([Tests.v]: [add]'s a₀ is all-⊥, a₁ is already
    "strict in both arguments", a₂ = a₁). *)
Definition afix_approx (A : ty) (F : aval (A ⇒ A)) (k : nat) : aval A :=
  Nat.iter k (aapply F) (abot A).

(** ** The interpreter *)

Inductive packed_aval : Type :=
| PackAval : forall A, aval A -> packed_aval.

Arguments PackAval {A} _.

Definition aenv : Type := list (string * packed_aval).

Fixpoint alookup (ρ : aenv) (x : string) : option packed_aval :=
  match ρ with
  | [] => None
  | (y, v) :: ρ' => if String.eqb x y then Some v else alookup ρ' x
  end.

(** Transport an abstract value across a run-time type equality. The proof is
    erased by extraction. *)
Definition cast_aval {A B} (E : A = B) (v : aval A) : aval B :=
  match E with eq_refl => v end.

(** Recover a value at the expected type from the heterogeneous environment.
    A mismatch is possible only for malformed low-level calls to [aeval]. *)
Definition unpack_aval (A : ty) (v : packed_aval) : aval A :=
  match v with
  | @PackAval B w =>
      match ty_eq_dec B A with
      | left E => cast_aval E w
      | right _ => abot A
      end
  end.

(** [aeval Γ ρ t A]: the abstract value of [t] at expected type [A], under
    parallel contexts — [Γ] types the free variables (for [infer] at
    application heads), [ρ] carries their abstract values. Structural on
    [t]; every clause total; the λ-clause is where the finiteness of 𝔻 is
    consumed, one table row per point of the argument's domain — and only
    the *monotone* points, so the values reaching a body (and any [fix]
    inside it) stay inside the carrier the stabilization argument is
    about. *)
Fixpoint aeval (Γ : ctx) (ρ : aenv) (t : term) (A : ty) : aval A :=
  match t with
  | tvar x =>
      match alookup ρ x with
      | Some v => unpack_aval A v
      | None => abot A
      end
  | λ x, u =>
      match A as A0 return aval A0 with
      | A1 ⇒ A2 =>
          AF (map (fun v =>
                     (v, aeval ((x, A1) :: Γ)
                           ((x, PackAval v) :: ρ) u A2))
                  (enum A1))
      | ℕ => abot ℕ
      end
  | f · u =>
      match infer Γ f with
      | Ok (A1 ⇒ B) =>
          match ty_eq_dec B A with
          | left E => cast_aval E
              (aapply (aeval Γ ρ f (A1 ⇒ B)) (aeval Γ ρ u A1))
          | right _ => abot A
          end
      | _ => abot A
      end
  | # _ =>
      match A as A0 return aval A0 with
      | ℕ => AN true                  (* every numeral is just "defined" *)
      | A1 ⇒ A2 => abot (A1 ⇒ A2)
      end
  | tsucc u =>
      match A as A0 return aval A0 with
      | ℕ => aeval Γ ρ u ℕ             (* succ♯ = id *)
      | A1 ⇒ A2 => abot (A1 ⇒ A2)
      end
  | tpred u =>
      match A as A0 return aval A0 with
      | ℕ => aeval Γ ρ u ℕ             (* pred♯ = id *)
      | A1 ⇒ A2 => abot (A1 ⇒ A2)
      end
  | ifz c then u1 else u2 =>             (* c♯ ⊓ (t♯ ⊔ u♯) *)
      if an_defined (aeval Γ ρ c ℕ)
      then ajoin (aeval Γ ρ u1 A) (aeval Γ ρ u2 A)
      else abot A
  | tfix A0 u =>
      match ty_eq_dec A0 A with
      | left E => cast_aval E
          (afix_approx A0 (aeval Γ ρ u (A0 ⇒ A0)) (dsize A0))
      | right _ => abot A
      end
  | u ∷ A0 =>
      match ty_eq_dec A0 A with
      | left E => cast_aval E (aeval Γ ρ u A0)
      | right _ => abot A
      end
  end.

(** ** Public API *)

Definition analyse (t : term) (A : ty) : aval A := aeval [] [] t A.

(** The headline question, for a first-order function: first require [t] to
    check at [ℕ ⇒ ℕ], then ask what [t♯] gives on abstract input ⊥. [true]
    means the analysis *certifies* strictness; [false] covers both an
    ill-typed/wrongly typed input and an inconclusive analysis — it never
    means "non-strict". *)
Definition certified_strict (t : term) : bool :=
  match check [] t (ℕ ⇒ ℕ) with
  | Ok tt => aval_eqb (aapply (analyse t (ℕ ⇒ ℕ)) (AN false)) (AN false)
  | Err _ => false
  end.
