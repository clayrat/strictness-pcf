(** * Extraction of the type checker, evaluator, and analyser to OCaml

    Because the term syntax is extrinsic, [term] becomes an ordinary OCaml
    variant over [string], [int], and [ty], and [infer]/[check] become two
    mutually recursive functions over it, with no [Obj.magic] or residual term
    indices. [step], [evalFuel], and [analyse] are extracted into the same
    artifact. Abstract values erase to a variant over [bool] and lists, so
    abstract functions print as literal tables and the finite domain remains
    visible in the output. With intrinsically typed term syntax, by contrast,
    context and type indices can survive as runtime fields and type-directed
    interpretation may require unsafe casts.

    This is a standalone driver, NOT part of the `make` build (it is not in
    _CoqProject). Regenerate with

        coqc -Q ../theories PCF Extract.v      (run from the extraction/ dir)

    which writes pcf.ml / pcf.mli here.

    The computational entry points are [infer], [check], [subst], [step],
    [evalFuel], [analyse], and [certified_strict], together with the data and
    example programs they traverse. Proofs from the Rocq development live in
    [Prop] and are erased, so the extracted artifact contains exactly the
    executable algorithms. [certified_strict] retains the type check that
    guards its analysis verdict.

    There is deliberately no parser in the verified or extracted code.
    [parser.ml] is a handwritten, unverified OCaml front end whose output is a
    raw [term]; the extracted checker remains the trust boundary for accepting
    that output as a well-typed program. *)

From PCF Require Import Ty Syntax Context Typing Checker Subst
                        OperationalSemantics Safety Strictness Examples.
From Stdlib Require Import String List Extraction.
Import ListNotations.

Extraction Language OCaml.

(** The indices of the intrinsically typed abstract values are proof-time
    information. Erasing the arrow indices keeps the extracted representation
    exactly the first-order [AN | AF] datatype printed by the demo. Rocq's
    safety check is conservative for the nested indexed rows, so it is disabled
    for this declaration; the generated [pcf.ml] is checked by the build
    to contain no [Obj.magic]. *)
Unset Extraction SafeImplicits.
Extraction Implicit AF [A B].

(** Numerals as native ints, so [# 3] prints as [3] rather than as a unary
    chain. Coq-originated values are nonnegative, but the extracted API is
    callable from OCaml with any [int], so the eliminator treats every [n <= 0]
    as zero instead of recursing forever on a negative input. *)
Extract Inductive nat => "int" [ "0" "(fun n -> n + 1)" ]
  "(fun zero succ n -> if n <= 0 then zero () else succ (n - 1))".

(** The Peano operations the algorithms use, as native [int] code:
    [Nat.pred] is the evaluator's truncated predecessor, [Nat.pow] sizes the finite
    domains ([add]/[mul] only occur inside [pow]'s definition). The source
    files import [Arith], so the constants to name are the [PeanoNat]
    aliases. Inlining them also keeps the extracted [Nat] module from
    occupying the names [add] and [mul], which belong to the PCF programs
    ([Nat.iter], driving abstract fixpoint iteration, is the one member
    that remains). *)
Extract Inlined Constant PeanoNat.Nat.pred =>
  "(fun n -> if n <= 0 then 0 else n - 1)".
Extract Inlined Constant PeanoNat.Nat.pow =>
  "(fun b e -> let rec go e = if e <= 0 then 1 else b * go (e - 1) in go e)".
Extract Inlined Constant PeanoNat.Nat.add => "( + )".
Extract Inlined Constant PeanoNat.Nat.mul => "( * )".

(** Variable names as native OCaml strings. [lookup] is the only consumer of
    string equality, and OCaml's structural equality on immutable strings is
    exactly [String.eqb]; inlining it avoids extracting the character-by-
    character recursion. *)
From Stdlib Require Import ExtrOcamlNativeString.
Extract Inlined Constant String.eqb => "(=)".

(** [result] and [option] are ordinary variants and are left alone: the driver
    pattern-matches on [Ok]/[Err] to print localized checker errors. *)

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Example programs

    Representative programs are exported so the driver never has to rebuild
    them. [Examples.v] supplies most; the definitions below exercise
    checker-specific behavior and mirror Tests.v. *)

Definition ex_id : term := λ "x", tvar "x".
Definition ex_id_ann : term := (λ "x", tvar "x") ∷ ℕ ⇒ ℕ.

(** A function of type [(ℕ ⇒ ℕ) ⇒ ℕ] applied to a numeral: the argument, not
    the application, is what the checker blames. *)
Definition ex_apply_to_three : term :=
  ((λ "f", tvar "f" · # 0) ∷ (ℕ ⇒ ℕ) ⇒ ℕ) · # 3.

Set Extraction Output Directory ".".

Extraction "pcf.ml"
  infer check
  ty_eqb lookup
  subst step evalFuel
  aval_eqb enum abot dsize aapply ajoin afix_approx aeval analyse
  certified_strict
  add add_body mul fact omega omega_untyped delta stuck_succ cbn_flagship
  blind
  cbn_flagship_ann loop slow strict_succ const_zero
  ex_id ex_id_ann ex_apply_to_three.
