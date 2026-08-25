(** * Tests: executable and operational claims, frozen

    Typing claims live mainly in Examples.v. The machinery used by the type
    checker—type equality, context lookup, and syntactic equality—computes, as
    do the checker, evaluator, and analyser cases below.

    Each test was eyeballed with [Compute] and then frozen as a [reflexivity]
    proof, so it runs in the kernel on every build — including the error
    messages and stuck reports, which are part of the executable interfaces.

    The exceptions are marked loudly: the *divergence* statements
    ([omega_diverges], [omega_untyped_diverges],
    [fact_approx_diverges]) and the *totality* statement ([slow_total]) are
    ∀-quantified over fuel or input and therefore cannot be a run — they are
    inductions, making the limit of finite observation explicit in Rocq. *)

From Stdlib Require Import String List Lia.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing Checker Subst
                        OperationalSemantics Safety Strictness Stabilization
                        AnalysisProperties LogicalRelation AnalysisSoundness
                        Examples.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Type equality

    [ty_eqb] is what the extracted checker will use to compare a synthesized
    type against an expected one; [ty_eqb_spec] (Ty.v) ties it to propositional
    equality. *)

Example ty_eqb_nat : ty_eqb ℕ ℕ = true.
Proof. reflexivity. Qed.

Example ty_eqb_arr : ty_eqb (ℕ ⇒ ℕ) (ℕ ⇒ ℕ) = true.
Proof. reflexivity. Qed.

Example ty_eqb_mismatch : ty_eqb ℕ (ℕ ⇒ ℕ) = false.
Proof. reflexivity. Qed.

Example ty_eqb_arity : ty_eqb (ℕ ⇒ ℕ ⇒ ℕ) ((ℕ ⇒ ℕ) ⇒ ℕ) = false.
Proof. reflexivity. Qed.

(** ** Context lookup

    Shadowing is by leftmost match, with no freshness condition: the inner
    binding wins, and the outer one is invisible rather than illegal. *)

Example lookup_hit : lookup [("x", ℕ); ("y", ℕ ⇒ ℕ)] "y" = Some (ℕ ⇒ ℕ).
Proof. reflexivity. Qed.

Example lookup_miss : lookup [("x", ℕ)] "z" = None.
Proof. reflexivity. Qed.

Example lookup_shadowed : lookup [("x", ℕ); ("x", ℕ ⇒ ℕ)] "x" = Some ℕ.
Proof. reflexivity. Qed.

(** ** Syntactic equality of raw terms

    Available because the syntax is raw: with the intrinsically typed [tm] of
    the System T development, comparing two terms meant heterogeneous equality
    and [inj_pair2_eq_dec]. *)

Example term_eq_same :
  (if term_eq_dec delta delta then true else false) = true.
Proof. reflexivity. Qed.

Example term_eq_diff :
  (if term_eq_dec (λ "x", tvar "x") (λ "y", tvar "y") then true else false)
  = false.
Proof. reflexivity. Qed.

(** ** Free variables

    [tvar "x"] is free in the body of [delta] but not in [delta] itself; the
    binder is the one place where names matter. *)

Example afi_open : afi "x" (tvar "x" · tvar "x").
Proof. now apply afi_app_l, afi_var. Qed.

Example afi_bound : ~ afi "x" delta.
Proof. unfold delta. inversion 1; subst. contradiction. Qed.

(** Every closed example is closed for the structural reason that it is typable
    in the empty context. *)
Example examples_closed :
  closed fact /\ closed omega /\ closed loop /\ closed cbn_flagship.
Proof.
  repeat split;
    eauto using typable_empty_closed, fact_typed, omega_typed, loop_typed,
                cbn_flagship_typed.
Qed.

(** ** The bidirectional checker on representative programs

    Everything here is [reflexivity]: these are runs of the extracted
    algorithm, executed in the kernel rather than in OCaml. Statements that
    quantify over *all* types cannot be single runs and are instead corollaries
    of soundness. *)

(** *** The factorial checks

    And it also *synthesizes*, because its head is the annotated [tfix]. That
    the checker succeeds says nothing about termination; evaluation and
    strictness analysis expose that gap. *)

Example fact_checks : check [] fact (ℕ ⇒ ℕ) = Ok tt.
Proof. reflexivity. Qed.

Example fact_infers : infer [] fact = Ok (ℕ ⇒ ℕ).
Proof. reflexivity. Qed.

Example arith_checks :
  check [] add (ℕ ⇒ ℕ ⇒ ℕ) = Ok tt /\ check [] mul (ℕ ⇒ ℕ ⇒ ℕ) = Ok tt.
Proof. split; reflexivity. Qed.

Example analysis_examples_check :
  check [] loop (ℕ ⇒ ℕ) = Ok tt
  /\ check [] slow (ℕ ⇒ ℕ) = Ok tt
  /\ check [] strict_succ (ℕ ⇒ ℕ) = Ok tt
  /\ check [] const_zero (ℕ ⇒ ℕ) = Ok tt.
Proof. repeat split; reflexivity. Qed.

(** *** The two Ωs

    [omega = fix_ℕ (λx. x)] is accepted, at ℕ, with no complaint — and accepting
    it is *correct*, not a bug in the checker: [infer_typable] turns the run into
    a derivation of [[] ⊢ omega ∈ ℕ]. The evaluator then shows the same term
    diverging. *)

Example omega_infers : infer [] omega = Ok ℕ.
Proof. reflexivity. Qed.

Corollary omega_accepted_is_typed : [] ⊢ omega ∈ ℕ.
Proof. apply infer_typable, omega_infers. Qed.

(** The untyped Ω is rejected, and the checker points at [delta]: a λ where a
    function type had to be *synthesized*. *)
Example omega_untyped_rejected :
  infer [] omega_untyped = Err (E_NoSynth delta).
Proof. reflexivity. Qed.

(** One run only rejects at one type. That no type works is not a computation
    but a corollary of [omega_untyped_untypable] and checker soundness — the
    checker cannot accept an untypable term, whatever it prints. *)
Corollary omega_untyped_rejected_everywhere : forall A,
  check [] omega_untyped A <> Ok tt.
Proof. intros A. apply untypable_rejected, omega_untyped_untypable. Qed.

(** Pushing an expected type into [delta] does not help either, and now the
    error is *inside* the λ: [x] is applied but the context gives it ℕ. This is
    the algorithmic form of the size argument [Ty.tarr_neq_dom]. *)
Example delta_checked_rejected :
  check [] delta (ℕ ⇒ ℕ) = Err (E_NotFun (tvar "x") ℕ).
Proof. reflexivity. Qed.

(** *** λ in a synthesizing position: the error an annotation repairs

    [λx. x] is not ill-typed; it is *unsynthesizable*. Given an expected type it
    checks, and [(λx. x : ℕ ⇒ ℕ)] synthesizes. Contrast [delta] above: there is
    no type to annotate it with (Examples.[delta_annotated_untypable]), so the
    two failures look alike on the surface and are not the same failure. *)

Example id_no_synth :
  infer [] (λ "x", tvar "x") = Err (E_NoSynth (λ "x", tvar "x")).
Proof. reflexivity. Qed.

Example id_checks : check [] (λ "x", tvar "x") (ℕ ⇒ ℕ) = Ok tt.
Proof. reflexivity. Qed.

Example id_ann_infers :
  infer [] ((λ "x", tvar "x") ∷ ℕ ⇒ ℕ) = Ok (ℕ ⇒ ℕ).
Proof. reflexivity. Qed.

(** The same phenomenon on the call-by-name example [(λx. 0) Ω], which is typable
    (Examples.[cbn_flagship_typed]) but not *checkable* — its head is a bare λ
    in synthesizing position. One annotation ([Examples.cbn_flagship_ann]), and
    the whole term synthesizes ℕ while still containing a diverging subterm. *)

Example cbn_flagship_no_synth :
  infer [] cbn_flagship = Err (E_NoSynth (λ "x", # 0)).
Proof. reflexivity. Qed.

Example cbn_flagship_ann_infers : infer [] cbn_flagship_ann = Ok ℕ.
Proof. reflexivity. Qed.

Corollary cbn_flagship_ann_typed : [] ⊢ cbn_flagship_ann ∈ ℕ.
Proof. apply infer_typable, cbn_flagship_ann_infers. Qed.

(** *** [ifz] is the other checkable former

    The checker puts [ifz] in checking mode: the branches must agree on
    a type, and the expected type is what they agree on. The alternative — an
    extra synthesis rule that infers both branches and compares — would work,
    but it would break the invariant that [C_Switch] is the *only* consumer of
    [ty_eqb] and the only source of a mismatch error, and it would still not
    subsume the checking rule (branches that are bare λs synthesize nothing).
    The observable cost is the same as for λ, with the same two repairs: an
    annotation, or an expected type from the outside. *)

Example ifz_no_synth :
  infer [] (ifz # 0 then # 1 else # 2)
  = Err (E_NoSynth (ifz # 0 then # 1 else # 2)).
Proof. reflexivity. Qed.

Example ifz_checks : check [] (ifz # 0 then # 1 else # 2) ℕ = Ok tt.
Proof. reflexivity. Qed.

Example ifz_ann_infers : infer [] ((ifz # 0 then # 1 else # 2) ∷ ℕ) = Ok ℕ.
Proof. reflexivity. Qed.

(** In checking mode the branches may themselves be bare λs — this is what the
    extra synthesis rule could not have covered. *)
Example ifz_lam_branches :
  check [] (ifz # 0 then (λ "x", tvar "x") else strict_succ) (ℕ ⇒ ℕ) = Ok tt.
Proof. reflexivity. Qed.

(** *** Getting stuck, caught statically

    [succ (λx. x)] is another kind of failure: not a loop, not a missing
    annotation, but a numeric primitive handed a function. The checker names the
    λ and the type it was measured against. *)

Example stuck_succ_rejected :
  infer [] stuck_succ = Err (E_LamNotFun (λ "x", tvar "x") ℕ).
Proof. reflexivity. Qed.

(** *** Where a bad argument is reported

    The point of [I_App]: the function is synthesized first, so its domain is
    known *before* the argument is looked at, and the argument is measured
    against it. The error therefore names the argument — [# 3] here, not the
    application, not the function. *)

Definition apply_to_three : term :=
  ((λ "f", tvar "f" · # 0) ∷ (ℕ ⇒ ℕ) ⇒ ℕ) · # 3.

Example wrong_argument :
  infer [] apply_to_three = Err (E_Mismatch (# 3) (ℕ ⇒ ℕ) ℕ).
Proof. reflexivity. Qed.

(** The mismatch the other way round: [fact] where a ℕ was expected. *)
Example wrong_argument_fact :
  infer [] (fact · fact) = Err (E_Mismatch fact ℕ (ℕ ⇒ ℕ)).
Proof. reflexivity. Qed.

(** And the cheapest error of all, the one that needs the context to be a
    lookup by name. *)
Example unbound_variable : infer [] (tvar "y") = Err (E_Unbound "y").
Proof. reflexivity. Qed.

(** *** The checker contract, on a term

    Accepted ⇒ typable ⇒ closed. This is the evaluator's precondition,
    obtained from a run of the checker rather than from a hand-written
    derivation. *)
Example fact_is_a_program : [] ⊢ fact ∈ ℕ ⇒ ℕ /\ closed fact.
Proof. apply check_program, fact_checks. Qed.

(** ** The evaluator on representative programs

    Fuel numbers were found by running [Compute]; the central call-by-name
    example needs exactly two units. *)

(** *** The factorial computes

    ~3600 CBN steps for [3! = 6] — call-by-name re-evaluates duplicated
    arguments, and nothing is shared. The relevant theorem is safety, not
    efficiency. *)

Example fact_runs : evalFuel 5000 (fact · # 3) = Value (# 6).
Proof. reflexivity. Qed.

(** The checker-to-evaluator connection on this program: checked, hence never
    [Stuck] — at any
    fuel, not just the one we ran. *)

Example fact_app_checks : check [] (fact · # 3) ℕ = Ok tt.
Proof. reflexivity. Qed.

Corollary fact_app_never_stuck : forall n s,
  evalFuel n (fact · # 3) <> Stuck s.
Proof.
  intros n s. eapply eval_no_stuck, check_typable, fact_app_checks.
Qed.

(** *** Ω times out — and diverges

    A run can only ever show [Timeout] at one fuel. The ∀-statement below is
    *not* a run: it is a two-line induction riding the loop
    Ω --> (λx. x) · Ω --> Ω. Divergence is provable but no finite run observes
    it; this is the operational content of ⟦Ω⟧ = ⊥. *)

Example omega_timeout : evalFuel 5000 omega = Timeout.
Proof. reflexivity. Qed.

Lemma omega_at_loop : forall A n,
  evalFuel n (omega_at A) = Timeout
  /\ evalFuel n ((λ "x", tvar "x") · omega_at A) = Timeout.
Proof. intros A n. induction n as [| n [IH1 IH2]]; split; simpl; auto. Qed.

Corollary omega_loop : forall n,
  evalFuel n omega = Timeout
  /\ evalFuel n ((λ "x", tvar "x") · omega) = Timeout.
Proof. apply omega_at_loop. Qed.

Theorem omega_at_diverges : forall A, diverges (omega_at A).
Proof. intros A n. apply omega_at_loop. Qed.

Theorem omega_diverges : forall n, evalFuel n omega = Timeout.
Proof. apply omega_at_diverges. Qed.

(** The logical relation packages exactly the same universal observation as
    natural bottom. *)
Corollary omega_related_bottom : semantic_rel (AN false) omega.
Proof.
  apply (proj2 (semantic_nat_bottom_iff omega)).
  unfold diverges. apply omega_diverges.
Qed.

(** *** The flagship: fuel two

    [(λx. 0) Ω] under CBN: one β that throws the argument away, one look to
    confirm a value. The diverging subterm was never touched — under a
    call-by-value rule the same term would sit in the argument forever. The
    annotated variant costs one extra step to strip the annotation. *)

Example flagship_runs : evalFuel 2 cbn_flagship = Value (# 0).
Proof. reflexivity. Qed.

Example flagship_ann_runs : evalFuel 3 cbn_flagship_ann = Value (# 0).
Proof. reflexivity. Qed.

(** *** Stuck, at run time this time

    [succ (λx. x)] is proved untypable and rejected statically. Run
    unchecked, it is the evaluator that reports it — and the report names the
    inner redex, like the checker's errors do. A numeral applied to an
    argument fails the same way. This is exactly what [eval_no_stuck] proves
    cannot happen to a checked program. *)

Example stuck_succ_runs : evalFuel 10 stuck_succ = Stuck stuck_succ.
Proof. reflexivity. Qed.

Example stuck_app_runs : evalFuel 5 (# 0 · # 1) = Stuck (# 0 · # 1).
Proof. reflexivity. Qed.

(** *** The key pair: [slow] and Ω on the same fuel

    At fuel 10 the two runs are *literally equal* observations. More fuel
    separates them — in one direction only: [slow] flips to [Value], and
    [evalFuel_value_mono] says that verdict is now permanent, while no fuel
    flips Ω ([omega_diverges]). Timeout is a fact about our patience, not
    about the program. *)

Example slow_vs_omega :
  evalFuel 10 (slow · # 5) = Timeout /\ evalFuel 10 omega = Timeout.
Proof. split; reflexivity. Qed.

Example slow_terminates : evalFuel 50 (slow · # 5) = Value (# 0).
Proof. reflexivity. Qed.

(** Frozen via the monotonicity lemma, not by re-running: a [Value] verdict
    survives any fuel increase. *)
Example slow_value_persists : evalFuel 5000 (slow · # 5) = Value (# 0).
Proof. apply evalFuel_value_mono with (n := 50); [lia | reflexivity]. Qed.

(** *** [slow] is total — provably, not observably

    The twin of [omega_diverges], on the other side of the asymmetry: no
    finite family of runs shows that [slow] converges on *every* input, but
    an induction does. Two remarks make this proof what it is.

    First, nothing here comes from typing. [⊢ slow ∈ ℕ ⇒ ℕ] and
    [⊢ omega_at (ℕ ⇒ ℕ) ∈ ℕ ⇒ ℕ] are derivations of the same shape; the
    induction below is an *external* argument about one particular program,
    riding the fact that its recursion descends along its input. This is
    the gap between typing and termination, exhibited as a proof obligation:
    totality can be a theorem about a language without general recursion, but
    for PCF it is a per-program effort that [fix] makes unautomatable in
    general.

    Second, the induction does not go through as stated on numerals. Under
    CBN the recursive call receives the *unevaluated* [tpred a], so after
    [k] iterations the argument is a chain of [pred]s, never a numeral.
    The provable statement quantifies over any argument that merely
    *evaluates* to the right numeral —

        a -->* # k  ->  slow · a -->* # 0

    — which is precisely Tait-style computability at type ℕ, in the small.
    The totality proof for all of System T ran on that pattern; here it
    survives for [slow] alone because [slow]'s recursion consumes [k]. *)

(** One pass through the loop, for an arbitrary (unevaluated) argument:
    unfold [fix], feed the body to itself, β. *)
Lemma slow_unfold : forall a,
  slow · a -->* (ifz a then # 0 else slow · tpred a).
Proof.
  intros a.
  eapply multi_step. { apply S_App1, S_Fix. }
  eapply multi_step. { apply S_App1, S_Beta. }
  eapply multi_step. { apply S_Beta. }
  apply multi_refl.
Qed.

Lemma slow_computes : forall k a, a -->* # k -> slow · a -->* # 0.
Proof.
  induction k as [| m IH]; intros a Ha;
    (eapply multi_trans; [apply slow_unfold |]);
    (eapply multi_trans; [apply multi_ifz1, Ha |]).
  - (* the ifz sees 0: done *)
    eapply multi_step. { apply S_IfzZ. } apply multi_refl.
  - (* the ifz sees S m: recurse on the still-unevaluated [tpred a] *)
    eapply multi_step. { apply S_IfzS. }
    apply IH.
    eapply multi_trans. { apply multi_pred1, Ha. }
    eapply multi_step. { apply S_PredN. } apply multi_refl.
Qed.

Theorem slow_total : forall k, slow · # k -->* # 0.
Proof. intros k. eapply slow_computes, multi_refl. Qed.

(** Back on the evaluator, via completeness: for every input *some* fuel
    suffices — stated without ever exhibiting a fuel formula (which would
    be quadratic in [k]: the pred-chains again). *)
Corollary slow_total_fuel : forall k,
  exists fuel, evalFuel fuel (slow · # k) = Value (# 0).
Proof.
  intros k. apply evalFuel_complete; [apply slow_total | apply v_num].
Qed.

(** *** Typing is conservative: the untyped Ω does not get stuck

    δδ β-reduces to itself, so this *untypable* term never actually
    breaks — it spins. [Stuck] catches genuine wrecks like [stuck_succ];
    rejection by the type system is a stronger, static judgment that also
    rules out programs whose only sin is looping in a way no simple type can
    describe. (The converse direction — typed, hence never stuck — is
    [eval_no_stuck].) *)

Example omega_untyped_timeout : evalFuel 100 omega_untyped = Timeout.
Proof. reflexivity. Qed.

Theorem omega_untyped_diverges : forall n, evalFuel n omega_untyped = Timeout.
Proof. induction n as [| n IH]; [reflexivity | exact IH]. Qed.

(** *** Where the closedness precondition earns its keep

    Naive substitution's one failure mode, frozen: substituting an *open*
    term under a binder for its free variable captures it — the constant
    function becomes the identity. No evaluator run can build this (programs are
    closed and reduction never goes under a binder; Subst.v), but the raw
    functions accept any term, so the boundary of the contract is worth one
    frozen witness. *)

Example subst_captures :
  <[ "x" := tvar "y" ]> (λ "y", tvar "x") = (λ "y", tvar "y").
Proof. reflexivity. Qed.

(** And the reason every theorem of Safety.v lives in the empty context:
    with a variable free, preservation is *false* — a well-typed open term
    β-steps by capture to a term of a different type. *)
Example capture_breaks_preservation :
  [("y", ℕ)] ⊢ (λ "x", λ "y", tvar "x") · tvar "y" ∈ (ℕ ⇒ ℕ) ⇒ ℕ
  /\ ((λ "x", λ "y", tvar "x") · tvar "y") --> (λ "y", tvar "y")
  /\ ~ ([("y", ℕ)] ⊢ (λ "y", tvar "y") ∈ (ℕ ⇒ ℕ) ⇒ ℕ).
Proof.
  repeat split.
  - typecheck.
  - apply S_Beta.
  - intros H. apply inv_lam in H as (A & B & E & Hb).
    injection E as <- <-.
    apply inv_var in Hb. discriminate.
Qed.

(** *** Conventions, frozen

    [pred 0 = 0] (the truncated predecessor), and the CBN strictness of the
    primitives: [succ] does drive its operand, so [succ (pred 0)] costs two
    steps before the value shows. *)

Example pred_zero : evalFuel 2 (tpred (# 0)) = Value (# 0).
Proof. reflexivity. Qed.

Example succ_is_strict : evalFuel 3 (tsucc (tpred (# 0))) = Value (# 1).
Proof. reflexivity. Qed.

(** ** Operational approximations to denotational behavior

    This development builds no *denotational* semantics in Rocq—no CPOs,
    continuous functions, or interpretation brackets—but the relevant
    approximation chains have operational counterparts that compute.

    A full denotational account would add exactly two things: the
    compositional definition of ⟦-⟧, and the adequacy claim connecting it
    to the operational side. The operational side itself — the right-hand
    column of adequacy — is complete in this development:

    - for a closed term [t] with [[] ⊢ t ∈ ℕ], obs(t) := n if
      [t -->* # n], and ⊥ otherwise, is *well-defined*: determinism
      ([cbn_deterministic]) gives at most one n, and [eval_nat_numeral] says
      such a program can only finish at a numeral. The restriction matters:
      for an arbitrary raw term, "otherwise" would conflate stuckness with
      divergence;
    - obs is *computably approximable*: [evalFuel_value_sound] and
      [evalFuel_complete] say the fuelled evaluator computes exactly [-->*],
      and [evalFuel_value_mono] makes n ↦ evalFuel n t a monotone chain in
      the flat domain — Timeout reads "still ⊥ at stage n", and a [Value],
      once reached, never changes. ⟦t⟧ is the limit of that chain;
    - the limit itself is the one thing no stage computes: deciding whether
      it stays ⊥ is the halting problem ([slow] versus Ω). The two-point domain
      trades the value of the limit for computability of the question
      "⊥ or not".

    ### The approximation table of [fact]

    [fact_approx k] = [fact_body]^k(Ω) — Ω playing ⊥, legitimately, since
    [omega_at_diverges] supplies the operational content of ⟦Ω⟧ = ⊥.
    [fact_approx_diverges] proves the entire on-and-beyond-diagonal region:
    when [k <= n], row [k] is ⊥ at input [n], for *every* fuel. The concrete
    runs below separately witness a few defined cells below the diagonal;
    they are examples, not a general factorial-correctness theorem. *)

(** The unfolding lemmas retain arbitrary call-by-name arguments.  Their
    closedness premises are exactly what licenses the naive named
    substitution when one beta-step installs an argument beneath a later
    binder. *)
Lemma add_unfold : forall a b, closed a ->
  add · a · b -->*
  (ifz a then b else tsucc (add · tpred a · b)).
Proof.
  intros a b Ha.
  eapply multi_step. { apply S_App1, S_App1, S_Fix. }
  eapply multi_step. { apply S_App1, S_App1, S_Beta. }
  eapply multi_step. { apply S_App1, S_Beta. }
  eapply multi_step. { apply S_Beta. }
  cbn [add]. fold add.
  cbn [String.eqb Ascii.eqb Bool.eqb].
  change (multi
    (<[ "n" := b ]> (ifz a then tvar "n"
      else tsucc ((<[ "m" := a ]> add) · tpred a · tvar "n")))
    (ifz a then b else tsucc (add · tpred a · b))).
  assert (Hadd : closed add) by
    (eapply typable_empty_closed; apply add_typed).
  rewrite (subst_closed add "m" a Hadd).
  simpl. fold add.
  rewrite (subst_closed a "n" b Ha). apply multi_refl.
Qed.

Lemma mul_unfold : forall a b, closed a ->
  mul · a · b -->*
  (ifz a then # 0 else add · b · (mul · tpred a · b)).
Proof.
  intros a b Ha.
  eapply multi_step. { apply S_App1, S_App1, S_Fix. }
  eapply multi_step. { apply S_App1, S_App1, S_Beta. }
  eapply multi_step. { apply S_App1, S_Beta. }
  eapply multi_step. { apply S_Beta. }
  cbn [mul]. fold mul add.
  cbn [String.eqb Ascii.eqb Bool.eqb].
  simpl. fold add mul.
  rewrite (subst_closed a "n" b Ha). apply multi_refl.
Qed.

Lemma fact_approx_unfold : forall k a,
  fact_approx (S k) · a -->*
  (ifz a then # 1 else mul · a · (fact_approx k · tpred a)).
Proof.
  intros k a.
  eapply multi_step. { apply S_App1, S_Beta. }
  eapply multi_step. { apply S_Beta. }
  cbn [fact_approx fact_body]. fold mul fact_approx.
  cbn [String.eqb Ascii.eqb Bool.eqb].
  simpl. fold mul fact_approx.
  assert (HF : closed (fact_approx k)) by
    (eapply typable_empty_closed; apply fact_approx_typed).
  rewrite (subst_closed (fact_approx k) "n" a HF). apply multi_refl.
Qed.

(** Addition is strict in its first argument. Multiplication at a positive
    first argument is therefore strict in its second: after one unfolding it
    passes that argument to the strict position of [add]. *)
Lemma add_strict_left : forall a b,
  closed a -> diverges a -> diverges (add · a · b).
Proof.
  intros a b Ha Hdiv.
  eapply diverges_multi_back. { apply add_unfold, Ha. }
  apply diverges_ifz1, Hdiv.
Qed.

Lemma mul_strict_right : forall m a b,
  closed a -> a -->* # (S m) -> closed b -> diverges b ->
  diverges (mul · a · b).
Proof.
  intros m a b Ha Haval Hb Hdiv.
  eapply diverges_multi_back.
  - eapply multi_trans. { apply mul_unfold, Ha. }
    eapply multi_trans. { apply multi_ifz1, Haval. }
    eapply multi_step. { apply S_IfzS. } apply multi_refl.
  - apply add_strict_left; assumption.
Qed.

(** The induction is generalized from numeral arguments to any closed,
    well-typed argument that computes to that numeral. This is necessary
    under CBN: the recursive call receives [tpred a], not the already-reduced
    predecessor numeral. *)
Theorem fact_approx_diverges_computable : forall k n a,
  [] ⊢ a ∈ ℕ -> a -->* # n -> k <= n ->
  diverges (fact_approx k · a).
Proof.
  induction k as [| k IH]; intros n a Htyped Hrun Hle.
  - simpl. apply diverges_app1, omega_at_diverges.
  - destruct n as [| m]; [lia |].
    assert (Hpred_typed : [] ⊢ tpred a ∈ ℕ) by
      (apply T_Pred; exact Htyped).
    assert (Hpred_run : tpred a -->* # m).
    { eapply multi_trans. { apply multi_pred1, Hrun. }
      eapply multi_step. { apply S_PredN. } apply multi_refl. }
    assert (Hrec : diverges (fact_approx k · tpred a)).
    { apply IH with (n := m); [exact Hpred_typed | exact Hpred_run | lia]. }
    assert (Ha_closed : closed a) by
      (eapply typable_empty_closed; exact Htyped).
    assert (Hrec_closed : closed (fact_approx k · tpred a)) by
      (eapply typable_empty_closed; eapply T_App;
       [apply fact_approx_typed | exact Hpred_typed]).
    eapply diverges_multi_back.
    + eapply multi_trans. { apply fact_approx_unfold. }
      eapply multi_trans. { apply multi_ifz1, Hrun. }
      eapply multi_step. { apply S_IfzS. } apply multi_refl.
    + apply mul_strict_right with (m := m); assumption.
Qed.

(** The promised whole-region theorem: approximation depth and evaluator
    fuel are independent. No finite timeout is being mistaken for a proof of
    divergence. *)
Theorem fact_approx_diverges : forall k n fuel,
  k <= n -> evalFuel fuel (fact_approx k · # n) = Timeout.
Proof.
  intros k n fuel Hle.
  apply (fact_approx_diverges_computable k n (# n));
    [apply T_Num | apply multi_refl | exact Hle].
Qed.

Example fact_approx_row0 :
  evalFuel 5000 (fact_approx 0 · # 0) = Timeout.
Proof. apply fact_approx_diverges. lia. Qed.

Example fact_approx_row1 :
  evalFuel 5000 (fact_approx 1 · # 0) = Value (# 1)
  /\ evalFuel 5000 (fact_approx 1 · # 1) = Timeout.
Proof. split; [reflexivity | apply fact_approx_diverges; lia]. Qed.

Example fact_approx_row2 :
  evalFuel 5000 (fact_approx 2 · # 0) = Value (# 1)
  /\ evalFuel 5000 (fact_approx 2 · # 1) = Value (# 1)
  /\ evalFuel 5000 (fact_approx 2 · # 2) = Timeout.
Proof.
  split; [reflexivity |].
  split; [reflexivity |].
  apply fact_approx_diverges. lia.
Qed.

Example fact_approx_row3 :
  evalFuel 5000 (fact_approx 3 · # 2) = Value (# 2)
  /\ evalFuel 5000 (fact_approx 3 · # 3) = Timeout.
Proof. split; [reflexivity | apply fact_approx_diverges; lia]. Qed.

(** The columns stabilize as the rows grow — and where they have stabilized
    they agree with [fact] itself, which is read as the limit
    ⊔ fⁿ(⊥) of the whole table. *)
Example fact_approx_agrees :
  evalFuel 5000 (fact_approx 4 · # 3) = Value (# 6)
  /\ evalFuel 5000 (fact · # 3) = Value (# 6).
Proof. split; reflexivity. Qed.

(** For Ω the table is ⊥ in every row — [omega]'s body is the identity, so
    its approximants never gain a defined point. This is [omega_loop]'s
    second component, read as a table; the ∀-statement [omega_diverges] is
    then the assertion that the *limit* is still ⊥, which no row shows. *)
Example omega_approx_flat :
  evalFuel 100 ((λ "x", tvar "x") · omega) = Timeout.
Proof. reflexivity. Qed.

(** What is deliberately absent here: any Rocq definition of ⟦-⟧, CPOs, or
    continuity. A fuelled NbE extension that normalized under binders with a
    ⊥-constant could reproduce this table as normal forms rather than pointwise
    runs; it would be the first place this development genuinely needed
    capture-avoiding substitution—see Subst.v's header. *)

(** ** Strictness analysis on representative programs

    The third algorithm's demo table, frozen — abstract *tables* this time,
    not runs: nothing here executes a program on a concrete input. In the
    tables below, [AN false] = ⊥, [AN true] = ⊤ and [AF [...]] is a
    function given pointwise on the two-point domain.

    Alongside each verdict the analysis is *held to account* operationally.
    The direct proofs below remain useful independent regressions for the
    concrete programs, while [certified_strict_sound] supplies the general
    result for every positive certificate. *)

(** *** The headline pair

    [λx. succ x] is certified strict: f♯(⊥) = ⊥. [λx. 0] gets ⊤ — visibly
    non-strict to us, but the abstract answer itself only means "unknown";
    ⊥ is the only verdict the analysis ever commits to. *)

Example strict_succ_analysed :
  analyse strict_succ (ℕ ⇒ ℕ) = AF [(AN false, AN false); (AN true, AN true)].
Proof. reflexivity. Qed.

Example const_zero_analysed :
  analyse const_zero (ℕ ⇒ ℕ) = AF [(AN false, AN true); (AN true, AN true)].
Proof. reflexivity. Qed.

Example headline_verdicts :
  certified_strict strict_succ = true /\ certified_strict const_zero = false.
Proof. split; reflexivity. Qed.

(** A certificate is only issued after the checker accepts the input at [ℕ ⇒ ℕ].
    In particular a closed program of the wrong type and an unbound variable
    cannot be mistaken for strict functions, whatever garbage the low-level
    total [analyse] function would return for them. *)
Example certificate_requires_checked_function :
  certified_strict omega = false
  /\ certified_strict (tvar "unbound") = false.
Proof. split; reflexivity. Qed.

(** The certificate behind the first verdict: [strict_succ] applied to a
    diverging argument diverges — f(⊥) = ⊥, operationally, ∀-quantified
    over fuel like every divergence statement in this file. *)
Lemma succ_omega_loop : forall n,
  evalFuel n (strict_succ · omega) = Timeout
  /\ evalFuel n (tsucc omega) = Timeout
  /\ evalFuel n (tsucc ((λ "x", tvar "x") · omega)) = Timeout.
Proof. induction n as [| n [IH1 [IH2 IH3]]]; repeat split; simpl; auto. Qed.

Theorem strict_succ_strict_op : forall n,
  evalFuel n (strict_succ · omega) = Timeout.
Proof. intros n. apply succ_omega_loop. Qed.

(** *** Ω, abstractly — and the analysis terminates on it

    The analyser computes ⟦Ω⟧♯ = ⊥ in [dsize ℕ = 2] iterations of the
    identity. No concrete run of Ω finishes, and proving ⟦Ω⟧ = ⊥ operationally
    needs an induction; the finite domain turns the corresponding abstract fact
    into a terminating computation. [fact] and [slow] analyse strict. *)

Example omega_analysed : analyse omega ℕ = AN false.
Proof. reflexivity. Qed.

Example fact_analysed :
  analyse fact (ℕ ⇒ ℕ) = AF [(AN false, AN false); (AN true, AN true)].
Proof. reflexivity. Qed.

Example slow_analysed :
  analyse slow (ℕ ⇒ ℕ) = AF [(AN false, AN false); (AN true, AN true)].
Proof. reflexivity. Qed.

Example recursive_verdicts :
  certified_strict fact = true /\ certified_strict slow = true.
Proof. split; reflexivity. Qed.

(** One unfolding exposes the strict [ifz] scrutinee. This gives direct
    operational proofs for both positive verdicts above, independently of the
    general certificate theorem. *)
Lemma fact_unfold : forall a,
  fact · a -->* (ifz a then # 1 else mul · a · (fact · tpred a)).
Proof.
  intros a.
  eapply multi_step. { apply S_App1, S_Fix. }
  eapply multi_step. { apply S_App1, S_Beta. }
  eapply multi_step. { apply S_Beta. }
  cbn [fact_body]. fold mul fact.
  cbn [String.eqb Ascii.eqb Bool.eqb].
  simpl. fold mul fact. apply multi_refl.
Qed.

Theorem fact_strict_op : diverges (fact · omega).
Proof.
  eapply diverges_multi_back. { apply fact_unfold. }
  apply diverges_ifz1. exact omega_diverges.
Qed.

Theorem slow_strict_op : diverges (slow · omega).
Proof.
  eapply diverges_multi_back. { apply slow_unfold. }
  apply diverges_ifz1. exact omega_diverges.
Qed.

(** *** Watching [add]'s fixpoint stabilize

    The iteration a₀ = ⊥, a_{n+1} = F♯(a_n) shown step by step — the
    computable shadow of the approximation chain, on the abstract side
    this time. a₀ is the constant-⊥ table; a₁ already says "strict in
    both arguments"; a₂ = a₁, and the analysis' answer is that fixpoint. *)

Definition addF : aval ((ℕ ⇒ ℕ ⇒ ℕ) ⇒ (ℕ ⇒ ℕ ⇒ ℕ)) :=
  aeval [] [] add_body ((ℕ ⇒ ℕ ⇒ ℕ) ⇒ (ℕ ⇒ ℕ ⇒ ℕ)).

Example add_iteration_start :
  afix_approx (ℕ ⇒ ℕ ⇒ ℕ) addF 0
  = AF [(AN false, AF [(AN false, AN false); (AN true, AN false)]);
        (AN true,  AF [(AN false, AN false); (AN true, AN false)])].
Proof. reflexivity. Qed.

Example add_iteration_step :
  afix_approx (ℕ ⇒ ℕ ⇒ ℕ) addF 1
  = AF [(AN false, AF [(AN false, AN false); (AN true, AN false)]);
        (AN true,  AF [(AN false, AN false); (AN true, AN true)])].
Proof. reflexivity. Qed.

Example add_iteration_stable :
  afix_approx (ℕ ⇒ ℕ ⇒ ℕ) addF 2 = afix_approx (ℕ ⇒ ℕ ⇒ ℕ) addF 1.
Proof. reflexivity. Qed.

Example add_analysed :
  analyse add (ℕ ⇒ ℕ ⇒ ℕ) = afix_approx (ℕ ⇒ ℕ ⇒ ℕ) addF 1.
Proof. reflexivity. Qed.

(** Operationally, [add] is strict in both arguments. The first argument is
    immediate from [add_unfold]. For the second, induction is strengthened to
    an arbitrary typed argument that computes to [m], because CBN passes the
    unevaluated [tpred a] into the recursive call. *)
Theorem add_strict_first_op : forall b,
  diverges (add · omega · b).
Proof.
  intros b. apply add_strict_left.
  - eapply typable_empty_closed, omega_typed.
  - exact omega_diverges.
Qed.

Lemma add_strict_second_computable : forall m a,
  [] ⊢ a ∈ ℕ -> a -->* # m -> diverges (add · a · omega).
Proof.
  induction m as [| m IH]; intros a Htyped Hrun.
  - eapply diverges_multi_back.
    + eapply multi_trans. { apply add_unfold.
                            eapply typable_empty_closed, Htyped. }
      eapply multi_trans. { apply multi_ifz1, Hrun. }
      eapply multi_step. { apply S_IfzZ. } apply multi_refl.
    + exact omega_diverges.
  - assert (Hpred_typed : [] ⊢ tpred a ∈ ℕ) by
      (apply T_Pred; exact Htyped).
    assert (Hpred_run : tpred a -->* # m).
    { eapply multi_trans. { apply multi_pred1, Hrun. }
      eapply multi_step. { apply S_PredN. } apply multi_refl. }
    eapply diverges_multi_back.
    + eapply multi_trans. { apply add_unfold.
                            eapply typable_empty_closed, Htyped. }
      eapply multi_trans. { apply multi_ifz1, Hrun. }
      eapply multi_step. { apply S_IfzS. } apply multi_refl.
    + apply diverges_succ1. apply IH; assumption.
Qed.

Theorem add_strict_second_op : forall m,
  diverges (add · # m · omega).
Proof.
  intros m. apply add_strict_second_computable with (m := m);
    [apply T_Num | apply multi_refl].
Qed.

(** [mul], by contrast, is strict in its first argument only — and that is
    not conservatism, it is the truth: [mul 0 Ω] returns [0] under CBN
    because the zero branch never touches [n]. One frozen run per claim. *)

Example mul_analysed :
  analyse mul (ℕ ⇒ ℕ ⇒ ℕ)
  = AF [(AN false, AF [(AN false, AN false); (AN true, AN false)]);
        (AN true,  AF [(AN false, AN true);  (AN true, AN true)])].
Proof. reflexivity. Qed.

Example mul_nonstrict_witness : evalFuel 10 (mul · # 0 · omega) = Value (# 0).
Proof. reflexivity. Qed.

(** The positive half of [mul_analysed]: an undefined first argument is
    forced by [ifz], regardless of the still-unevaluated second argument. *)
Theorem mul_strict_first_op : forall b,
  diverges (mul · omega · b).
Proof.
  intros b. eapply diverges_multi_back.
  - apply mul_unfold. eapply typable_empty_closed, omega_typed.
  - apply diverges_ifz1. exact omega_diverges.
Qed.

(** *** Why the carrier is the *monotone* tables

    The proof that [dsize A] iterations suffice is an argument about ascending
    chains, and a non-monotone table invalidates it: on
    {⊥↦⊤, ⊤↦⊥} the iteration oscillates forever, and [afix_approx] at
    [dsize ℕ = 2] returns a non-fixpoint. Frozen as a negative demo: *)

Definition not_table : aval (ℕ ⇒ ℕ) :=
  AF [(AN false, AN true); (AN true, AN false)].

Example not_table_oscillates :
  afix_approx ℕ not_table 1 = AN true
  /\ afix_approx ℕ not_table 2 = AN false
  /\ afix_approx ℕ not_table 3 = AN true.
Proof. repeat split; reflexivity. Qed.

(** This is why [enum] filters: no such table is ever enumerated — in
    particular the λ-clause never feeds one into a body, where it could
    reach an inner [fix] — and nothing is lost, since the abstraction of a
    concrete function is always monotone. 𝔻(ℕ ⇒ ℕ) is exactly the
    three-element chain const-⊥ ⊑ id ⊑ const-⊤.

    The positive counterpart is now a theorem, not a slogan: for every
    functional *in* the carrier the budgeted iteration reaches a genuine
    fixpoint, and the least one ([Stabilization.afix_approx_is_fixpoint],
    [Stabilization.afix_least]) — the oscillation above is precisely what
    happens outside its hypothesis. *)

Example not_table_excluded :
  existsb (aval_eqb not_table) (enum (ℕ ⇒ ℕ)) = false.
Proof. reflexivity. Qed.

Example enum_fun_is_the_three_chain :
  enum (ℕ ⇒ ℕ)
  = [AF [(AN false, AN false); (AN true, AN false)];   (* const ⊥ *)
     AF [(AN false, AN false); (AN true, AN true)];    (* id     *)
     AF [(AN false, AN true);  (AN true, AN true)]].   (* const ⊤ *)
Proof. reflexivity. Qed.

(** *** Higher order works the same, and stays finite

    [λg. fix_ℕ g] is the
    abstract least-fixpoint operator tabulated over 𝔻(ℕ ⇒ ℕ): lfp(const-⊥)
    = lfp(id) = ⊥, lfp(const-⊤) = ⊤ — three rows, each an iteration that
    terminated. *)

Example ho_lfp_analysed :
  analyse (λ "g", tfix ℕ (tvar "g")) ((ℕ ⇒ ℕ) ⇒ ℕ)
  = AF [(AF [(AN false, AN false); (AN true, AN false)], AN false);
        (AF [(AN false, AN false); (AN true, AN true)],  AN false);
        (AF [(AN false, AN true);  (AN true, AN true)],  AN true)].
Proof. reflexivity. Qed.

(** *** Conservativity: the double demo on one term

    [loop = fix (λg n. ifz n then g 0 else 0)] itself is certified strict —
    loop♯ is the identity table — and that is *true*: [loop] forces its
    argument ([loop_strict_op] below), returns 0 on nonzero input, and
    diverges on 0.

    But [blind = λx. loop 0] gets ⊤. The function is semantically strict —
    everywhere-diverging, so it sends every argument, ⊥ included, to ⊥ by
    definition ([blind_strict_op]) — yet the two-point domain abstracted
    [0] to ⊤ the moment it was written, and the abstract [ifz] can no
    longer see that [loop ⊤] must take the diverging branch:
    loop♯(⊤) = ⊤. The success and the blindness are one term apart, and
    the difference between them is exactly the information the abstraction
    forgot: the concrete value 0. *)

Example loop_analysed :
  analyse loop (ℕ ⇒ ℕ) = AF [(AN false, AN false); (AN true, AN true)].
Proof. reflexivity. Qed.

Example blind_analysed :
  analyse blind (ℕ ⇒ ℕ) = AF [(AN false, AN true); (AN true, AN true)].
Proof. reflexivity. Qed.

Example conservativity_verdicts :
  certified_strict loop = true /\ certified_strict blind = false.
Proof. split; reflexivity. Qed.

(** The three operational facts that pin the demo down. [loop] really is
    strict; [loop 0] really diverges (so [loop]'s strictness verdict is no
    accident of totality); and [blind] really is strict — the ⊤ above is
    the abstraction's blindness, not a property of the program. *)

Lemma loop_omega_loop : forall n,
  evalFuel n (loop · omega) = Timeout
  /\ evalFuel n
       ((λ "g", λ "n", ifz tvar "n" then tvar "g" · # 0 else # 0)
          · loop · omega) = Timeout
  /\ evalFuel n
       ((λ "n", ifz tvar "n" then loop · # 0 else # 0) · omega) = Timeout
  /\ evalFuel n (ifz omega then loop · # 0 else # 0) = Timeout
  /\ evalFuel n (ifz (λ "x", tvar "x") · omega then loop · # 0 else # 0)
     = Timeout.
Proof.
  induction n as [| n [IH1 [IH2 [IH3 [IH4 IH5]]]]]; repeat split; simpl; auto.
Qed.

Theorem loop_strict_op : forall n, evalFuel n (loop · omega) = Timeout.
Proof. intros n. apply loop_omega_loop. Qed.

Lemma loop0_loop : forall n,
  evalFuel n (loop · # 0) = Timeout
  /\ evalFuel n
       ((λ "g", λ "n", ifz tvar "n" then tvar "g" · # 0 else # 0)
          · loop · # 0) = Timeout
  /\ evalFuel n
       ((λ "n", ifz tvar "n" then loop · # 0 else # 0) · # 0) = Timeout
  /\ evalFuel n (ifz # 0 then loop · # 0 else # 0) = Timeout.
Proof. induction n as [| n [IH1 [IH2 [IH3 IH4]]]]; repeat split; simpl; auto. Qed.

Theorem loop_zero_diverges : forall n, evalFuel n (loop · # 0) = Timeout.
Proof. intros n. apply loop0_loop. Qed.

Example loop_positive_returns : evalFuel 10 (loop · # 1) = Value (# 0).
Proof. reflexivity. Qed.

Theorem blind_strict_op : forall n, evalFuel n (blind · omega) = Timeout.
Proof. destruct n as [| n]; [reflexivity | exact (proj1 (loop0_loop n))]. Qed.

(** *** The general theorem instantiated

    [certified_strict_sound] turns each frozen [certified_strict _ = true]
    verdict above into a ∀-statement — divergence on *every* well-typed
    diverging argument, not only on the Ω of the hand-made loops. The
    [reflexivity] discharges the Boolean premise by running the checker and
    the analyser inside the proof; fixpoint stabilization, analyser properties,
    the step-indexed relation, and the fundamental theorem compose invisibly
    behind it. *)

Corollary strict_succ_strict_sem : forall u,
  [] ⊢ u ∈ ℕ -> diverges u -> diverges (strict_succ · u).
Proof. apply certified_strict_sound. reflexivity. Qed.

Corollary loop_strict_sem : forall u,
  [] ⊢ u ∈ ℕ -> diverges u -> diverges (loop · u).
Proof. apply certified_strict_sound. reflexivity. Qed.

Corollary fact_strict_sem : forall u,
  [] ⊢ u ∈ ℕ -> diverges u -> diverges (fact · u).
Proof. apply certified_strict_sound. reflexivity. Qed.

(** The hand-made certificates above become the Ω-instances of these. *)
Example strict_succ_omega_inst : forall n,
  evalFuel n (strict_succ · omega) = Timeout.
Proof.
  exact (strict_succ_strict_sem omega omega_typed (omega_at_diverges ℕ)).
Qed.

(** And the exact boundary of the theorem, stated by its silence: for
    [blind] the Boolean premise is *false* ([conservativity_verdicts]), so
    the certificate theorem asserts nothing about it — yet [blind] is
    semantically strict ([blind_strict_op] above). The gap between "certified"
    and "true" is
    the information the two-point domain forgot, now visible as the
    difference between a derivable corollary and a hand-made induction. *)

(** *** The complete implemented pipeline

    The three algorithms in one line each, all previously proved or frozen:
    a checked program never gets stuck ([check_eval_contract]); its
    meaning is effectively approximable but its divergence undecidable
    ([fact_approx], [omega_diverges] versus [slow_total]); and the
    finite abstraction trades the answer's precision for an analysis that
    always terminates — every [analyse] above is a [reflexivity], including
    on Ω. What was lost in 𝔻 = {⊥ ≤ ⊤} is exactly what [blind] needed:
    which number the computation was defined *at*. That loss is also why
    the analysis halts — a finite domain is exhaustible, ℕ_⊥ is not. *)

(** The public soundness theorem and all of its dependencies are axiom-free. *)
(** ** Axiom audit

    One [Print Assumptions] per headline theorem of the development, so any
    accidental axiom shows up in the build log. Each must report "Closed
    under the global context". *)

Print Assumptions algo_sound.             (* checker soundness *)
Print Assumptions check_eval_contract.    (* checked programs do not get stuck *)
Print Assumptions cbn_deterministic.      (* deterministic small-step evaluation *)
Print Assumptions slow_total.             (* inductive totality proof *)
Print Assumptions afix_approx_is_fixpoint. (* finite iteration reaches a fixpoint *)
Print Assumptions checked_fix_is_fixpoint. (* the result for checked programs *)
Print Assumptions logical_fundamental.    (* analysis fundamental theorem *)
Print Assumptions certified_strict_sound. (* public certificate soundness *)
