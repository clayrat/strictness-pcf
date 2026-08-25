(** * Checker: the bidirectional type checker

    The declarative judgment [Γ ⊢ t ∈ A] is not an algorithm: the
    rule [T_Lam] *guesses* the domain of a λ, so a naive reading of the rules
    would have to invent a type out of nothing, and [lam_type_not_unique] says
    there is no canonical choice to invent.

    The repair is to split the judgment in two, by the direction in which type
    information flows:

        Γ ⊢ t ⇑ A     (synthesis: [A] is an *output*, computed from [t] and [Γ])
        Γ ⊢ t ⇓ A     (checking:  [A] is an *input*, [t] is measured against it)

    The arrows point up and down because ⇒ is already the function type of
    Ty.v and a notation cannot serve both roles.

    Every term former is assigned to exactly one mode:

    - a variable reads its type off the context, a numeral is a ℕ, [succ]/[pred]
      always produce a ℕ, an annotation [(t : A)] and the annotated [fix_A] were
      *given* their type — all of these synthesize;
    - a λ has nothing to synthesize from, so it only checks: against [A ⇒ B] it
      pushes [A] into the context and checks its body against [B]. [ifz] is in
      checking mode for the same reason, one level up: its two branches must
      agree on a type, and the expected type is the only thing that says which.

    The two modes meet in the two places where information changes direction:

    - [I_App] runs the function in synthesis mode and *uses* the domain it
      obtains as the expected type of the argument. This is the whole point of
      the discipline: the argument never has to be guessed at, so the checker
      reports the mismatch exactly at the argument that is wrong, and not at the
      whole application;
    - [C_Switch] is the only rule that can fire anywhere: a term that
      synthesizes [A] also checks against [A]. This is where the decidable
      equality [ty_eqb] of Ty.v is consumed, and it is the only place a
      "expected X, got Y" error can arise.

    Everything below is stated twice: once as the two judgments (a
    specification, still with no algorithm in it), once as the mutually
    recursive [infer]/[check] that decides them. The results:

    - [bidir_sound]: both judgments imply [Γ ⊢ t ∈ A] — the checker never
      accepts an untypable term;
    - [algo_sound] / [algo_complete]: [infer] and [check] decide the two
      judgments exactly (no false positives, no false negatives);
    - [synth_unique]: synthesized types are unique, even though declarative
      typing is not;
    - [check_incomplete]: the converse of soundness *fails* — some declaratively
      typable terms are rejected, and that is by design. The missing annotation
      is exactly what the user has to supply. *)

From Stdlib Require Import String List.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** The two judgments *)

Reserved Notation "Γ '⊢' t '⇑' A" (at level 40, t at level 99, A at level 60).
Reserved Notation "Γ '⊢' t '⇓' A" (at level 40, t at level 99, A at level 60).

Inductive synth : ctx -> term -> ty -> Prop :=
| I_Var : forall Γ x A,
    lookup Γ x = Some A ->
    Γ ⊢ tvar x ⇑ A
| I_Num : forall Γ n,
    Γ ⊢ # n ⇑ ℕ
| I_Succ : forall Γ t,
    Γ ⊢ t ⇓ ℕ ->
    Γ ⊢ tsucc t ⇑ ℕ
| I_Pred : forall Γ t,
    Γ ⊢ t ⇓ ℕ ->
    Γ ⊢ tpred t ⇑ ℕ
(** The rule that pays for the whole discipline: the function is synthesized,
    and its domain [A] — now known — becomes the expected type of the argument.
    Compare [T_App], where [A] appears in two premises and in neither
    conclusion, i.e. has to be guessed. *)
| I_App : forall Γ t u A B,
    Γ ⊢ t ⇑ A ⇒ B ->
    Γ ⊢ u ⇓ A ->
    Γ ⊢ t · u ⇑ B
(** [fix_A] carries its type, so it synthesizes; the operand is checked against
    [A ⇒ A]. Nothing here notices that the recursion may not terminate. *)
| I_Fix : forall Γ t A,
    Γ ⊢ t ⇓ A ⇒ A ->
    Γ ⊢ tfix A t ⇑ A
(** The user's escape hatch: an annotation turns a checkable term into a
    synthesizing one. It is the *only* rule that does so. *)
| I_Ann : forall Γ t A,
    Γ ⊢ t ⇓ A ->
    Γ ⊢ (t ∷ A) ⇑ A

with chk : ctx -> term -> ty -> Prop :=
| C_Lam : forall Γ x t A B,
    ((x, A) :: Γ) ⊢ t ⇓ B ->
    Γ ⊢ (λ x, t) ⇓ A ⇒ B
| C_IfZ : forall Γ c t u A,
    Γ ⊢ c ⇓ ℕ ->
    Γ ⊢ t ⇓ A ->
    Γ ⊢ u ⇓ A ->
    Γ ⊢ (ifz c then t else u) ⇓ A
(** Mode switch. Read backwards, as the algorithm runs it: to check [t] against
    [A], synthesize a type for [t] and compare. The comparison is where
    [ty_eqb] is used and where the "expected/got" error message is produced. *)
| C_Switch : forall Γ t A,
    Γ ⊢ t ⇑ A ->
    Γ ⊢ t ⇓ A

where "Γ '⊢' t '⇑' A" := (synth Γ t A)
and   "Γ '⊢' t '⇓' A" := (chk Γ t A).

#[export] Hint Constructors synth chk : pcf.

Scheme synth_mind := Minimality for synth Sort Prop
  with chk_mind   := Minimality for chk   Sort Prop.
Combined Scheme bidir_ind from synth_mind, chk_mind.

(** ** Soundness against the declarative judgment

    Both modes refine [Γ ⊢ t ∈ A]: erasing the arrows gives a derivation of the
    original judgment. Thus whatever the checker accepts is a real PCF program
    and is covered by the evaluator's safety theorems. *)

Theorem bidir_sound :
  (forall Γ t A, Γ ⊢ t ⇑ A -> Γ ⊢ t ∈ A) /\
  (forall Γ t A, Γ ⊢ t ⇓ A -> Γ ⊢ t ∈ A).
Proof. apply bidir_ind; eauto with pcf. Qed.

Corollary synth_typing : forall Γ t A, Γ ⊢ t ⇑ A -> Γ ⊢ t ∈ A.
Proof. apply bidir_sound. Qed.

Corollary chk_typing : forall Γ t A, Γ ⊢ t ⇓ A -> Γ ⊢ t ∈ A.
Proof. apply bidir_sound. Qed.

(** ** Synthesis is deterministic

    [lam_type_not_unique] says the declarative judgment assigns [λ x, # 0]
    every type of the form [A ⇒ ℕ]. Synthesis has no such freedom: the type is
    read off the term and the context. Note where each rule gets its type from —
    the context ([I_Var]), the syntax ([I_Num], [I_Succ], [I_Pred]), an
    annotation ([I_Fix], [I_Ann]) or a subderivation ([I_App]) — never from
    thin air. That is exactly why λ is missing from the list. *)

Theorem synth_unique : forall Γ t A B, Γ ⊢ t ⇑ A -> Γ ⊢ t ⇑ B -> A = B.
Proof.
  intros Γ t A B H. generalize dependent B.
  induction H; intros C HC; inversion HC; subst; auto.
  - eauto using lookup_unique.
  - assert (E : A ⇒ B = A0 ⇒ C) by auto. now injection E.
Qed.

(** ** Errors

    The checker returns an error rather than a [bool], because *where* it fails
    is an important part of its interface. Each constructor records the offending
    subterm, so a rejected program points at one node of its own syntax tree:

    - [E_Unbound x]         — [x] is not in the context;
    - [E_NoSynth t]         — [t] is a λ or an [ifz] in synthesizing position.
                              An annotation supplies the missing mode switch
                              only when [t] is itself checkable at that type;
    - [E_NotFun t A]        — [t] is applied but synthesized the non-function
                              type [A];
    - [E_LamNotFun t A]     — a λ is checked against the non-function type [A];
    - [E_Mismatch t A B]    — checking [t] expected [A] and synthesis produced
                              [B]. This is the mode switch failing, and [t] is
                              the smallest subterm to blame. *)

Inductive error : Type :=
| E_Unbound   : string -> error
| E_NoSynth   : term -> error
| E_NotFun    : term -> ty -> error
| E_LamNotFun : term -> ty -> error
| E_Mismatch  : term -> ty -> ty -> error.

Inductive result (X : Type) : Type :=
| Ok  : X -> result X
| Err : error -> result X.

Arguments Ok {X} _.
Arguments Err {X} _.

(** Three combinators, so that the two functions below read like the rules and
    not like error plumbing. [switch] is [C_Switch]; [after] is the "having
    checked the operand, synthesize this" shape shared by [I_Succ], [I_Pred],
    [I_Fix] and [I_Ann]; [apply_to] is [I_App]. *)

Definition lookup_ty (G : ctx) (x : string) : result ty :=
  match lookup G x with
  | Some A => Ok A
  | None => Err (E_Unbound x)
  end.

Definition after (r : result unit) (A : ty) : result ty :=
  match r with
  | Ok _ => Ok A
  | Err e => Err e
  end.

Definition switch (t : term) (B : ty) (r : result ty) : result unit :=
  match r with
  | Ok A => if ty_eqb A B then Ok tt else Err (E_Mismatch t B A)
  | Err e => Err e
  end.

Definition apply_to (f : term) (rf : result ty) (karg : ty -> result unit)
  : result ty :=
  match rf with
  | Ok (A ⇒ B) => after (karg A) B
  | Ok ℕ => Err (E_NotFun f ℕ)
  | Err e => Err e
  end.

(** ** The algorithm

    Read [infer] top-down as the
    synthesis rules and [check] as the checking rules: [check] handles the two
    genuinely checkable formers (λ, [ifz]) and sends everything else through
    [switch] — which is [C_Switch] and nothing else.

    Design note. Those last seven branches of [check] look like duplication of
    [infer], and morally they are one line: [check G t B = switch t B
    (infer G t)] for every [t] that is not a λ or an [ifz]. That line cannot be
    *written*, because the guard condition rejects a mutual call [infer G t] on
    the very argument [check] is recursing on; the branches below call [infer]
    only on the strict subterm [f] of an application. The lemma
    [check_switch] recovers the intended equation as a theorem, and every proof
    afterwards uses it instead of the individual branches — so the duplication
    is discharged once and never reasoned about again.

    The duplication is avoidable, but only by moving the mode discipline out of
    the functions and into the datatype; that alternative is written out after
    [check_switch] below. *)

Definition synthesizing (t : term) : bool :=
  match t with
  | tlam _ _ => false
  | tifz _ _ _ => false
  | _ => true
  end.

Fixpoint infer (G : ctx) (t : term) : result ty :=
  match t with
  | tvar x   => lookup_ty G x
  | # _      => Ok ℕ
  | tsucc u  => after (check G u ℕ) ℕ
  | tpred u  => after (check G u ℕ) ℕ
  | f · u    => apply_to f (infer G f) (check G u)
  | tfix A u => after (check G u (A ⇒ A)) A
  | u ∷ A    => after (check G u A) A
  | λ _, _   => Err (E_NoSynth t)
  | ifz _ then _ else _ => Err (E_NoSynth t)
  end

with check (G : ctx) (t : term) (B : ty) : result unit :=
  match t with
  | λ x, u => match B with
              | A ⇒ C => check ((x, A) :: G) u C
              | ℕ => Err (E_LamNotFun t ℕ)
              end
  | ifz c then a else b =>
      match check G c ℕ with
      | Err e => Err e
      | Ok _ => match check G a B with
                | Err e => Err e
                | Ok _ => check G b B
                end
      end
  | tvar x   => switch t B (lookup_ty G x)
  | # _      => switch t B (Ok ℕ)
  | tsucc u  => switch t B (after (check G u ℕ) ℕ)
  | tpred u  => switch t B (after (check G u ℕ) ℕ)
  | f · u    => switch t B (apply_to f (infer G f) (check G u))
  | tfix A u => switch t B (after (check G u (A ⇒ A)) A)
  | u ∷ A    => switch t B (after (check G u A) A)
  end.

(** The equation the definition could not state. *)
Lemma check_switch : forall Γ t B,
  synthesizing t = true -> check Γ t B = switch t B (infer Γ t).
Proof. intros Γ [] B H; simpl in *; try reflexivity; discriminate. Qed.

(** ** Alternative: split the *syntax* instead of the modes

    Everything above puts the two modes into two functions over one datatype.
    The alternative is to put them into the datatype: split raw terms into two
    mutually inductive sorts, checkable [val] and synthesizable [neu], joined by
    the two coercions the rules already use — the mode switch, and the cut.

        val ::= λx. v | # n | succ v | pred v | ifz v then v else v
              | fix v | emb n
        neu ::= x | n v | (v : A)

    Three things fall out at once.

    - **[E_NoSynth] disappears.** A λ in a synthesizing position is no longer a
      term the checker rejects; it is not a term at all, because the head of an
      application must be a [neu]. The error type loses a constructor — and the
      useful localized diagnostic "λx. x in synthesizing position, repaired by
      an annotation" becomes a *parse* error rather than something the
      algorithm reports.

    - **[fix] loses its annotation.** [fix] is a checkable former: to check
      [fix v] against [A], check [v] against [A ⇒ A]. The expected type is
      already there, so [fix_A] becomes plain [fix], and the design decision
      "[fix] is annotated, λ is not" evaporates — the only annotation left in
      the language is the explicit cut. (The Idris development writes this
      former as a binder, [Fix : String -> Val -> Val]; same thing.)

    - **The duplication in [check] goes away.** [check (emb n) B] recurses into
      the *strict* subterm [n], so the guard condition is satisfied with the
      mode switch written once. [check_switch] becomes unnecessary because the
      equation it recovers is the definition.

    A second variation, orthogonal to the first: give λ an annotation of its
    own, as a separate *synthesizing* former,

        neu ::= … | λx:A. n

    Its body is a [neu], not a [val]: a form that synthesizes [A ⇒ B] has
    to get [B] from somewhere,
    and the only source is the body. The payoff is that only the *head* λ of an
    application spine ever carries a type, while every λ in argument position
    stays bare and is checked against the domain. A representative term is

        (λx:(A→A)→(A→A). x) (λx. x) (λx. x)

    with exactly one annotation, on the head. Our [((λx. x) : A) u] carries the
    same information in a cut node instead of on the binder; the [Lan] version
    is what a surface language with `fun (x : A) -> e` actually does.

    Why this development does not do either, in two lines:

    - The raw-syntax motivation weakens. Ill-formed programs were meant to
      *exist* and the checker rejects them; the val/neu split already enforces
      half of the discipline in the datatype, so part of the rejection moves to
      the parser.

    - The evaluator pays for it. The split syntax is not closed under
      substitution: β with
      a λ substituted into head position turns [x w] into [(λy. v) w], which is
      ill-sorted, and repairing it needs a cut — hence a *type* — at every
      substitution. That is precisely what the extrinsic design lets the
      evaluator and analyser avoid. An intrinsically typed implementation can
      instead sidestep this by
      projecting to its intrinsic [Term] the moment checking succeeds
      ([val2Term] / [neu2Term]) and running the evaluator on that instead.

    So the honest accounting is: the split buys one error constructor, one
    annotation and seven duplicated branches, and costs a second syntax, an
    erasure into [term], and soundness restated modulo that erasure. *)

(** ** Inverting the combinators *)

Lemma switch_Ok : forall t B r, switch t B r = Ok tt -> r = Ok B.
Proof.
  intros t B [A|e] H; simpl in H.
  - destruct (ty_eqb_spec A B); [now subst | discriminate].
  - discriminate.
Qed.

Lemma after_Ok : forall r A C, after r A = Ok C -> r = Ok tt /\ A = C.
Proof.
  intros [[]|e] A C H; simpl in H; [now injection H | discriminate].
Qed.

Lemma apply_to_Ok : forall f rf k B,
  apply_to f rf k = Ok B -> exists A, rf = Ok (A ⇒ B) /\ k A = Ok tt.
Proof.
  intros f [[|A C]|e] k B H; simpl in H; try discriminate.
  apply after_Ok in H as [Hk ->]. eauto.
Qed.

(** ** Soundness of the algorithm

    Success is a derivation: the checker has no false positives. Together with
    [bidir_sound], a program the checker accepts is typable, so the evaluator
    will not get it stuck. *)

(** The uniform half of every synthesizing case: once [infer] is known correct
    at [t], [check] is correct at [t] for free, by [check_switch] + [C_Switch].
    This is the proof-level counterpart of the duplication in [check]. *)
Lemma synthesizing_case : forall Γ t,
  synthesizing t = true ->
  (forall A, infer Γ t = Ok A -> Γ ⊢ t ⇑ A) ->
  (forall A, infer Γ t = Ok A -> Γ ⊢ t ⇑ A) /\
  (forall B, check Γ t B = Ok tt -> Γ ⊢ t ⇓ B).
Proof.
  intros Γ t Hs Hi. split; [exact Hi|].
  intros B H. rewrite check_switch in H by exact Hs.
  apply switch_Ok in H. auto using C_Switch.
Qed.

Theorem algo_sound : forall t Γ,
  (forall A, infer Γ t = Ok A -> Γ ⊢ t ⇑ A) /\
  (forall B, check Γ t B = Ok tt -> Γ ⊢ t ⇓ B).
Proof.
  induction t as [ x | x u IHu | f IHf u IHu | n | u IHu | u IHu
                 | c IHc a IHa b IHb | A u IHu | u IHu A ]; intros Γ.
  - (* tvar *)
    apply synthesizing_case; [reflexivity|].
    unfold infer, lookup_ty. destruct (lookup Γ x) eqn:E; intros A H.
    + injection H as <-. now apply I_Var.
    + discriminate.
  - (* tlam: no synthesis; checking pushes the domain into the context *)
    split.
    + intros A H. discriminate.
    + intros [|A B] H; simpl in H.
      * discriminate.
      * apply C_Lam, IHu, H.
  - (* tapp: the mode switch of [I_App] *)
    apply synthesizing_case; [reflexivity|].
    intros B H. simpl in H. apply apply_to_Ok in H as (A & Hf & Hu).
    apply I_App with (A := A); [apply IHf, Hf | apply IHu, Hu].
  - (* tnum *)
    apply synthesizing_case; [reflexivity|].
    intros A H. injection H as <-. apply I_Num.
  - (* tsucc *)
    apply synthesizing_case; [reflexivity|].
    intros A H. simpl in H. apply after_Ok in H as [Hu <-].
    apply I_Succ, IHu, Hu.
  - (* tpred *)
    apply synthesizing_case; [reflexivity|].
    intros A H. simpl in H. apply after_Ok in H as [Hu <-].
    apply I_Pred, IHu, Hu.
  - (* tifz: checkable only, and all three subterms are in checking mode *)
    split.
    + intros A H. discriminate.
    + intros B H. simpl in H.
      destruct (check Γ c ℕ) as [[]|e] eqn:Ec; [|discriminate].
      destruct (check Γ a B) as [[]|e] eqn:Ea; [|discriminate].
      apply C_IfZ; [apply IHc, Ec | apply IHa, Ea | apply IHb, H].
  - (* tfix *)
    apply synthesizing_case; [reflexivity|].
    intros C H. simpl in H. apply after_Ok in H as [Hu <-].
    apply I_Fix, IHu, Hu.
  - (* tann *)
    apply synthesizing_case; [reflexivity|].
    intros C H. simpl in H. apply after_Ok in H as [Hu <-].
    apply I_Ann, IHu, Hu.
Qed.

Corollary infer_sound : forall Γ t A, infer Γ t = Ok A -> Γ ⊢ t ⇑ A.
Proof. intros Γ t A. now apply (algo_sound t Γ). Qed.

Corollary check_sound : forall Γ t A, check Γ t A = Ok tt -> Γ ⊢ t ⇓ A.
Proof. intros Γ t A. now apply (algo_sound t Γ). Qed.

(** ** Completeness for the bidirectional judgments

    No false negatives relative to [synth] and [chk]: whatever either
    bidirectional judgment derives, the corresponding function finds — and
    [infer] finds *the* synthesized type, not merely one. This is not
    completeness for the declarative judgment [has_type]; [check_incomplete]
    below gives a declaratively typable term rejected for lack of an
    annotation. *)

Lemma synth_synthesizing : forall Γ t A, Γ ⊢ t ⇑ A -> synthesizing t = true.
Proof. intros Γ t A H. destruct H; reflexivity. Qed.

Theorem algo_complete :
  (forall Γ t A, Γ ⊢ t ⇑ A -> infer Γ t = Ok A) /\
  (forall Γ t A, Γ ⊢ t ⇓ A -> check Γ t A = Ok tt).
Proof.
  apply bidir_ind; intros; simpl.
  - (* I_Var *) unfold lookup_ty. now rewrite H.
  - (* I_Num *) reflexivity.
  - (* I_Succ *) now rewrite H0.
  - (* I_Pred *) now rewrite H0.
  - (* I_App *) unfold apply_to. rewrite H0. simpl. now rewrite H2.
  - (* I_Fix *) now rewrite H0.
  - (* I_Ann *) now rewrite H0.
  - (* C_Lam *) exact H0.
  - (* C_IfZ *) rewrite H0, H2. exact H4.
  - (* C_Switch *)
    rewrite check_switch by (eapply synth_synthesizing; eauto).
    rewrite H0. simpl. now rewrite ty_eqb_refl.
Qed.

Corollary infer_complete : forall Γ t A, Γ ⊢ t ⇑ A -> infer Γ t = Ok A.
Proof. apply algo_complete. Qed.

Corollary check_complete : forall Γ t A, Γ ⊢ t ⇓ A -> check Γ t A = Ok tt.
Proof. apply algo_complete. Qed.

(** An error is a proof of *un*typability in the corresponding mode: since
    [infer] and [check] are functions, a returned [Err] rules out every
    derivation. This is what makes the error messages trustworthy rather than
    merely informative. *)

Corollary infer_err_sound : forall Γ t e A, infer Γ t = Err e -> ~ (Γ ⊢ t ⇑ A).
Proof. intros Γ t e A H Hd. rewrite (infer_complete _ _ _ Hd) in H. discriminate. Qed.

Corollary check_err_sound : forall Γ t e A, check Γ t A = Err e -> ~ (Γ ⊢ t ⇓ A).
Proof. intros Γ t e A H Hd. rewrite (check_complete _ _ _ Hd) in H. discriminate. Qed.

(** The two judgments are therefore decidable, which is the precise form of
    "the checker terminates": unlike the evaluator, it answers on every input. *)

Corollary synth_dec : forall Γ t, {A | Γ ⊢ t ⇑ A} + {forall A, ~ (Γ ⊢ t ⇑ A)}.
Proof.
  intros Γ t. destruct (infer Γ t) as [A|e] eqn:E.
  - left. exists A. now apply infer_sound.
  - right. intros A. now apply (infer_err_sound _ _ _ _ E).
Defined.

Corollary check_dec : forall Γ t A, {Γ ⊢ t ⇓ A} + {~ (Γ ⊢ t ⇓ A)}.
Proof.
  intros Γ t A. destruct (check Γ t A) as [[]|e] eqn:E.
  - left. now apply check_sound.
  - right. now apply (check_err_sound _ _ _ _ E).
Defined.

(** ** The checker contract

    What the checker accepts is a well-typed — hence, in the empty context,
    closed — program. Divergence is not excluded, and cannot be: [omega]
    passes. *)

Theorem check_typable : forall Γ t A, check Γ t A = Ok tt -> Γ ⊢ t ∈ A.
Proof. intros Γ t A H. apply chk_typing, check_sound, H. Qed.

Theorem infer_typable : forall Γ t A, infer Γ t = Ok A -> Γ ⊢ t ∈ A.
Proof. intros Γ t A H. apply synth_typing, infer_sound, H. Qed.

Corollary check_program : forall t A, check [] t A = Ok tt -> [] ⊢ t ∈ A /\ closed t.
Proof.
  intros t A H. split.
  - now apply check_typable.
  - eapply typable_empty_closed, check_typable, H.
Qed.

(** Contrapositive, and the reason the untyped Ω needs no separate computation
    below: an untypable term is rejected in *both* modes, whatever the checker
    happens to print. *)
Corollary untypable_rejected : forall Γ t A,
  ~ (Γ ⊢ t ∈ A) -> check Γ t A <> Ok tt.
Proof. intros Γ t A H Hc. apply H, check_typable, Hc. Qed.

(** ** Where bidirectionality is strictly weaker

    Soundness has no converse. [(λx. x) 0] is typable by the declarative rules — take
    [A = ℕ] in [T_App] — but the checker has to synthesize a type for the
    function in an application, and a bare λ cannot. The error is
    [E_NoSynth (λ x. x)]: the algorithm points at the λ, which is precisely the
    subterm the user must annotate.

    This is the cost of the discipline and it is a deliberate one: the type is
    demanded exactly where the rules would otherwise have to guess. *)

Definition id_applied : term := (λ "x", tvar "x") · # 0.
Definition id_applied_ann : term := ((λ "x", tvar "x") ∷ ℕ ⇒ ℕ) · # 0.

Example id_applied_typable : [] ⊢ id_applied ∈ ℕ.
Proof. unfold id_applied. typecheck. Qed.

Example id_applied_rejected :
  infer [] id_applied = Err (E_NoSynth (λ "x", tvar "x")).
Proof. reflexivity. Qed.

Theorem check_incomplete : exists t A, [] ⊢ t ∈ A /\ check [] t A <> Ok tt.
Proof.
  exists id_applied, ℕ. split.
  - exact id_applied_typable.
  - unfold id_applied. simpl. discriminate.
Qed.

(** The repair, and the only one available: an annotation, which is what
    [I_Ann] is for. Note that it is *not* available for [delta = λx. x x]
    (Examples.[delta_annotated_untypable]) — there the obstruction is the type
    system, not the mode discipline. *)
Example id_applied_ann_accepted : infer [] id_applied_ann = Ok ℕ.
Proof. reflexivity. Qed.
