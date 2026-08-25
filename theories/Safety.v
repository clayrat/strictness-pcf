(** * Safety: what typing buys at run time

    A well-typed program neither breaks nor gets stuck as it steps: it can only
    finish with a value or keep going. This property is split into the three
    standard pieces plus the checker-to-evaluator corollary:

    - [progress]:     a well-typed closed term is a value or can step;
    - [preservation]: a step preserves the type (via [subst_typing]);
    - [eval_safe]:    therefore [evalFuel] on a well-typed closed program
                      answers [Value] or [Timeout], never [Stuck] — and a
                      [Value] answer of type ℕ is a numeral;
    - [check_eval_contract]: the connection from checking to evaluation,

          check [] t A = Ok tt  ->  evalFuel n t ∈ { Value, Timeout }.

    What is *not* here matters as much: nothing rules out [Timeout] forever.
    [omega] is well typed and diverges; safety promises it will diverge
    without getting stuck. The step relation is also deterministic
    ([OperationalSemantics.cbn_deterministic]). *)

From Stdlib Require Import String List.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing Subst OperationalSemantics
                        Checker.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Canonical forms

    The value convention, now as lemmas: a *value* of type ℕ is a numeral, a
    value of arrow type is a λ. This is where the choice of [tnum] literals
    pays (Syntax.v's design note): "numeral" is a constructor pattern, not a
    recursively defined predicate. *)

Lemma canonical_nat : forall v,
  [] ⊢ v ∈ ℕ -> value v -> exists n, v = # n.
Proof.
  intros v Ht Hv. destruct Hv; eauto.
  apply inv_lam in Ht as (A & B & Habs & _). discriminate.
Qed.

Lemma canonical_arr : forall v A B,
  [] ⊢ v ∈ A ⇒ B -> value v -> exists x t, v = λ x, t.
Proof.
  intros v A B Ht Hv. destruct Hv; eauto.
  apply inv_num in Ht. discriminate.
Qed.

(** ** Progress

    A well-typed closed term is not stuck: it is a value, or some rule
    applies. The proof uses the inversion lemmas plus canonical forms; note
    which cases produce the step — [fix] and annotations always step, an
    application steps by β exactly when its head has finished evaluating,
    and the strict primitives step inside their operand until a numeral
    appears. *)

Theorem progress : forall t A,
  [] ⊢ t ∈ A -> value t \/ exists u, t --> u.
Proof.
  induction t as [ x | x b _ | f IHf a _ | n | u IHu | u IHu
                 | c IHc t1 _ t2 _ | A0 u _ | u _ A0 ];
    intros A Ht.
  - apply inv_var in Ht. rewrite lookup_nil in Ht. discriminate.
  - left. apply v_lam.
  - right. apply inv_app in Ht as (B & Hf & _).
    destruct (IHf _ Hf) as [Hv | [f' Hs]].
    + destruct (canonical_arr _ _ _ Hf Hv) as (x & b & ->).
      eexists. apply S_Beta.
    + eexists. apply S_App1, Hs.
  - left. apply v_num.
  - right. apply inv_succ in Ht as [_ Hu].
    destruct (IHu _ Hu) as [Hv | [u' Hs]].
    + destruct (canonical_nat _ Hu Hv) as (n & ->). eexists. apply S_SuccN.
    + eexists. apply S_Succ1, Hs.
  - right. apply inv_pred in Ht as [_ Hu].
    destruct (IHu _ Hu) as [Hv | [u' Hs]].
    + destruct (canonical_nat _ Hu Hv) as (n & ->). eexists. apply S_PredN.
    + eexists. apply S_Pred1, Hs.
  - right. apply inv_ifz in Ht as (Hc & _ & _).
    destruct (IHc _ Hc) as [Hv | [c' Hs]].
    + destruct (canonical_nat _ Hc Hv) as (n & ->).
      destruct n; eexists; [apply S_IfzZ | apply S_IfzS].
    + eexists. apply S_Ifz1, Hs.
  - right. eexists. apply S_Fix.
  - right. eexists. apply S_Ann.
Qed.

(** ** Preservation

    Stepping does not change the type. Stated for the empty context because
    that is where [subst_typing] lives — the β-case substitutes the argument,
    which is closed precisely because the whole program is (the CBN twist:
    the argument is substituted *untyped-for-values*, i.e. possibly a whole
    unevaluated computation like Ω, and the lemma does not care). *)

Theorem preservation : forall t u A,
  [] ⊢ t ∈ A -> t --> u -> [] ⊢ u ∈ A.
Proof.
  intros t u A Ht Hs. revert A Ht. induction Hs; intros C Ht.
  - (* β *)
    apply inv_app in Ht as (A & Hf & Ha).
    apply inv_lam in Hf as (A' & B' & Eq & Hb).
    injection Eq as <- <-.
    eapply subst_typing; eassumption.
  - apply inv_app in Ht as (A & Hf & Ha). eauto using has_type.
  - apply inv_succ in Ht as [-> _]. apply T_Num.
  - apply inv_succ in Ht as [-> Hu]. eauto using has_type.
  - apply inv_pred in Ht as [-> _]. apply T_Num.
  - apply inv_pred in Ht as [-> Hu]. eauto using has_type.
  - apply inv_ifz in Ht as (_ & H1 & _). exact H1.
  - apply inv_ifz in Ht as (_ & _ & H2). exact H2.
  - apply inv_ifz in Ht as (Hc & H1 & H2). eauto using has_type.
  - (* fix unfolds to an application of its own body *)
    apply inv_fix in Ht as [-> Hf]. eauto using has_type.
  - apply inv_ann in Ht as [-> Hu]. exact Hu.
Qed.

(** ** The evaluator is safe

    The two theorems above, iterated down a run: a well-typed closed program
    answers [Value] (with a value of the same type) or [Timeout]. [Stuck] is
    unreachable. *)

Theorem eval_safe : forall n t A,
  [] ⊢ t ∈ A ->
  (exists v, evalFuel n t = Value v /\ [] ⊢ v ∈ A /\ value v)
  \/ evalFuel n t = Timeout.
Proof.
  induction n as [| n IH]; intros t A Ht; simpl; [auto |].
  destruct (step t) eqn:E.
  - apply IH. eapply preservation; eauto using step_next_sound.
  - left. eexists. eauto using step_value_sound.
  - exfalso. apply step_stuck_sound in E as [Hnf Hnv].
    destruct (progress _ _ Ht) as [Hv | [u Hs]]; [exact (Hnv Hv) | exact (Hnf _ Hs)].
Qed.

Corollary eval_no_stuck : forall n t A s,
  [] ⊢ t ∈ A -> evalFuel n t <> Stuck s.
Proof.
  intros n t A s Ht Hev.
  destruct (eval_safe n t A Ht) as [(v & Ev & _) | Ev]; congruence.
Qed.

(** At type ℕ the value is a numeral. This corollary and [eval_no_stuck]
    together give an operational account of the flat domain: a *checked*
    closed ℕ-program has exactly two possible fates — a numeral, or running
    forever — and by determinism at most one numeral. ℕ_⊥ = {⊥, 0, 1, …} is
    precisely that set of fates; [Stuck] has no point in the domain because
    typing removed it before the semantics ever looks. The flat order
    (⊥ below everything, numbers incomparable) is [evalFuel]'s knowledge
    order: [Timeout] can later become any numeral, but a numeral never
    becomes another ([evalFuel_value_mono] + determinism). *)
Corollary eval_nat_numeral : forall n t v,
  [] ⊢ t ∈ ℕ -> evalFuel n t = Value v -> exists k, v = # k.
Proof.
  intros n t v Ht Ev.
  destruct (eval_safe n t ℕ Ht) as [(w & Ew & Hw & Hv) | Ew]; try congruence.
  rewrite Ev in Ew. injection Ew as <-. eauto using canonical_nat.
Qed.

(** ** From checking to safe evaluation

    The checker produces a typing derivation, and that derivation feeds the
    safety theorem, ensuring that evaluation never reports [Stuck]. *)

Theorem check_eval_contract : forall t A n,
  check [] t A = Ok tt ->
  (exists v, evalFuel n t = Value v) \/ evalFuel n t = Timeout.
Proof.
  intros t A n Hc. apply check_typable in Hc.
  destruct (eval_safe n t A Hc) as [(v & Ev & _) | Ev]; eauto.
Qed.
