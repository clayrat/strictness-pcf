(** * Operational semantics: call-by-name small steps and the fuelled evaluator

    Everything is stated twice: once as an inductive relation [t --> u] (the
    specification), once as functions

        step     : term -> step_result
        evalFuel : nat -> term -> eval_result

    with soundness and completeness connecting them. From completeness,
    determinism of the relation is a two-line corollary — the function *is*
    the proof that at most one rule applies.

    The evaluation strategy is CALL-BY-NAME. The
    β-rule [S_Beta] substitutes the argument *unevaluated* — there is no
    congruence rule stepping the argument of an application — while the
    numeric primitives are strict: [succ], [pred] and [ifz] each drive their
    numeric operand to a numeral before acting ([S_Succ1]/[S_Pred1]/[S_Ifz1]),
    and the values of type ℕ are exactly the numerals. The flat domain ℕ_⊥ is
    the denotational shadow of this convention.

    The flagship consequence: [(λx. 0) · Ω] converges here (the Ω is
    discarded unevaluated by [S_Beta]), whereas a call-by-value rule
    "evaluate the argument first" would loop on it forever. Same term, same
    typing derivation — the strategy alone decides. [Tests.v] records that the
    term reaches [0] with fuel *two*.

    Fuel. [evalFuel n t] performs at most [n] calls to [step]. It answers
    [Value v] and [Stuck s] with certainty; [Timeout] is *not* an answer
    about [t], only about our patience — the asymmetry made precise by
    [evalFuel_value_mono] (a [Value] verdict survives any fuel increase; no
    such lemma is provable for [Timeout], and Tests.v shows [slow] flipping
    from [Timeout] to [Value] while [omega] never does).

    Denotationally, for a closed ℕ-program,
    n ↦ evalFuel n t is a computable monotone chain in the flat domain ℕ_⊥
    ([Timeout] = "still ⊥ at stage n"), and ⟦t⟧ is its limit. The chain is
    computable at every stage; whether the limit stays ⊥ is the halting
    problem. This file and Safety.v prove the operational facts needed to
    justify that reading; a compositional denotation and its adequacy theorem
    are intentionally outside the mechanized development. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing Subst.

Open Scope string_scope.
Open Scope pcf_scope.

(** ** Values

    Numerals and λ-abstractions, nothing else. In particular an annotated
    term is not a value: [S_Ann] strips the annotation, which by then has
    done its only job — steering the checker. *)

Inductive value : term -> Prop :=
| v_num : forall n, value (# n)
| v_lam : forall x t, value (λ x, t).

#[export] Hint Constructors value : pcf.

(** ** The step relation *)

Reserved Notation "t '-->' u" (at level 70).

Inductive cbn : term -> term -> Prop :=
(** The CBN heart: [u] is substituted as-is, evaluated later if ever. The
    substitution is the naive, non-renaming one — sound because no rule
    below steps under a binder and evaluation starts from closed programs; the full
    argument is Subst.v's header. *)
| S_Beta : forall x t u,
    (λ x, t) · u --> <[ x := u ]> t
| S_App1 : forall t t' u,
    t --> t' ->
    t · u --> t' · u
(** The strict fragment: each primitive first drives its operand to a
    numeral, then computes. [pred 0 = 0], the usual truncated convention. *)
| S_SuccN : forall n,
    tsucc (# n) --> # (S n)
| S_Succ1 : forall t t',
    t --> t' ->
    tsucc t --> tsucc t'
| S_PredN : forall n,
    tpred (# n) --> # (Nat.pred n)
| S_Pred1 : forall t t',
    t --> t' ->
    tpred t --> tpred t'
| S_IfzZ : forall t u,
    (ifz # 0 then t else u) --> t
| S_IfzS : forall n t u,
    (ifz # (S n) then t else u) --> u
| S_Ifz1 : forall c c' t u,
    c --> c' ->
    (ifz c then t else u) --> (ifz c' then t else u)
(** One unconditional unfolding — the whole difference from System T's
    [trec], which consumed a numeral at each unfolding and therefore had to
    stop. Nothing is consumed here, which is exactly why [evalFuel] below
    needs fuel. Denotationally, a run that has fired
    [S_Fix] k times has explored [t]'s self-application to depth k — the
    k-th approximant fᵏ(⊥), which Tests.v realizes
    syntactically by cutting the recursion off with Ω ([fact_approx]). *)
| S_Fix : forall A t,
    tfix A t --> t · tfix A t
| S_Ann : forall t A,
    (t ∷ A) --> t

where "t '-->' u" := (cbn t u).

#[export] Hint Constructors cbn : pcf.

(** ** Multi-step *)

Reserved Notation "t '-->*' u" (at level 70).

Inductive multi : term -> term -> Prop :=
| multi_refl : forall t, t -->* t
| multi_step : forall t u v, t --> u -> u -->* v -> t -->* v

where "t '-->*' u" := (multi t u).

#[export] Hint Constructors multi : pcf.

Lemma multi_trans : forall t u v, t -->* u -> u -->* v -> t -->* v.
Proof. induction 1; eauto with pcf. Qed.

(** Congruences: [-->*] passes through every non-binding context the step
    relation descends into. Used by the termination proofs in Tests.v. *)

Lemma multi_app1 : forall t t' u, t -->* t' -> t · u -->* t' · u.
Proof. induction 1; eauto with pcf. Qed.

Lemma multi_succ1 : forall t t', t -->* t' -> tsucc t -->* tsucc t'.
Proof. induction 1; eauto with pcf. Qed.

Lemma multi_pred1 : forall t t', t -->* t' -> tpred t -->* tpred t'.
Proof. induction 1; eauto with pcf. Qed.

Lemma multi_ifz1 : forall c c' t u,
  c -->* c' -> (ifz c then t else u) -->* (ifz c' then t else u).
Proof. induction 1; eauto with pcf. Qed.

(** ** Normal forms, stuck terms

    A stuck term is a normal form that is not a value: evaluation has stopped
    for a bad reason. [tsucc (λx. x)] is the running example and is proved
    untypable: typing is precisely the
    static exclusion of this run-time fate (Safety.v). *)

Definition normal_form (t : term) : Prop := forall u, ~ (t --> u).
Definition stuck (t : term) : Prop := normal_form t /\ ~ value t.

Lemma value_no_step : forall v, value v -> forall u, ~ (v --> u).
Proof. intros v Hv u Hs. destruct Hv; inversion Hs. Qed.

(** ** The algorithm: one step

    [step] either performs the unique available reduction ([SNext]), reports
    a value ([SValue]), or reports the stuck *sub*term ([SStuck s]) — the
    inner redex to blame, in the same spirit as the checker errors: for
    [tsucc (λx. x) · u] the report is [tsucc (λx. x)], not the whole term. *)

Inductive step_result : Type :=
| SNext  : term -> step_result
| SValue : step_result
| SStuck : term -> step_result.

Fixpoint step (t : term) : step_result :=
  match t with
  | tvar _  => SStuck t
  | λ _, _  => SValue
  | # _     => SValue
  | (λ x, b) · u => SNext (<[ x := u ]> b)
  | f · u =>
      match step f with
      | SNext f' => SNext (f' · u)
      | SValue   => SStuck t          (* a numeral in function position *)
      | SStuck s => SStuck s
      end
  | tsucc (# n) => SNext (# (S n))
  | tsucc u =>
      match step u with
      | SNext u' => SNext (tsucc u')
      | SValue   => SStuck t          (* succ of a λ *)
      | SStuck s => SStuck s
      end
  | tpred (# n) => SNext (# (Nat.pred n))
  | tpred u =>
      match step u with
      | SNext u' => SNext (tpred u')
      | SValue   => SStuck t
      | SStuck s => SStuck s
      end
  | ifz # 0 then a else b => SNext a
  | ifz # (S _) then a else b => SNext b
  | ifz c then a else b =>
      match step c with
      | SNext c' => SNext (ifz c' then a else b)
      | SValue   => SStuck t          (* ifz on a λ *)
      | SStuck s => SStuck s
      end
  | tfix A u => SNext (u · tfix A u)
  | u ∷ A => SNext u
  end.

(** ** [step] agrees with the relation

    Four unfolding equations first: [simpl] is too eager on nested [match]es,
    and these state exactly one layer of [step] each, which is also how one
    would explain the function aloud — "an application steps its head unless
    the head is already a λ". All four are [reflexivity]. *)

Lemma step_app_eq : forall f a,
  step (f · a) =
  match f with
  | λ x, b => SNext (<[ x := a ]> b)
  | _ => match step f with
         | SNext f' => SNext (f' · a)
         | SValue   => SStuck (f · a)
         | SStuck s => SStuck s
         end
  end.
Proof. destruct f; reflexivity. Qed.

Lemma step_succ_eq : forall u,
  step (tsucc u) =
  match u with
  | # n => SNext (# (S n))
  | _ => match step u with
         | SNext u' => SNext (tsucc u')
         | SValue   => SStuck (tsucc u)
         | SStuck s => SStuck s
         end
  end.
Proof. destruct u; reflexivity. Qed.

Lemma step_pred_eq : forall u,
  step (tpred u) =
  match u with
  | # n => SNext (# (Nat.pred n))
  | _ => match step u with
         | SNext u' => SNext (tpred u')
         | SValue   => SStuck (tpred u)
         | SStuck s => SStuck s
         end
  end.
Proof. destruct u; reflexivity. Qed.

Lemma step_ifz_eq : forall c a b,
  step (ifz c then a else b) =
  match c with
  | # 0 => SNext a
  | # (S _) => SNext b
  | _ => match step c with
         | SNext c' => SNext (ifz c' then a else b)
         | SValue   => SStuck (ifz c then a else b)
         | SStuck s => SStuck s
         end
  end.
Proof. destruct c; reflexivity. Qed.

Lemma value_step : forall v, value v -> step v = SValue.
Proof. destruct 1; reflexivity. Qed.

(** The workhorse of the case analyses below: case on one step of the head
    [X] — [destruct ... eqn:] substitutes the outcome into the hypotheses —
    and discharge by [discriminate] every branch it can. *)
Local Ltac head_case X :=
  destruct (step X) eqn:E; try discriminate.

(** Completeness: every derivable step is the one [step] takes. In each
    congruence case the induction hypothesis pins down the head's step and
    rewrites the inner [match]; for a [fix] or annotated head [step] has
    already computed, and the hypothesis pins down the target instead. *)
Lemma step_complete : forall t u, t --> u -> step t = SNext u.
Proof.
  induction 1; try reflexivity;
    [ rewrite step_app_eq | rewrite step_succ_eq
    | rewrite step_pred_eq | rewrite step_ifz_eq ];
    match goal with
    | IH : step ?x = SNext _ |- _ =>
        destruct x; try discriminate;
        first [ now rewrite IH | injection IH as <-; reflexivity ]
    end.
Qed.

(** Soundness of [SNext]: the function only takes derivable steps. *)
Lemma step_next_sound : forall t u, step t = SNext u -> t --> u.
Proof.
  induction t as [ x | x b IHb | f IHf a IHa | n | s IHs | p IHp
                 | c IHc t1 IHt1 t2 IHt2 | A r IHr | r IHr A ];
    intros w H; try discriminate.
  - (* application: split on the head *)
    rewrite step_app_eq in H.
    destruct f as [y | y b | f1 f2 | n | f' | f' | fc ft fe | Af fr | fr Af];
      try discriminate.
    + injection H as <-. apply S_Beta.
    + head_case (f1 · f2). injection H as <-. apply S_App1. apply IHf; reflexivity.
    + head_case (tsucc f'). injection H as <-. apply S_App1. apply IHf; reflexivity.
    + head_case (tpred f'). injection H as <-. apply S_App1. apply IHf; reflexivity.
    + head_case (ifz fc then ft else fe).
      injection H as <-. apply S_App1. apply IHf; reflexivity.
    + injection H as <-. apply S_App1, S_Fix.
    + injection H as <-. apply S_App1, S_Ann.
  - (* succ: split on the operand *)
    rewrite step_succ_eq in H.
    destruct s as [y | y b | s1 s2 | n | s' | s' | sc st se | As sr | sr As];
      try discriminate.
    + head_case (s1 · s2). injection H as <-. apply S_Succ1. apply IHs; reflexivity.
    + injection H as <-. apply S_SuccN.
    + head_case (tsucc s'). injection H as <-. apply S_Succ1. apply IHs; reflexivity.
    + head_case (tpred s'). injection H as <-. apply S_Succ1. apply IHs; reflexivity.
    + head_case (ifz sc then st else se).
      injection H as <-. apply S_Succ1. apply IHs; reflexivity.
    + injection H as <-. apply S_Succ1, S_Fix.
    + injection H as <-. apply S_Succ1, S_Ann.
  - (* pred *)
    rewrite step_pred_eq in H.
    destruct p as [y | y b | p1 p2 | n | p' | p' | pc pt pe | Ap pr | pr Ap];
      try discriminate.
    + head_case (p1 · p2). injection H as <-. apply S_Pred1. apply IHp; reflexivity.
    + injection H as <-. apply S_PredN.
    + head_case (tsucc p'). injection H as <-. apply S_Pred1. apply IHp; reflexivity.
    + head_case (tpred p'). injection H as <-. apply S_Pred1. apply IHp; reflexivity.
    + head_case (ifz pc then pt else pe).
      injection H as <-. apply S_Pred1. apply IHp; reflexivity.
    + injection H as <-. apply S_Pred1, S_Fix.
    + injection H as <-. apply S_Pred1, S_Ann.
  - (* ifz: split on the scrutinee; a numeral splits again on zero *)
    rewrite step_ifz_eq in H.
    destruct c as [y | y b | c1 c2 | n | c' | c' | cc ct ce | Ac cr | cr Ac];
      try discriminate.
    + head_case (c1 · c2). injection H as <-. apply S_Ifz1. apply IHc; reflexivity.
    + destruct n; injection H as <-; [apply S_IfzZ | apply S_IfzS].
    + head_case (tsucc c'). injection H as <-. apply S_Ifz1. apply IHc; reflexivity.
    + head_case (tpred c'). injection H as <-. apply S_Ifz1. apply IHc; reflexivity.
    + head_case (ifz cc then ct else ce).
      injection H as <-. apply S_Ifz1. apply IHc; reflexivity.
    + injection H as <-. apply S_Ifz1, S_Fix.
    + injection H as <-. apply S_Ifz1, S_Ann.
  - injection H as <-. apply S_Fix.
  - injection H as <-. apply S_Ann.
Qed.

(** Soundness of [SValue]: only values are reported as values. *)
Lemma step_value_sound : forall t, step t = SValue -> value t.
Proof.
  destruct t; intros H; auto with pcf; try discriminate.
  - rewrite step_app_eq in H.
    destruct t1 as [y | y b | f1 f2 | n | f' | f' | fc ft fe | Af fr | fr Af];
      try discriminate.
    + head_case (f1 · f2).
    + head_case (tsucc f').
    + head_case (tpred f').
    + head_case (ifz fc then ft else fe).
  - rewrite step_succ_eq in H.
    destruct t as [y | y b | s1 s2 | n | s' | s' | sc st se | As sr | sr As];
      try discriminate.
    + head_case (s1 · s2).
    + head_case (tsucc s').
    + head_case (tpred s').
    + head_case (ifz sc then st else se).
  - rewrite step_pred_eq in H.
    destruct t as [y | y b | p1 p2 | n | p' | p' | pc pt pe | Ap pr | pr Ap];
      try discriminate.
    + head_case (p1 · p2).
    + head_case (tsucc p').
    + head_case (tpred p').
    + head_case (ifz pc then pt else pe).
  - rewrite step_ifz_eq in H.
    destruct t1 as [y | y b | c1 c2 | n | c' | c' | cc ct ce | Ac cr | cr Ac];
      try discriminate.
    + head_case (c1 · c2).
    + destruct n; discriminate.
    + head_case (tsucc c').
    + head_case (tpred c').
    + head_case (ifz cc then ct else ce).
Qed.

(** Soundness of [SStuck] — for free, from the two lemmas above: if [t]
    could step, completeness would have made [step] say so; if it were a
    value, [value_step] would have. *)
Lemma step_stuck_sound : forall t s, step t = SStuck s -> stuck t.
Proof.
  intros t s H. split.
  - intros u Hu. apply step_complete in Hu. congruence.
  - intros Hv. apply value_step in Hv. congruence.
Qed.

(** Determinism, as promised: the relation admits at most one step because a
    *function* computes it. No diamond lemmas, no case bash. *)
Theorem cbn_deterministic : forall t u v, t --> u -> t --> v -> u = v.
Proof.
  intros t u v Hu Hv.
  apply step_complete in Hu. apply step_complete in Hv. congruence.
Qed.

(** ** The evaluator

    [evalFuel n t] iterates [step] at most [n] times and returns one of three
    outcomes: a value, a timeout, or a stuck report. *)

Inductive eval_result : Type :=
| Value   : term -> eval_result
| Timeout : eval_result
| Stuck   : term -> eval_result.

Fixpoint evalFuel (fuel : nat) (t : term) : eval_result :=
  match fuel with
  | 0 => Timeout
  | S fuel' =>
      match step t with
      | SNext t' => evalFuel fuel' t'
      | SValue   => Value t
      | SStuck s => Stuck s
      end
  end.

(** ** What the answers mean *)

(** A [Value] answer is a finished run: the result is reachable and really is
    a value. *)
Lemma evalFuel_value_sound : forall n t v,
  evalFuel n t = Value v -> t -->* v /\ value v.
Proof.
  induction n as [| n IH]; intros t v H; simpl in H; [discriminate |].
  destruct (step t) eqn:E.
  - apply IH in H as [Hm Hv]. eauto using multi_step, step_next_sound.
  - injection H as <-. eauto using multi_refl, step_value_sound.
  - discriminate.
Qed.

(** A [Stuck] answer is a finished run too: some reachable term is genuinely
    stuck ([s] is the inner redex reported for the message). *)
Lemma evalFuel_stuck_sound : forall n t s,
  evalFuel n t = Stuck s -> exists u, t -->* u /\ stuck u.
Proof.
  induction n as [| n IH]; intros t s H; simpl in H; [discriminate |].
  destruct (step t) eqn:E.
  - apply IH in H as (u & Hm & Hu). eauto using multi_step, step_next_sound.
  - discriminate.
  - injection H as <-. eauto using multi_refl, step_stuck_sound.
Qed.

(** Completeness of the evaluator for finished runs: whatever [-->*] can
    finish, some fuel finds. Together with [evalFuel_value_sound] this says
    the fuelled function computes exactly the reflexive-transitive closure —
    fuel changes what we can *see*, never what is *there*. Tests.v uses it
    to state termination of [slow] without exhibiting a fuel formula. *)
Lemma evalFuel_complete : forall t v,
  t -->* v -> value v -> exists n, evalFuel n t = Value v.
Proof.
  induction 1 as [t | t u v Hs Hm IH]; intros Hv.
  - exists 1. simpl. rewrite (value_step _ Hv). reflexivity.
  - destruct (IH Hv) as [n En]. exists (S n). simpl.
    rewrite (step_complete _ _ Hs). exact En.
Qed.

(** The asymmetry of observation, one half of it: a [Value] verdict is
    definitive — more fuel cannot change it. There is no such lemma for
    [Timeout], and there cannot be: [slow] times out on small fuel and
    converges on more, while [omega] times out on all (Tests.v). A finite
    run can confirm termination; it can never confirm divergence. *)
Lemma evalFuel_value_mono : forall n m t v,
  n <= m -> evalFuel n t = Value v -> evalFuel m t = Value v.
Proof.
  induction n as [| n IH]; intros m t v Hle H; simpl in H; [discriminate |].
  destruct m as [| m]; [lia |]. simpl.
  destruct (step t); auto.
  apply IH; [lia | exact H].
Qed.

(** ** Divergence and strict evaluation contexts

    A finite [Timeout] is only lack of evidence.  The universal statement
    below is genuine operational divergence.  The closure lemmas say that
    divergence propagates backwards along reduction and out through the two
    strict contexts needed by the factorial-approximant proof. *)

Definition diverges (t : term) : Prop :=
  forall fuel, evalFuel fuel t = Timeout.

Lemma evalFuel_step : forall n t u,
  t --> u -> evalFuel (S n) t = evalFuel n u.
Proof.
  intros n t u Hstep. simpl.
  rewrite (step_complete _ _ Hstep). reflexivity.
Qed.

Lemma diverges_step_back : forall t u,
  t --> u -> diverges u -> diverges t.
Proof.
  intros t u Hstep Hdiv [| fuel]; [reflexivity |].
  rewrite (evalFuel_step _ _ _ Hstep). apply Hdiv.
Qed.

Lemma diverges_multi_back : forall t u,
  t -->* u -> diverges u -> diverges t.
Proof.
  intros t u Hmulti. induction Hmulti; intros Hdiv.
  - exact Hdiv.
  - eapply diverges_step_back; [exact H | apply IHHmulti, Hdiv].
Qed.

(** A diverging term must always have another step, and that successor still
    diverges.  A [Value] or [Stuck] result at the next evaluator call would
    contradict the universal [Timeout] hypothesis. *)
Lemma diverges_next : forall t,
  diverges t -> exists u, t --> u /\ diverges u.
Proof.
  intros t Hdiv. destruct (step t) as [u | | s] eqn:E.
  - exists u. split; [apply step_next_sound, E |].
    intros n. specialize (Hdiv (S n)).
    change (match step t with
            | SNext t' => evalFuel n t'
            | SValue => Value t
            | SStuck s' => Stuck s'
            end = Timeout) in Hdiv.
    now rewrite E in Hdiv.
  - specialize (Hdiv 1). simpl in Hdiv. rewrite E in Hdiv. discriminate.
  - specialize (Hdiv 1). simpl in Hdiv. rewrite E in Hdiv. discriminate.
Qed.

Lemma diverges_app1 : forall f a,
  diverges f -> diverges (f · a).
Proof.
  intros f a Hdiv fuel. revert f Hdiv.
  induction fuel as [| fuel IH]; intros f Hdiv; [reflexivity |].
  destruct (diverges_next _ Hdiv) as (f' & Hstep & Hdiv').
  rewrite (evalFuel_step fuel (f · a) (f' · a));
    [apply IH, Hdiv' | apply S_App1, Hstep].
Qed.

Lemma diverges_ifz1 : forall c a b,
  diverges c -> diverges (ifz c then a else b).
Proof.
  intros c a b Hdiv fuel. revert c Hdiv.
  induction fuel as [| fuel IH]; intros c Hdiv; [reflexivity |].
  destruct (diverges_next _ Hdiv) as (c' & Hstep & Hdiv').
  rewrite (evalFuel_step fuel (ifz c then a else b)
            (ifz c' then a else b));
    [apply IH, Hdiv' | apply S_Ifz1, Hstep].
Qed.

Lemma diverges_succ1 : forall t,
  diverges t -> diverges (tsucc t).
Proof.
  intros t Hdiv fuel. revert t Hdiv.
  induction fuel as [| fuel IH]; intros t Hdiv; [reflexivity |].
  destruct (diverges_next _ Hdiv) as (t' & Hstep & Hdiv').
  rewrite (evalFuel_step fuel (tsucc t) (tsucc t'));
    [apply IH, Hdiv' | apply S_Succ1, Hstep].
Qed.
