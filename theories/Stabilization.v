(** * Stabilization: bounded iteration reaches the abstract fixpoint

    The abstract fixpoint algorithm relies on one fact: the iteration
    [a₀ = ⊥, a_{k+1} = F♯(a_k)] has stabilized after [dsize A] steps.
    AbstractDomain.v proved that the enumerated carrier is a finite
    decidable poset with [aapply] closed and monotone on it; FiniteOrder.v
    proved the representation-independent measure argument ([upper_size]
    counts the carrier elements above a point; a monotone step either fixes
    the point or strictly shrinks the count). This file connects the two
    and exposes the PCF-specific theorems:

    - [afix_approx_is_fixpoint]: for every functional [F] in the enumerated
      (hence monotone) carrier, [afix_approx A F (dsize A)] is a genuine
      fixpoint of [aapply F];
    - [afix_least]: it is the *least* one — the analysis computes lfp(F♯),
      not merely some fixpoint;
    - the hypothesis [In F (enum (A ⇒ A))] is exactly what Tests.v's
      [not_table] lacks: on that non-monotone table the iteration provably
      oscillates, so the carrier hypothesis is necessary.

    This file deliberately stops before operational semantics.
    AnalysisProperties.v proves that [aeval] returns carrier values and is
    monotone, so the fixpoint theorem applies to every [F] a checked program's
    [fix] actually produces; LogicalRelation.v and AnalysisSoundness.v carry
    the result to the evaluator. *)

From Stdlib Require Import String Bool List Arith Lia.
From Equations Require Import Equations.
Import ListNotations.
From PCF Require Import Ty Strictness FiniteOrder.
(** Every fact about the domain itself is re-exported from AbstractDomain:
    importing Stabilization gives the whole abstract-domain theory. *)
From PCF Require Export AbstractDomain.

Open Scope ty_scope.

(** ** The measure: how much room is left above [a] *)

Definition upsize (A : ty) (a : aval A) : nat :=
  upper_size (aval_finite_poset A) a.

Lemma upsize_le : forall A (a : aval A), upsize A a <= dsize A.
Proof.
  intros. eapply Nat.le_trans; [apply upper_size_le | apply enum_le_dsize].
Qed.

Lemma upsize_pos : forall A (a : aval A),
  In a (enum A) -> 1 <= upsize A a.
Proof.
  intros A a Ha. exact (upper_size_pos _ (aval_finite_poset A) _ Ha).
Qed.

(** A strict rise strictly shrinks the room above. *)
Lemma upsize_strict : forall A (a b : aval A),
  In a (enum A) -> In b (enum A) ->
  aleb a b = true -> a <> b ->
  upsize A b < upsize A a.
Proof.
  intros A a b Ha Hb Hab Hne.
  exact (upper_size_strict _ (aval_finite_poset A) _ _ Ha Hb Hab Hne).
Qed.

(** ** Stabilization *)

(** The engine: from any point of the carrier sitting below its own image,
    with [n] at least the room above it, [n] more steps reach a fixpoint.
    A step either already fixes the point or strictly shrinks the room. *)
Lemma chain_stab : forall n A (F : aval (A ⇒ A)) (a : aval A),
  In F (enum (A ⇒ A)) -> In a (enum A) ->
  aleb a (aapply F a) = true ->
  upsize A a <= n ->
  Nat.iter (S n) (aapply F) a = Nat.iter n (aapply F) a.
Proof.
  intros n A F a HF Ha Hrise Hup.
  apply (finite_chain_stab _ (aval_finite_poset A) n (aapply F) a).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - exact Ha.
  - exact Hrise.
  - exact Hup.
Qed.

(** *** The bounded iterate is a fixpoint

    For every functional in the carrier, [dsize A] iterations produce a
    genuine fixpoint. The hypothesis is exactly what [Tests.not_table]
    lacks — on that non-monotone table the iteration provably oscillates —
    so the theorem is sharp. *)

Theorem afix_approx_is_fixpoint : forall A (F : aval (A ⇒ A)),
  In F (enum (A ⇒ A)) ->
  aapply F (afix_approx A F (dsize A)) = afix_approx A F (dsize A).
Proof.
  intros A F HF.
  unfold afix_approx.
  apply (finite_iter_is_fixpoint _ (aval_finite_poset A)
    (aapply F) (abot A) (dsize A)).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - apply abot_enum.
  - apply abot_least.
  - apply enum_le_dsize.
Qed.

(** Once fixed, forever fixed: any budget beyond [dsize A] returns the
    same answer. *)
Corollary afix_stable : forall A (F : aval (A ⇒ A)) k,
  In F (enum (A ⇒ A)) -> dsize A <= k ->
  afix_approx A F k = afix_approx A F (dsize A).
Proof.
  intros A F k HF Hk. induction k as [| k IH].
  - assert (dsize A = 0) by lia. congruence.
  - destruct (Nat.eq_dec (dsize A) (S k)) as [-> | Hne]; [reflexivity |].
    simpl. rewrite IH; [| lia]. apply afix_approx_is_fixpoint, HF.
Qed.

(** The iterates never leave the carrier... *)
Lemma afix_approx_enum : forall A (F : aval (A ⇒ A)) k,
  In F (enum (A ⇒ A)) -> In (afix_approx A F k) (enum A).
Proof.
  intros A F k HF. unfold afix_approx.
  apply (iter_closed _ (aval_finite_poset A) (aapply F) (abot A) k).
  - intros x Hx. apply aapply_enum; assumption.
  - apply abot_enum.
Qed.

(** Pointwise larger functionals have pointwise larger approximants. *)
Lemma afix_approx_mono : forall A (F G : aval (A ⇒ A)),
  In F (enum (A ⇒ A)) -> In G (enum (A ⇒ A)) ->
  aleb F G = true -> forall k,
  aleb (afix_approx A F k) (afix_approx A G k) = true.
Proof.
  intros A F G HF HG HFG k. unfold afix_approx.
  apply (finite_iter_mono _ (aval_finite_poset A)
    (aapply F) (aapply G) (abot A) k).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - intros x Hx. apply aapply_fun_mono; assumption.
  - apply abot_enum.
Qed.

(** *** ...and the answer is the least fixpoint

    Not just *a* fixpoint: anything in the carrier that [F] fixes sits
    above the analysis' answer. The abstract [fix] really is lfp — the
    computable finite shadow of ⊔ fⁿ(⊥), now as a theorem. *)

Theorem afix_least : forall A (F : aval (A ⇒ A)) (b : aval A),
  In F (enum (A ⇒ A)) -> In b (enum A) ->
  aapply F b = b ->
  aleb (afix_approx A F (dsize A)) b = true.
Proof.
  intros A F b HF Hb Hfix. unfold afix_approx.
  apply (finite_iter_least _ (aval_finite_poset A)
    (aapply F) (abot A) (dsize A) b).
  - intros x Hx. apply aapply_enum; assumption.
  - intros x y Hx Hy Hxy. apply aapply_mono; assumption.
  - apply abot_enum.
  - apply abot_least.
  - exact Hb.
  - exact Hfix.
Qed.

(** ** The canonical, proof-facing domain

    The index of [aval A] rules out values of the wrong PCF type; membership
    in [enum A] additionally records the semantic carrier invariant: canonical
    keys, carrier-valued rows, and monotonicity. Proofs live in [Prop], so this
    wrapper erases to the underlying [aval] if it is ever extracted. *)

Record cval (A : ty) : Type := {
  cval_raw : aval A;
  cval_in_enum : In cval_raw (enum A)
}.

Arguments cval_raw {A} _.
Arguments cval_in_enum {A} _.

Definition cbot (A : ty) : cval A.
Proof.
  refine {| cval_raw := abot A; cval_in_enum := abot_enum A |}.
Defined.

Definition capply {A B} (f : cval (A ⇒ B)) (v : cval A) : cval B.
Proof.
  refine {| cval_raw := aapply (cval_raw f) (cval_raw v) |}.
  apply aapply_enum; apply cval_in_enum.
Defined.

Definition cjoin {A} (u v : cval A) : cval A.
Proof.
  refine {| cval_raw := ajoin (cval_raw u) (cval_raw v) |}.
  apply ajoin_enum; apply cval_in_enum.
Defined.

Definition cfix {A} (F : cval (A ⇒ A)) : cval A.
Proof.
  refine {| cval_raw := afix_approx A (cval_raw F) (dsize A) |}.
  apply afix_approx_enum, cval_in_enum.
Defined.

Definition cle {A} (u v : cval A) : Prop :=
  aleb (cval_raw u) (cval_raw v) = true.
