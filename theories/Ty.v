(** * Ty: the types of PCF

    PCF keeps exactly the two type formers System T needs for its running
    examples and drops everything else:

        A, B ::= ℕ | A ⇒ B

    Products, Unit and Bool are gone: none of the three algorithms implemented
    here (bidirectional type checking, the CBN evaluator, and strictness
    analysis) needs them, and every extra base type would add a case to all
    three.

    Unlike System T's [ty] in the NbE development, this [ty] is *not* an index
    of the term datatype. Terms are raw (see Syntax.v) and typing is a separate
    judgment (see Typing.v). Types therefore have to carry their own decidable
    equality: the bidirectional checker compares a synthesized type against an
    expected one at run time, which an intrinsic representation would have done
    silently by unification at elaboration time. *)

From Stdlib Require Import Bool Lia.

Inductive ty : Type :=
| tnat : ty
| tarr : ty -> ty -> ty.

Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.

Notation "'ℕ'" := tnat : ty_scope.
Infix "⇒" := tarr (at level 60, right associativity) : ty_scope.

Open Scope ty_scope.

(** ** Basic structure *)

Lemma tarr_inj : forall A1 A2 B1 B2, A1 ⇒ A2 = B1 ⇒ B2 -> A1 = B1 /\ A2 = B2.
Proof. intros A1 A2 B1 B2 H. injection H. auto. Qed.

Lemma tnat_neq_tarr : forall A B, ℕ <> A ⇒ B.
Proof. discriminate. Qed.

(** ** The obstruction behind the untyped Ω

    [ty_size] exists for exactly one lemma, [tarr_neq_dom]: no simple type
    solves the equation [A = A ⇒ B]. That equation is what the self-application
    [x x] would need — the same [x] used both as a function of domain [A] and as
    its own argument — so this size argument, and nothing about λ-abstraction or
    about recursion, is the real reason [(λx. x x)(λx. x x)] is not a PCF
    program. It is also the reason no type *annotation* can repair it: the
    lemma quantifies over every [A], so there is no type to annotate with.
    See [Examples.delta_untypable]. *)

Fixpoint ty_size (A : ty) : nat :=
  match A with
  | ℕ => 1
  | A1 ⇒ A2 => S (ty_size A1 + ty_size A2)
  end.

Lemma ty_size_pos : forall A, 0 < ty_size A.
Proof. induction A; simpl; lia. Qed.

Lemma tarr_neq_dom : forall A B, A <> A ⇒ B.
Proof.
  intros A B H.
  assert (E : ty_size A = ty_size (A ⇒ B)) by (rewrite <- H; reflexivity).
  simpl in E. pose proof (ty_size_pos B). lia.
Qed.

Lemma tarr_neq_cod : forall A B, B <> A ⇒ B.
Proof.
  intros A B H.
  assert (E : ty_size B = ty_size (A ⇒ B)) by (rewrite <- H; reflexivity).
  simpl in E. pose proof (ty_size_pos A). lia.
Qed.

(** ** Decidable equality

    Both forms are provided: [ty_eq_dec] for proofs and [ty_eqb] for the
    extracted type checker, where a [bool] is what we want to see in the OCaml
    output rather than a sumbool carrying proof terms. *)

Definition ty_eq_dec : forall A B : ty, {A = B} + {A <> B}.
Proof. decide equality. Defined.

Fixpoint ty_eqb (A B : ty) : bool :=
  match A, B with
  | ℕ, ℕ => true
  | A1 ⇒ A2, B1 ⇒ B2 => ty_eqb A1 B1 && ty_eqb A2 B2
  | _, _ => false
  end.

Lemma ty_eqb_refl : forall A, ty_eqb A A = true.
Proof. induction A; simpl; [reflexivity | rewrite IHA1, IHA2; reflexivity]. Qed.

Lemma ty_eqb_eq : forall A B, ty_eqb A B = true -> A = B.
Proof.
  induction A as [| A1 IH1 A2 IH2]; intros [| B1 B2]; simpl; try discriminate.
  - reflexivity.
  - intros H. apply andb_true_iff in H as [H1 H2].
    rewrite (IH1 _ H1), (IH2 _ H2). reflexivity.
Qed.

Lemma ty_eqb_spec : forall A B, reflect (A = B) (ty_eqb A B).
Proof.
  intros A B. destruct (ty_eqb A B) eqn:E; constructor.
  - now apply ty_eqb_eq.
  - intros ->. rewrite ty_eqb_refl in E. discriminate.
Qed.
