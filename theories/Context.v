(** * Context: typing contexts as association lists

    With de Bruijn indices a context is a [list ty] and "variable lookup" is
    just indexing. With names it is a [list (string * ty)] and lookup is a
    partial function: [lookup Γ x] can fail, which is precisely the first way
    the type checker can reject a term ("unbound variable").

    Taking the *leftmost* matching binding makes shadowing work with no
    freshness side conditions anywhere: [(x, ℕ) :: (x, ℕ ⇒ ℕ) :: Γ] is a legal
    context in which [x] has type ℕ. This is why the typing judgment can state
    its variable rule as an equation [lookup Γ x = Some A] instead of as an
    inductive membership relation — and the equation is what makes types of
    *variables* unique even though types of terms are not (Typing.v). *)

From Stdlib Require Import String List.
Import ListNotations.
From PCF Require Import Ty.

Definition ctx : Type := list (string * ty).

(** The context binder is spelled [G] in the *computational* definitions — here
    and in Checker.v — and [Γ] everywhere else. Coq extracts the Unicode binder
    name [Γ] as the identifier [_UU0393_], so the executable definitions use
    [G] to keep the generated OCaml readable. Statements and proofs, being
    erased, retain the conventional mathematical name. *)

Fixpoint lookup (G : ctx) (x : string) : option ty :=
  match G with
  | [] => None
  | (y, A) :: G' => if String.eqb x y then Some A else lookup G' x
  end.

Lemma lookup_nil : forall x, lookup [] x = None.
Proof. reflexivity. Qed.

Lemma lookup_eq : forall Γ x A, lookup ((x, A) :: Γ) x = Some A.
Proof. intros. simpl. now rewrite String.eqb_refl. Qed.

Lemma lookup_neq : forall Γ x y A, x <> y -> lookup ((y, A) :: Γ) x = lookup Γ x.
Proof.
  intros Γ x y A H. simpl.
  destruct (String.eqb_spec x y); [contradiction | reflexivity].
Qed.

(** Uniqueness: [lookup] is a function, so a variable has at most one type in a
    given context. This tiny fact carries the whole untypability argument for
    the untyped Ω — in [x x] both occurrences must get *the same* [A] from the
    context. *)
Lemma lookup_unique : forall Γ x A B,
  lookup Γ x = Some A -> lookup Γ x = Some B -> A = B.
Proof. intros Γ x A B H1 H2. rewrite H1 in H2. now injection H2. Qed.

(** ** Context inclusion

    The named analogue of a de Bruijn order-preserving embedding, and the form
    in which weakening is stated in Typing.v: [Γ ⊆ Δ] says every binding
    *visible* in [Γ] is visible with the same type in [Δ]. Working with the
    visible-bindings relation rather than with list prefixes is what lets
    [incl_ext] hold with no freshness condition — the new binding shadows
    whatever [x] used to mean on both sides. *)

Definition ctx_incl (Γ Δ : ctx) : Prop :=
  forall x A, lookup Γ x = Some A -> lookup Δ x = Some A.

Notation "Γ ⊆ Δ" := (ctx_incl Γ Δ) (at level 70).

Lemma incl_refl : forall Γ, Γ ⊆ Γ.
Proof. now unfold ctx_incl. Qed.

Lemma incl_trans : forall Γ Δ Θ, Γ ⊆ Δ -> Δ ⊆ Θ -> Γ ⊆ Θ.
Proof. unfold ctx_incl. auto. Qed.

Lemma incl_nil : forall Γ, [] ⊆ Γ.
Proof. unfold ctx_incl. intros Γ x A H. discriminate. Qed.

Lemma incl_ext : forall Γ Δ x A, Γ ⊆ Δ -> ((x, A) :: Γ) ⊆ ((x, A) :: Δ).
Proof.
  intros Γ Δ x A H y B. simpl.
  destruct (String.eqb y x); [trivial | apply H].
Qed.

(** The two structural rearrangements a named context needs; both are immediate
    once inclusion is phrased in terms of [lookup]. *)

Lemma incl_shadow : forall Γ x A B, ((x, A) :: (x, B) :: Γ) ⊆ ((x, A) :: Γ).
Proof.
  intros Γ x A B y C. simpl.
  destruct (String.eqb y x); [trivial | trivial].
Qed.

Lemma incl_swap : forall Γ x y A B,
  x <> y -> ((x, A) :: (y, B) :: Γ) ⊆ ((y, B) :: (x, A) :: Γ).
Proof.
  intros Γ x y A B Hxy z C. simpl.
  destruct (String.eqb_spec z x) as [Hzx|Hzx];
  destruct (String.eqb_spec z y) as [Hzy|Hzy]; trivial.
  exfalso. apply Hxy. now rewrite <- Hzx, Hzy.
Qed.
