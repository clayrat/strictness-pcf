(** * Operational soundness of the strictness analyser

    This file is the capstone of the analysis development. AnalysisProperties.v
    proves that [aeval] is carrier-valued and monotone; LogicalRelation.v
    supplies the step-indexed relation and its compatibility laws. Here the
    two interfaces meet:

    - [logical_fundamental] relates every bidirectionally typed term to the
      abstract value computed by [aeval];
    - [analyse_check_related] specializes the theorem to closed programs; and
    - [certified_strict_sound] proves the public Boolean certificate sound.

    The theorem is operational: a positive certificate guarantees divergence
    when the certified function is applied to any well-typed diverging natural
    argument. It does not require a separate denotational semantics. *)

From Stdlib Require Import String List Arith Lia.
Import ListNotations.
From PCF Require Import Ty Syntax Context Typing Checker Subst
                        OperationalSemantics Strictness Stabilization
                        AnalysisProperties LogicalRelation.

Open Scope string_scope.
Open Scope ty_scope.
Open Scope pcf_scope.

(** ** Bridging related and ordered environments *)

(** Forgetting the concrete components of a related environment leaves the
    reflexive abstract environment relation required by [aeval]'s carrier
    theorem. *)
Lemma cenv_rel_aenv_refl : forall k Γ ρ γ,
  cenv_rel k Γ ρ γ -> aenv_le Γ ρ ρ.
Proof.
  intros k Γ ρ γ Henv. induction Henv; constructor;
    auto using aleb_refl.
Qed.

(** ** Fundamental theorem *)

(** Every bidirectionally typed term is related, at every finite observation
    depth, to the abstract value computed in a correspondingly related
    environment. The mutual statement follows the checker judgments: the
    application rule needs the synthesized domain, while lambda and [ifz]
    consume an expected type. *)
Theorem logical_fundamental :
  (forall Γ t A, Γ ⊢ t ⇑ A -> forall ρ γ,
      open_term_rel Γ ρ γ t A)
  /\
  (forall Γ t A, Γ ⊢ t ⇓ A -> forall ρ γ,
      open_term_rel Γ ρ γ t A).
Proof.
  apply bidir_ind.
  - (* variable *)
    intros Γ x A Hlookup ρ γ k Henv.
    destruct (cenv_lookup_rel _ _ _ _ Henv _ _ Hlookup)
      as (a & u & Habstract & Hconcrete & _ & _ & Hrel).
    cbn [aeval instantiate].
    rewrite Habstract, Hconcrete, unpack_pack. exact Hrel.
  - (* numeral *)
    intros Γ n ρ γ k Henv. apply semantic_rel_num.
  - (* successor *)
    intros Γ t Ht IH ρ γ k Henv.
    cbn [aeval instantiate]. apply term_rel_succ, IH, Henv.
  - (* predecessor *)
    intros Γ t Ht IH ρ γ k Henv.
    cbn [aeval instantiate]. apply term_rel_pred, IH, Henv.
  - (* application *)
    intros Γ f u A B Hf IHf Hu IHu ρ γ k Henv.
    assert (Hinfer : infer Γ f = Ok (A ⇒ B)) by
      (apply infer_complete; exact Hf).
    rewrite (aeval_app_eq Γ ρ f u A B Hinfer).
    cbn [instantiate].
    eapply term_rel_app.
    + eapply aeval_check_enum;
        [eassumption | eapply cenv_rel_aenv_refl; eassumption].
    + eapply instantiate_closed_of_typing; [exact Henv | apply chk_typing, Hu].
    + exact (IHf ρ γ k Henv).
    + exact (IHu ρ γ k Henv).
  - (* fix *)
    intros Γ f A Hf IH ρ γ k Henv.
    rewrite aeval_fix_eq. cbn [instantiate].
    eapply term_rel_fix.
    + eapply aeval_check_enum;
        [eassumption | eapply cenv_rel_aenv_refl; eassumption].
    + eapply instantiate_closed_of_typing; [exact Henv | apply chk_typing, Hf].
    + exact (IH ρ γ k Henv).
  - (* annotation *)
    intros Γ t A Ht IH ρ γ k Henv.
    rewrite aeval_ann_eq. cbn [instantiate].
    eapply term_rel_step_back; [apply S_Ann | exact (IH ρ γ k Henv)].
  - (* lambda *)
    intros Γ x t A B Ht IH ρ γ k. revert ρ γ.
    induction k as [| k IHk]; intros ρ γ Henv; [exact I |].
    cbn [aeval instantiate]. split.
    + apply IHk. apply (cenv_rel_down (S k) k Γ ρ γ); [lia | exact Henv].
    + left. exists x, (instantiate (cremove x γ) t). split;
        [reflexivity |].
      intros d u Hd Hclosed_u Hdu.
      rewrite aapply_tabulate by exact Hd.
      assert (Hdown : cenv_rel k Γ ρ γ).
      { apply (cenv_rel_down (S k) k Γ ρ γ); [lia | exact Henv]. }
      assert (Hext : cenv_rel k ((x, A) :: Γ)
          ((x, PackAval d) :: ρ) ((x, u) :: γ)).
      { constructor; assumption. }
      pose proof (IH ((x, PackAval d) :: ρ) ((x, u) :: γ) k Hext)
        as Hbody.
      rewrite (instantiate_cons t γ x u (cenv_rel_closed _ _ _ _ Hdown)
        Hclosed_u) in Hbody.
      exact Hbody.
  - (* conditional *)
    intros Γ c t u A Hc IHc Ht IHt Hu IHu ρ γ k Henv.
    cbn [aeval instantiate]. eapply term_rel_ifz.
    + eapply aeval_check_enum;
        [eassumption | eapply cenv_rel_aenv_refl; eassumption].
    + eapply aeval_check_enum;
        [eassumption | eapply cenv_rel_aenv_refl; eassumption].
    + exact (IHc ρ γ k Henv).
    + exact (IHt ρ γ k Henv).
    + exact (IHu ρ γ k Henv).
  - (* mode switch *)
    intros Γ t A Ht IH ρ γ k Henv. exact (IH ρ γ k Henv).
Qed.

Corollary logical_synth_fundamental : forall Γ t A,
  Γ ⊢ t ⇑ A -> forall ρ γ, open_term_rel Γ ρ γ t A.
Proof. apply logical_fundamental. Qed.

Corollary logical_check_fundamental : forall Γ t A,
  Γ ⊢ t ⇓ A -> forall ρ γ, open_term_rel Γ ρ γ t A.
Proof. apply logical_fundamental. Qed.

(** ** Closed programs and the public certificate *)

Corollary analyse_check_related : forall t A,
  [] ⊢ t ⇓ A -> semantic_rel (analyse t A) t.
Proof.
  intros t A Ht k. unfold analyse.
  pose proof (logical_check_fundamental [] t A Ht [] [] k (CEnvRel_nil k))
    as Hrel.
  rewrite instantiate_nil in Hrel. exact Hrel.
Qed.

(** End-to-end soundness of the Boolean strictness certificate. A positive
    answer includes its typing guard and guarantees divergence on every
    closed, well-typed diverging natural argument. *)
Theorem certified_strict_sound : forall f,
  certified_strict f = true ->
  forall u, [] ⊢ u ∈ ℕ -> diverges u -> diverges (f · u).
Proof.
  intros f Hcert. unfold certified_strict in Hcert.
  destruct (check [] f (ℕ ⇒ ℕ)) as [[] | e] eqn:Hcheck;
    [| discriminate].
  apply aval_eqb_eq in Hcert.
  eapply semantic_strict_nat.
  - apply analyse_check_enum, check_sound, Hcheck.
  - apply analyse_check_related, check_sound, Hcheck.
  - exact Hcert.
Qed.
