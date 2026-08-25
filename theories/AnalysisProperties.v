(** * Analysis properties: carrier closure and monotonicity

    This is the bridge from Stabilization.v's finite order theory to the
    abstract interpreter. It proves, mutually for the bidirectional synthesis
    and checking judgments, that [aeval]

    - returns a value in the enumerated carrier; and
    - is monotone in a pointwise-ordered abstract environment.

    Consequently every functional supplied by a well-checked program to the
    [fix] clause satisfies the carrier premise of
    [afix_approx_is_fixpoint]. These are the abstract-interpreter invariants
    consumed by AnalysisSoundness.v. *)

From Stdlib Require Import String Bool List Eqdep_dec.
From Equations Require Import Equations.
Import ListNotations.
From PCF Require Import Ty Syntax Context Checker Strictness Stabilization.

Open Scope string_scope.
Open Scope ty_scope.
Open Scope pcf_scope.

(** ** Ordered, carrier-valued environments *)

Inductive aenv_le : ctx -> aenv -> aenv -> Prop :=
| AEnvLe_nil : aenv_le [] [] []
| AEnvLe_cons : forall Γ ρ σ x A (u v : aval A),
    In u (enum A) ->
    In v (enum A) ->
    aleb u v = true ->
    aenv_le Γ ρ σ ->
    aenv_le ((x, A) :: Γ)
      ((x, PackAval u) :: ρ) ((x, PackAval v) :: σ).

#[export] Hint Constructors aenv_le : pcf.

Lemma aenv_le_refl_left : forall Γ ρ σ,
  aenv_le Γ ρ σ -> aenv_le Γ ρ ρ.
Proof.
  intros Γ ρ σ H. induction H; constructor; auto using aleb_refl.
Qed.

Lemma aenv_le_refl_right : forall Γ ρ σ,
  aenv_le Γ ρ σ -> aenv_le Γ σ σ.
Proof.
  intros Γ ρ σ H. induction H; constructor; auto using aleb_refl.
Qed.

Lemma aenv_lookup_le : forall Γ ρ σ,
  aenv_le Γ ρ σ ->
  forall x A, lookup Γ x = Some A ->
  exists (u v : aval A),
    alookup ρ x = Some (PackAval u)
    /\ alookup σ x = Some (PackAval v)
    /\ In u (enum A) /\ In v (enum A)
    /\ aleb u v = true.
Proof.
  intros Γ ρ σ Henv. induction Henv;
    intros y B Hlookup; simpl in Hlookup; [discriminate |].
  simpl. destruct (String.eqb y x) eqn:E.
  - injection Hlookup as <-. exists u, v. repeat split; assumption.
  - apply IHHenv in Hlookup as (u' & v' & Hu' & Hv' & Hcu & Hcv & Hle).
    exists u', v'. repeat split; assumption.
Qed.

(** ** Equations for well-typed branches of the total interpreter *)

Lemma cast_aval_same : forall A (v : aval A) (E : A = A), cast_aval E v = v.
Proof.
  intros A v E. rewrite (@UIP_dec ty ty_eq_dec A A E eq_refl). reflexivity.
Qed.

Lemma unpack_pack : forall A (v : aval A),
  unpack_aval A (PackAval v) = v.
Proof.
  intros A v. unfold unpack_aval. destruct (ty_eq_dec A A) as [E | E].
  - apply cast_aval_same.
  - contradiction E. reflexivity.
Qed.

Lemma aeval_app_eq : forall Γ ρ f u A B,
  infer Γ f = Ok (A ⇒ B) ->
  aeval Γ ρ (f · u) B =
    aapply (aeval Γ ρ f (A ⇒ B)) (aeval Γ ρ u A).
Proof.
  intros Γ ρ f u A B H. cbn [aeval]. rewrite H.
  destruct (ty_eq_dec B B) as [E | E].
  - apply cast_aval_same.
  - contradiction E. reflexivity.
Qed.

Lemma aeval_fix_eq : forall Γ ρ t A,
  aeval Γ ρ (tfix A t) A =
    afix_approx A (aeval Γ ρ t (A ⇒ A)) (dsize A).
Proof.
  intros Γ ρ t A. cbn [aeval]. destruct (ty_eq_dec A A) as [E | E].
  - apply cast_aval_same.
  - contradiction E. reflexivity.
Qed.

Lemma aeval_ann_eq : forall Γ ρ t A,
  aeval Γ ρ (t ∷ A) A = aeval Γ ρ t A.
Proof.
  intros Γ ρ t A. cbn [aeval]. destruct (ty_eq_dec A A) as [E | E].
  - apply cast_aval_same.
  - contradiction E. reflexivity.
Qed.

(** The paired conclusion carried through the mutual induction. *)
Definition aeval_respects (Γ : ctx) (ρ σ : aenv)
  (t : term) (A : ty) : Prop :=
  In (aeval Γ ρ t A) (enum A)
  /\ In (aeval Γ σ t A) (enum A)
  /\ aleb (aeval Γ ρ t A) (aeval Γ σ t A) = true.

Lemma table_leb_map_pointwise : forall I O (leO : O -> O -> bool)
    (f g : I -> O) xs,
  (forall x, In x xs -> leO (f x) (g x) = true) ->
  table_leb leO (map (fun x => (x, f x)) xs)
    (map (fun x => (x, g x)) xs) = true.
Proof.
  intros I O leO f g xs H. induction xs as [|x xs IH]; simpl; auto.
  rewrite H by apply in_eq. apply IH. intros y Hy. apply H. right. exact Hy.
Qed.

(** ** Mutual carrier closure and monotonicity *)

Theorem aeval_respects_fundamental :
  (forall Γ t A, Γ ⊢ t ⇑ A -> forall ρ σ,
      aenv_le Γ ρ σ -> aeval_respects Γ ρ σ t A)
  /\
  (forall Γ t A, Γ ⊢ t ⇓ A -> forall ρ σ,
      aenv_le Γ ρ σ -> aeval_respects Γ ρ σ t A).
Proof.
  apply bidir_ind.
  - (* variable *)
    intros Γ x A Hlookup ρ σ Henv.
    destruct (aenv_lookup_le _ _ _ Henv _ _ Hlookup)
      as (u & v & Hu & Hv & Hcu & Hcv & Hle).
    unfold aeval_respects. cbn [aeval]. rewrite Hu, Hv, !unpack_pack.
    repeat split; assumption.
  - (* numeral *)
    intros Γ n ρ σ Henv. unfold aeval_respects. simpl.
    repeat split; auto.
  - (* successor *)
    intros Γ t Ht IH ρ σ Henv. exact (IH ρ σ Henv).
  - (* predecessor *)
    intros Γ t Ht IH ρ σ Henv. exact (IH ρ σ Henv).
  - (* application *)
    intros Γ f u A B Hf IHf Hu IHu ρ σ Henv.
    destruct (IHf ρ σ Henv) as (HFρ & HFσ & HFle).
    destruct (IHu ρ σ Henv) as (Huρ & Huσ & Hule).
    unfold aeval_respects.
    assert (Hinfer : infer Γ f = Ok (A ⇒ B)) by
      (apply infer_complete; exact Hf).
    rewrite (aeval_app_eq Γ ρ f u A B Hinfer),
      (aeval_app_eq Γ σ f u A B Hinfer).
    repeat split.
    + eapply aapply_enum; eauto.
    + eapply aapply_enum; eauto.
    + eapply aleb_trans.
      * eapply aapply_mono; eauto.
      * eapply aapply_fun_mono; eauto.
  - (* fix *)
    intros Γ t A Ht IH ρ σ Henv.
    destruct (IH ρ σ Henv) as (HFρ & HFσ & HFle).
    unfold aeval_respects. rewrite !aeval_fix_eq. repeat split.
    + eapply afix_approx_enum; eauto.
    + eapply afix_approx_enum; eauto.
    + eapply afix_approx_mono; eauto.
  - (* annotation *)
    intros Γ t A Ht IH ρ σ Henv.
    unfold aeval_respects. rewrite !aeval_ann_eq. exact (IH ρ σ Henv).
  - (* lambda *)
    intros Γ x t A B Ht IH ρ σ Henv.
    unfold aeval_respects. cbn [aeval].
    set (tr := map (fun v =>
      (v, aeval ((x, A) :: Γ) ((x, PackAval v) :: ρ) t B)) (enum A)).
    set (ts := map (fun v =>
      (v, aeval ((x, A) :: Γ) ((x, PackAval v) :: σ) t B)) (enum A)).
    assert (Htr : In (AF tr) (enum (A ⇒ B))).
    { simpl. apply in_map_iff. exists tr. split; [reflexivity |].
      apply filter_In. split.
      - apply all_tables_complete.
        + subst tr. rewrite map_map. apply map_id.
        + intros a b Hab. subst tr. apply in_map_iff in Hab as (v & E & Hv).
          injection E as <- <-.
          assert (Hext : aenv_le ((x, A) :: Γ)
            ((x, PackAval v) :: ρ) ((x, PackAval v) :: ρ))
            by (constructor; [exact Hv | exact Hv | apply aleb_refl |
                exact (aenv_le_refl_left _ _ _ Henv)]).
          destruct (IH _ _ Hext) as (Hb & _ & _).
          exact Hb.
      - unfold monotone_tbl. rewrite forallb_forall. intros [a b] Hab.
        rewrite forallb_forall. intros [a' b'] Hab'.
        subst tr. apply in_map_iff in Hab as (u & E & Hu).
        apply in_map_iff in Hab' as (v & E' & Hv).
        injection E as <- <-. injection E' as <- <-. simpl.
        destruct (aleb u v) eqn:Euv; [| reflexivity].
        assert (Hext : aenv_le ((x, A) :: Γ)
          ((x, PackAval u) :: ρ) ((x, PackAval v) :: ρ))
          by (constructor; [exact Hu | exact Hv | exact Euv |
              exact (aenv_le_refl_left _ _ _ Henv)]).
        destruct (IH _ _ Hext) as (_ & _ & Hle).
        exact Hle. }
    assert (Hts : In (AF ts) (enum (A ⇒ B))).
    { simpl. apply in_map_iff. exists ts. split; [reflexivity |].
      apply filter_In. split.
      - apply all_tables_complete.
        + subst ts. rewrite map_map. apply map_id.
        + intros a b Hab. subst ts. apply in_map_iff in Hab as (v & E & Hv).
          injection E as <- <-.
          assert (Hext : aenv_le ((x, A) :: Γ)
            ((x, PackAval v) :: σ) ((x, PackAval v) :: σ))
            by (constructor; [exact Hv | exact Hv | apply aleb_refl |
                exact (aenv_le_refl_right _ _ _ Henv)]).
          destruct (IH _ _ Hext) as (Hb & _ & _).
          exact Hb.
      - unfold monotone_tbl. rewrite forallb_forall. intros [a b] Hab.
        rewrite forallb_forall. intros [a' b'] Hab'.
        subst ts. apply in_map_iff in Hab as (u & E & Hu).
        apply in_map_iff in Hab' as (v & E' & Hv).
        injection E as <- <-. injection E' as <- <-. simpl.
        destruct (aleb u v) eqn:Euv; [| reflexivity].
        assert (Hext : aenv_le ((x, A) :: Γ)
          ((x, PackAval u) :: σ) ((x, PackAval v) :: σ))
          by (constructor; [exact Hu | exact Hv | exact Euv |
              exact (aenv_le_refl_right _ _ _ Henv)]).
        destruct (IH _ _ Hext) as (_ & _ & Hle).
        exact Hle. }
    repeat split; try assumption.
    subst tr ts. simp aleb.
    apply table_leb_map_pointwise. intros v Hv.
    assert (Hext : aenv_le ((x, A) :: Γ)
      ((x, PackAval v) :: ρ) ((x, PackAval v) :: σ))
      by (constructor; [exact Hv | exact Hv | apply aleb_refl | exact Henv]).
    destruct (IH _ _ Hext) as (_ & _ & Hle). exact Hle.
  - (* ifz *)
    intros Γ c t u A Hc IHc Ht IHt Hu IHu ρ σ Henv.
    destruct (IHc ρ σ Henv) as (Hcρ & Hcσ & Hcle).
    destruct (IHt ρ σ Henv) as (Htρ & Htσ & Htle).
    destruct (IHu ρ σ Henv) as (Huρ & Huσ & Hule).
    destruct (enum_nat_inv _ Hcρ) as [Ecρ | Ecρ];
      destruct (enum_nat_inv _ Hcσ) as [Ecσ | Ecσ];
      rewrite Ecρ, Ecσ in *; simp an_defined aleb in *;
      unfold aeval_respects; cbn [aeval];
      rewrite Ecρ, Ecσ; simp an_defined.
    + repeat split; auto using abot_enum, aleb_refl.
    + repeat split; auto using abot_enum, ajoin_enum, abot_least.
    + discriminate.
    + repeat split; eauto using ajoin_enum, ajoin_mono.
  - (* mode switch *)
    intros Γ t A Ht IH ρ σ Henv. exact (IH ρ σ Henv).
Qed.

Corollary aeval_synth_respects : forall Γ t A,
  Γ ⊢ t ⇑ A -> forall ρ σ,
  aenv_le Γ ρ σ -> aeval_respects Γ ρ σ t A.
Proof. apply aeval_respects_fundamental. Qed.

Corollary aeval_check_respects : forall Γ t A,
  Γ ⊢ t ⇓ A -> forall ρ σ,
  aenv_le Γ ρ σ -> aeval_respects Γ ρ σ t A.
Proof. apply aeval_respects_fundamental. Qed.

(** The carrier projection alone, at the minimal hypothesis: a reflexively
    ordered abstract environment. AnalysisSoundness.v consumes this form at
    application, [fix] and [ifz] sites. *)
Corollary aeval_synth_enum : forall Γ t A,
  Γ ⊢ t ⇑ A -> forall ρ,
  aenv_le Γ ρ ρ -> In (aeval Γ ρ t A) (enum A).
Proof.
  intros Γ t A Ht ρ Henv.
  exact (proj1 (aeval_synth_respects _ _ _ Ht _ _ Henv)).
Qed.

Corollary aeval_check_enum : forall Γ t A,
  Γ ⊢ t ⇓ A -> forall ρ,
  aenv_le Γ ρ ρ -> In (aeval Γ ρ t A) (enum A).
Proof.
  intros Γ t A Ht ρ Henv.
  exact (proj1 (aeval_check_respects _ _ _ Ht _ _ Henv)).
Qed.

Corollary aeval_synth_mono : forall Γ t A,
  Γ ⊢ t ⇑ A -> forall ρ σ,
  aenv_le Γ ρ σ ->
  aleb (aeval Γ ρ t A) (aeval Γ σ t A) = true.
Proof.
  intros Γ t A Ht ρ σ Henv.
  exact (proj2 (proj2 (aeval_synth_respects _ _ _ Ht _ _ Henv))).
Qed.

Corollary aeval_check_mono : forall Γ t A,
  Γ ⊢ t ⇓ A -> forall ρ σ,
  aenv_le Γ ρ σ ->
  aleb (aeval Γ ρ t A) (aeval Γ σ t A) = true.
Proof.
  intros Γ t A Ht ρ σ Henv.
  exact (proj2 (proj2 (aeval_check_respects _ _ _ Ht _ _ Henv))).
Qed.

Corollary analyse_check_enum : forall t A,
  [] ⊢ t ⇓ A -> In (analyse t A) (enum A).
Proof.
  intros t A Ht. destruct (aeval_check_respects _ _ _ Ht [] [] AEnvLe_nil).
  exact H.
Qed.

Corollary checked_fix_is_fixpoint : forall t A,
  [] ⊢ t ⇓ (A ⇒ A) ->
  aapply (analyse t (A ⇒ A))
    (afix_approx A (analyse t (A ⇒ A)) (dsize A)) =
  afix_approx A (analyse t (A ⇒ A)) (dsize A).
Proof.
  intros t A Ht. apply afix_approx_is_fixpoint, analyse_check_enum, Ht.
Qed.
