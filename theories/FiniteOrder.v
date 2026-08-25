(** * Finite carrier order theory

    This file is independent of PCF and of the representation of abstract
    values. It packages exactly the mathematics used by the strictness
    analyser:

    - a partial order restricted to a carrier predicate;
    - a carrier-closed least-upper-bound operation, from which the usual
      join algebra follows;
    - a finite Boolean presentation of an order, used to prove that monotone
      iteration from a least element stabilizes within the carrier size.

    [Stabilization.v] supplies these interfaces with [enum], [aleb], [ajoin],
    [abot], and [aapply]. *)

From Stdlib Require Import Bool List Arith Lia.
Import ListNotations.

(** ** Carrier-scoped posets and join-semilattices *)

Record carrier_poset (X : Type) : Type := {
  ord_member : X -> Prop;
  ord_le : X -> X -> Prop;
  ord_refl : forall x, ord_le x x;
  ord_trans : forall x y z, ord_le x y -> ord_le y z -> ord_le x z;
  ord_antisym : forall x y,
    ord_member x -> ord_member y -> ord_le x y -> ord_le y x -> x = y
}.

Arguments ord_member {X} _ _.
Arguments ord_le {X} _ _ _.
Arguments ord_refl {X} _ _.
Arguments ord_trans {X} _ _ _ _ _ _.
Arguments ord_antisym {X} _ _ _ _ _ _ _.

Record join_semilat (X : Type) : Type := {
  join_base : carrier_poset X;
  join_op : X -> X -> X;
  join_closed : forall x y,
    ord_member join_base x -> ord_member join_base y ->
    ord_member join_base (join_op x y);
  join_left : forall x y,
    ord_member join_base x -> ord_member join_base y ->
    ord_le join_base x (join_op x y);
  join_right : forall x y,
    ord_member join_base x -> ord_member join_base y ->
    ord_le join_base y (join_op x y);
  join_least : forall x y z,
    ord_member join_base x -> ord_member join_base y ->
    ord_member join_base z ->
    ord_le join_base x z -> ord_le join_base y z ->
    ord_le join_base (join_op x y) z
}.

Arguments join_base {X} _.
Arguments join_op {X} _ _ _.

Lemma join_le_iff : forall X (J : join_semilat X) x y z,
  ord_member (join_base J) x ->
  ord_member (join_base J) y ->
  ord_member (join_base J) z ->
  (ord_le (join_base J) (join_op J x y) z <->
    ord_le (join_base J) x z /\ ord_le (join_base J) y z).
Proof.
  intros X [O join Hclosed Hleft Hright Hleast] x y z Hx Hy Hz.
  cbn in *. split.
  - intro H. split.
    + eapply ord_trans; [exact (Hleft _ _ Hx Hy) | exact H].
    + eapply ord_trans; [exact (Hright _ _ Hx Hy) | exact H].
  - intros [Hxz Hyz]. apply Hleast; assumption.
Qed.

Lemma join_mono : forall X (J : join_semilat X) x1 x2 y1 y2,
  ord_member (join_base J) x1 -> ord_member (join_base J) x2 ->
  ord_member (join_base J) y1 -> ord_member (join_base J) y2 ->
  ord_le (join_base J) x1 x2 -> ord_le (join_base J) y1 y2 ->
  ord_le (join_base J) (join_op J x1 y1) (join_op J x2 y2).
Proof.
  intros X [O join Hclosed Hleft Hright Hleast]
    x1 x2 y1 y2 Hx1 Hx2 Hy1 Hy2 Hx Hy. cbn in *.
  apply Hleast.
  - exact Hx1.
  - exact Hy1.
  - exact (Hclosed _ _ Hx2 Hy2).
  - eapply ord_trans; [exact Hx | exact (Hleft _ _ Hx2 Hy2)].
  - eapply ord_trans; [exact Hy | exact (Hright _ _ Hx2 Hy2)].
Qed.

Lemma join_idem : forall X (J : join_semilat X) x,
  ord_member (join_base J) x -> join_op J x x = x.
Proof.
  intros X [O join Hclosed Hleft Hright Hleast] x Hx. cbn in *.
  apply (ord_antisym O); try assumption.
  - apply Hclosed; assumption.
  - apply Hleast; try assumption; apply ord_refl.
  - apply Hleft; assumption.
Qed.

Lemma join_comm : forall X (J : join_semilat X) x y,
  ord_member (join_base J) x -> ord_member (join_base J) y ->
  join_op J x y = join_op J y x.
Proof.
  intros X [O join Hclosed Hleft Hright Hleast] x y Hx Hy. cbn in *.
  apply (ord_antisym O).
  - apply Hclosed; assumption.
  - apply Hclosed; assumption.
  - apply Hleast.
    + exact Hx.
    + exact Hy.
    + apply Hclosed; assumption.
    + apply Hright; assumption.
    + apply Hleft; assumption.
  - apply Hleast.
    + exact Hy.
    + exact Hx.
    + apply Hclosed; assumption.
    + apply Hright; assumption.
    + apply Hleft; assumption.
Qed.

Lemma join_assoc : forall X (J : join_semilat X) x y z,
  ord_member (join_base J) x ->
  ord_member (join_base J) y ->
  ord_member (join_base J) z ->
  join_op J (join_op J x y) z = join_op J x (join_op J y z).
Proof.
  intros X [O join Hclosed Hleft Hright Hleast] x y z Hx Hy Hz. cbn in *.
  assert (Hxy : ord_member O (join x y)) by (apply Hclosed; assumption).
  assert (Hyz : ord_member O (join y z)) by (apply Hclosed; assumption).
  assert (Hl : ord_member O (join (join x y) z))
    by (apply Hclosed; assumption).
  assert (Hr : ord_member O (join x (join y z)))
    by (apply Hclosed; assumption).
  apply (ord_antisym O); try assumption.
  - apply Hleast.
    + exact Hxy.
    + exact Hz.
    + exact Hr.
    + apply Hleast.
      * exact Hx.
      * exact Hy.
      * exact Hr.
      * exact (Hleft _ _ Hx Hyz).
      * eapply ord_trans.
        -- exact (Hleft _ _ Hy Hz).
        -- exact (Hright _ _ Hx Hyz).
    + eapply ord_trans.
      * exact (Hright _ _ Hy Hz).
      * exact (Hright _ _ Hx Hyz).
  - apply Hleast.
    + exact Hx.
    + exact Hyz.
    + exact Hl.
    + eapply ord_trans.
      * exact (Hleft _ _ Hx Hy).
      * exact (Hleft _ _ Hxy Hz).
    + apply Hleast.
      * exact Hy.
      * exact Hz.
      * exact Hl.
      * eapply ord_trans.
        -- exact (Hright _ _ Hx Hy).
        -- exact (Hleft _ _ Hxy Hz).
      * exact (Hright _ _ Hxy Hz).
Qed.

Record bounded_join_semilat (X : Type) : Type := {
  bounded_join_base : join_semilat X;
  order_bottom : X;
  bottom_closed : ord_member (join_base bounded_join_base) order_bottom;
  bottom_least : forall x,
    ord_member (join_base bounded_join_base) x ->
    ord_le (join_base bounded_join_base) order_bottom x
}.

Arguments bounded_join_base {X} _.
Arguments order_bottom {X} _.

Lemma join_bottom_l : forall X (J : bounded_join_semilat X) x,
  ord_member (join_base (bounded_join_base J)) x ->
  join_op (bounded_join_base J) (order_bottom J) x = x.
Proof.
  intros X [[O join Hclosed Hleft Hright Hleast] bot Hbot Hleastbot] x Hx.
  cbn in *. apply (ord_antisym O); try assumption.
  - apply Hclosed; assumption.
  - apply Hleast; try assumption; [apply Hleastbot, Hx | apply ord_refl].
  - apply Hright; assumption.
Qed.

Lemma join_bottom_r : forall X (J : bounded_join_semilat X) x,
  ord_member (join_base (bounded_join_base J)) x ->
  join_op (bounded_join_base J) x (order_bottom J) = x.
Proof.
  intros X J x Hx.
  rewrite (join_comm _ (bounded_join_base J));
    auto using bottom_closed, join_bottom_l.
Qed.

(** ** Finite Boolean orders *)

Record finite_poset (X : Type) : Type := {
  finite_carrier : list X;
  finite_eqb : X -> X -> bool;
  finite_leb : X -> X -> bool;
  finite_eqb_refl : forall x, finite_eqb x x = true;
  finite_eqb_eq : forall x y, finite_eqb x y = true -> x = y;
  finite_leb_refl : forall x, finite_leb x x = true;
  finite_leb_trans : forall x y z,
    finite_leb x y = true -> finite_leb y z = true -> finite_leb x z = true;
  finite_leb_antisym : forall x y,
    In x finite_carrier -> In y finite_carrier ->
    finite_leb x y = true -> finite_leb y x = true -> x = y
}.

Arguments finite_carrier {X} _.
Arguments finite_eqb {X} _ _ _.
Arguments finite_leb {X} _ _ _.

Definition finite_carrier_poset {X} (O : finite_poset X) : carrier_poset X.
Proof.
  refine {| ord_member := fun x => In x (finite_carrier O);
            ord_le := fun x y => finite_leb O x y = true |}.
  - apply finite_leb_refl.
  - intros. eapply finite_leb_trans; eauto.
  - intros. eapply finite_leb_antisym; eauto.
Defined.

Definition finite_closed {X} (O : finite_poset X) (f : X -> X) : Prop :=
  forall x, In x (finite_carrier O) -> In (f x) (finite_carrier O).

Definition finite_monotone {X} (O : finite_poset X) (f : X -> X) : Prop :=
  forall x y,
    In x (finite_carrier O) -> In y (finite_carrier O) ->
    finite_leb O x y = true -> finite_leb O (f x) (f y) = true.

Definition upper_size {X} (O : finite_poset X) (x : X) : nat :=
  length (filter (finite_leb O x) (finite_carrier O)).

Lemma filter_length_le : forall (X : Type) (f : X -> bool) l,
  length (filter f l) <= length l.
Proof.
  induction l as [| h t IH]; simpl; [lia |].
  destruct (f h); simpl; lia.
Qed.

Lemma filter_length_mono : forall (X : Type) (f g : X -> bool) l,
  (forall y, In y l -> f y = true -> g y = true) ->
  length (filter f l) <= length (filter g l).
Proof.
  induction l as [| h t IH]; intros Himp; simpl; [lia |].
  destruct (f h) eqn:Ef.
  - rewrite (Himp h (or_introl eq_refl) Ef). simpl.
    apply le_n_S, IH. intros y Hy. apply Himp. right. exact Hy.
  - destruct (g h); simpl;
      (eapply Nat.le_trans; [apply IH | lia]);
      intros y Hy; apply Himp; right; assumption.
Qed.

Lemma filter_length_strict : forall (X : Type) (f g : X -> bool) l x,
  (forall y, In y l -> f y = true -> g y = true) ->
  In x l -> f x = false -> g x = true ->
  length (filter f l) < length (filter g l).
Proof.
  induction l as [| h t IH]; intros x Himp Hin Hf Hg; [destruct Hin |].
  simpl. destruct Hin as [-> | Hin].
  - rewrite Hf, Hg. simpl.
    assert (length (filter f t) <= length (filter g t));
      [apply filter_length_mono | lia].
    intros y Hy. apply Himp. right. exact Hy.
  - destruct (f h) eqn:Ef.
    + rewrite (Himp h (or_introl eq_refl) Ef). simpl.
      apply -> Nat.succ_lt_mono. eapply IH; eauto.
      intros y Hy. apply Himp. right. exact Hy.
    + destruct (g h); simpl.
      * assert (length (filter f t) < length (filter g t));
          [eapply IH; eauto | lia].
        intros y Hy. apply Himp. right. exact Hy.
      * eapply IH; eauto.
        intros y Hy. apply Himp. right. exact Hy.
Qed.

Lemma upper_size_le : forall X (O : finite_poset X) x,
  upper_size O x <= length (finite_carrier O).
Proof. intros. apply filter_length_le. Qed.

Lemma upper_size_pos : forall X (O : finite_poset X) x,
  In x (finite_carrier O) -> 1 <= upper_size O x.
Proof.
  intros X O x Hx. unfold upper_size.
  assert (Hin : In x (filter (finite_leb O x) (finite_carrier O))).
  { apply filter_In. split; [exact Hx | apply finite_leb_refl]. }
  destruct (filter (finite_leb O x) (finite_carrier O));
    [destruct Hin | simpl; lia].
Qed.

Lemma upper_size_strict : forall X (O : finite_poset X) x y,
  In x (finite_carrier O) -> In y (finite_carrier O) ->
  finite_leb O x y = true -> x <> y ->
  upper_size O y < upper_size O x.
Proof.
  intros X O x y Hx Hy Hxy Hne. unfold upper_size.
  eapply filter_length_strict with (x := x).
  - intros z _ Hyz. eapply finite_leb_trans; eauto.
  - exact Hx.
  - destruct (finite_leb O y x) eqn:Eyx; [| reflexivity].
    exfalso. apply Hne. eapply finite_leb_antisym; eauto.
  - apply finite_leb_refl.
Qed.

(** ** Finite monotone iteration *)

Lemma iter_fixed : forall X (f : X -> X) x n,
  f x = x -> Nat.iter n f x = x.
Proof.
  intros X f x n E. induction n as [| n IH]; simpl; [reflexivity |].
  rewrite IH. exact E.
Qed.

Lemma iter_shift : forall X (f : X -> X) n x,
  Nat.iter (S n) f x = Nat.iter n f (f x).
Proof.
  intros X f n x. induction n as [| n IH]; simpl; [reflexivity |].
  rewrite <- IH. reflexivity.
Qed.

Lemma iter_closed : forall X (O : finite_poset X) (f : X -> X) x n,
  finite_closed O f -> In x (finite_carrier O) ->
  In (Nat.iter n f x) (finite_carrier O).
Proof.
  intros X O f x n Hclosed Hx. induction n as [| n IH]; simpl; auto.
Qed.

Theorem finite_chain_stab : forall X (O : finite_poset X) n
    (f : X -> X) x,
  finite_closed O f -> finite_monotone O f ->
  In x (finite_carrier O) ->
  finite_leb O x (f x) = true ->
  upper_size O x <= n ->
  Nat.iter (S n) f x = Nat.iter n f x.
Proof.
  intros X O n. induction n as [| n IH]; intros f x Hclosed Hmono Hx Hrise Hup.
  - pose proof (upper_size_pos X O x Hx). lia.
  - destruct (finite_eqb O x (f x)) eqn:E.
    + apply finite_eqb_eq in E.
      rewrite !iter_fixed; congruence.
    + assert (Hne : x <> f x).
      { intros H. rewrite <- H, finite_eqb_refl in E. discriminate. }
      assert (Hfx : In (f x) (finite_carrier O)) by (apply Hclosed, Hx).
      rewrite (iter_shift X f (S n) x), (iter_shift X f n x).
      apply (IH f (f x)); try assumption.
      * apply Hmono; assumption.
      * pose proof (upper_size_strict X O x (f x) Hx Hfx Hrise Hne). lia.
Qed.

Theorem finite_iter_is_fixpoint : forall X (O : finite_poset X)
    (f : X -> X) bottom budget,
  finite_closed O f -> finite_monotone O f ->
  In bottom (finite_carrier O) ->
  (forall x, In x (finite_carrier O) -> finite_leb O bottom x = true) ->
  length (finite_carrier O) <= budget ->
  f (Nat.iter budget f bottom) = Nat.iter budget f bottom.
Proof.
  intros X O f bottom budget Hclosed Hmono Hbot Hleast Hbudget.
  change (Nat.iter (S budget) f bottom = Nat.iter budget f bottom).
  apply finite_chain_stab with (O := O); try assumption.
  - apply Hleast, Hclosed, Hbot.
  - eapply Nat.le_trans; [apply upper_size_le | exact Hbudget].
Qed.

Theorem finite_iter_least : forall X (O : finite_poset X)
    (f : X -> X) bottom n x,
  finite_closed O f -> finite_monotone O f ->
  In bottom (finite_carrier O) ->
  (forall y, In y (finite_carrier O) -> finite_leb O bottom y = true) ->
  In x (finite_carrier O) -> f x = x ->
  finite_leb O (Nat.iter n f bottom) x = true.
Proof.
  intros X O f bottom n x Hclosed Hmono Hbot Hleast Hx Hfix.
  induction n as [| n IH]; simpl.
  - apply Hleast, Hx.
  - rewrite <- Hfix. apply Hmono; try assumption.
    apply iter_closed; assumption.
Qed.

Theorem finite_iter_mono : forall X (O : finite_poset X)
    (f g : X -> X) bottom n,
  finite_closed O f -> finite_closed O g -> finite_monotone O f ->
  (forall x, In x (finite_carrier O) -> finite_leb O (f x) (g x) = true) ->
  In bottom (finite_carrier O) ->
  finite_leb O (Nat.iter n f bottom) (Nat.iter n g bottom) = true.
Proof.
  intros X O f g bottom n Hf Hg Hmono Hfg Hbot.
  induction n as [| n IH]; simpl; [apply finite_leb_refl |].
  eapply finite_leb_trans.
  - apply Hmono.
    + exact (iter_closed X O f bottom n Hf Hbot).
    + exact (iter_closed X O g bottom n Hg Hbot).
    + exact IH.
  - apply Hfg. exact (iter_closed X O g bottom n Hg Hbot).
Qed.
