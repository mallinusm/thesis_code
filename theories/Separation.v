From Coq Require Import FunctionalExtensionality Lists.List.

From stdpp Require Import
  base.
From iris Require
  bi.derived_connectives
  bi.interface
  proofmode.tactics.

From Thesis Require Import AST Heap.

Import ListNotations.

Section Separation.

  (** We abstract away the concrete implementation of the Separation logic
      framework. This typeclass thus defines all the connectives that we want to
      support. Here, P is the type of Separation logic propositions. *)
  Class SepLog (P : Type) : Type :=
  {
    l_top : P ;
    l_bottom : P ;
    l_emp : P ;
    l_pure : Prop -> P ;
    l_star : P -> P -> P ;
    l_wand : P -> P -> P ;
    l_and : P -> P -> P ;
    l_or : P -> P -> P ;
    l_impl : P -> P -> P ;
    l_contains : ptr -> P ;
    l_validity : P -> Prop ;
    l_entails : P -> P -> Prop ;
    l_equiv : P -> P -> Prop ;
    l_pto : ptr -> nat -> nat -> P ;
    l_ex {A : Type} : (A -> P) -> P ;
    l_all {A : Type} : (A -> P) -> P;

    (* Derived connectives. *)
    l_emp_prop (Q : Prop) : P :=
      l_and (l_pure Q) l_emp;

    l_list_at : ptr -> list nat -> P :=
      fix list_at (p : ptr) (l : list nat) : P :=
        match l with
        | nil =>
            l_emp_prop (p = 0)
        | n :: t =>
            l_and
              (l_pure (p <> 0))
              (l_ex (fun (q : ptr) =>
                       (l_star
                          (l_pto p n q)
                          (list_at q t))))
        end;
  }.

  (** The type of shallow Separation logic propositions. *)
  Definition hprop : Type := heaplet -> Prop.

  Definition h_pure (P : Prop) : hprop := fun _ => P.

  Definition h_top : hprop := h_pure True.

  Definition h_bottom : hprop := h_pure False.

  Definition h_emp : hprop := fun (h : heaplet) => h = heaplet_empty.

  Definition h_and (P Q : hprop) : hprop := fun (h : heaplet) => P h /\ Q h.

  Definition h_or (P Q : hprop) : hprop := fun (h : heaplet) => P h \/ Q h.

  Definition h_pto (p : ptr) (n1 n2 : nat) : hprop :=
    fun (h : heaplet) =>
      h = heaplet_update heaplet_empty p (chunk_make n1 n2).

  Definition h_star (P Q : hprop) : hprop :=
    fun (h : heaplet) =>
      exists (h1 h2 : heaplet),
        P h1 /\ Q h2 /\ heaplet_disjoint h1 h2 /\ h = heaplet_union h1 h2.

  Definition h_wand (P Q : hprop) : hprop :=
    fun (h : heaplet) =>
      forall (h' : heaplet),
        heaplet_disjoint h h' -> P h' -> Q (heaplet_union h h').

  Definition h_all [A : Type] (f : A -> hprop) : hprop :=
    fun (h : heaplet) => forall (a : A), f a h.

  Definition h_ex [A : Type] (f : A -> hprop) : hprop :=
    fun (h : heaplet) => exists (a : A), f a h.

  Definition h_contains (p : ptr) : hprop :=
    h_ex (fun (c : chunk) =>
      match c with (n1, n2) => h_pto p n1 n2 end).

  Definition h_impl (P Q : hprop) : hprop := fun (h : heaplet) => P h -> Q h.

  Definition h_entails (P Q : hprop) : Prop := forall (h : heaplet), P h -> Q h.

  (* Definition h_validity (Q : hprop) : Prop := h_entails h_top Q. *)

  Definition h_equiv (P Q : hprop) : Prop := h_entails P Q /\ h_entails Q P.

End Separation.

Notation "p '|->' '(' n1 ',' n2 ')'" := (l_pto p n1 n2) (at level 95, no associativity).
Notation "P ∗ Q" := (l_star P Q) (at level 80, right associativity).
Notation "P −∗ Q" := (l_wand P Q) (at level 70, right associativity).
Notation "P '|-' Q" := (l_entails P Q) (at level 80, right associativity).
Notation "'|-' Q" := (l_validity Q) (at level 90, right associativity).

#[export] Instance hprop_equiv : base.Equiv hprop := h_equiv.
#[export] Instance pred_equivalence : Equivalence (≡@{hprop}).
Proof. firstorder. Qed.

Import iris.bi.interface.

(* Variant hemp (h : heaplet) : Prop := *)
(*   MkEmp : hemp h. *)
(* Variant sepₚ {w} (P Q : Pred w) (ι : Assignment w) : Prop := *)
(*   MkSep : P ι -> Q ι -> sepₚ P Q ι. *)
(* Variant wandₚ {w} (P Q : Pred w) (ι : Assignment w) : Prop := *)
(*   MkWand : (P ι -> Q ι) -> wandₚ P Q ι. *)
Variant persistently (P : hprop) (h : heaplet) : Prop :=
  MkPersistently : P h -> persistently P h.

#[export] Instance ofe_dist_pred : ofe.Dist hprop :=
  ofe.discrete_dist.

Definition bimixin_hprop :
  BiMixin h_entails h_emp (fun P _ => P) h_and h_or h_impl
    h_all h_ex h_star h_wand persistently.
Proof.
  constructor; try firstorder.
  - unfold h_entails. intros.
    unfold h_star. exists heaplet_empty, h.
    firstorder.
  - unfold h_entails. intros.
    unfold h_star in H.
    destruct H as (h1 & h2 & H1 & H2 & H3 & H4).
    subst. unfold h_emp in H1. subst.
    rewrite heaplet_union_empty_l. assumption.
  - unfold h_entails. intros.
    unfold h_star. unfold h_star in H.
    destruct H as (h1 & h2 & H1 & H2 & H3 & H4).
    subst. exists h2, h1. firstorder.
    rewrite heaplet_union_comm.
    + reflexivity.
    + assumption.
  - intros. unfold h_entails.
    intros. unfold h_star.
    unfold h_star in H.
    destruct H as (h1 & h2 & H1 & H2 & H3 & H4).
    destruct H1 as (h3 & h4 & H5 & H6 & H7 & H8).
    subst. exists h3, h4. admit.
  - admit.
  - admit.
  - admit.
Admitted.

(** Iris defines [bi_later_mixin_id] for BI algebras without later. However,
    the identity function as later still causes some later-specific
    typeclasses to be picked. We just define our own trivial modality and
    mixin to avoid that. *)
Variant later (P : hprop) (h : heaplet) : Prop :=
  MkLater : P h -> later P h.

Definition bilatermixin_hprop :
  BiLaterMixin h_entails (fun P _ => P) h_or h_impl
    h_all h_ex h_star persistently later.
Proof. firstorder. Qed.

Canonical HProp : bi :=
  {| bi_car            := hprop;
    bi_bi_mixin       := bimixin_hprop;
    bi_bi_later_mixin := bilatermixin_hprop;
  |}.

Module Import proofmode.
  Export iris.bi.interface.
  Export iris.bi.derived_connectives.
  Export iris.proofmode.tactics.
End proofmode.

(** A concrete and shallow Separation logic based on the implementation over
    the `hprop` type that uses Coq's deep-embedded propositions. *)
Global Instance ShallowSepLog : SepLog (interface.bi_car HProp) :=
  { l_top := bi_pure True ;
    l_bottom := bi_pure False ;
    l_emp := bi_emp ;
    l_pure := bi_pure ;
    l_pto := h_pto ;
    l_star := bi_sep ;
    l_wand := bi_wand ;
    l_contains := h_contains ;
    l_and := bi_and ;
    l_or := bi_or ;
    l_impl := bi_impl ;
    l_entails := bi_entails ;
    l_validity := bi_emp_valid ;
    l_equiv := bi_equiv _ ;
    l_ex := @bi_exist _;
    l_all := @bi_forall _;
  }.
