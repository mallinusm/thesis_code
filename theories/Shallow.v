From Coq Require Import String.

From Thesis Require Import AST Store Heap Monad Separation.

Section Shallow.

  Definition predicate : Type := c_store -> iris.bi.interface.bi_car HProp.

  Definition M : Type -> Type := cont predicate.

  Global Instance ShallowSpecification : Monad M :=
  {
    ret {A : Type} (a : A) :=
      fun (Q : A -> predicate) => Q a ;
    bind {A B : Type} (m : M A) (f : A -> M B) :=
      fun (Q : B -> predicate) =>
        m (fun (a : A) => f a Q) ;
  }.

  (** For the remainder of this file, we generalize the constraint generation
      by working against the Separation logic interface. *)
  Definition success {A : Type} : M A := fun _ _ => l_pure True.

  Definition error {A : Type} : M A := fun _ _ => l_pure False.

  (** Restrict ourselves to natural numbers in order to make it easier to move
      this infrastructure into a deep-embedding. *)
  Definition angelic_branch : M nat :=
    fun (Q : nat -> predicate) (s : c_store) =>
      l_ex (fun (n : nat) => Q n s).

  Definition demonic_branch : M nat :=
    fun (Q : nat -> predicate) (s : c_store) =>
      l_all (fun (n : nat) => Q n s).

  Definition angelic_choice {A : Type} (m1 m2 : M A) : M A :=
    fun (Q : A -> predicate) (s : c_store) =>
      l_or (m1 Q s) (m2 Q s).

  Definition demonic_choice {A : Type} (m1 m2 : M A) : M A :=
    fun (Q : A -> predicate) (s : c_store) =>
      l_and (m1 Q s) (m2 Q s).

  Definition assert (p : Prop) : M unit :=
    fun (Q : unit -> predicate) (s : c_store) =>
      l_and (l_pure p) (Q tt s).

  Definition assume (p : Prop) : M unit :=
    fun (Q : unit -> predicate) (s : c_store) =>
      l_impl (l_pure p) (Q tt s).

  Definition assign (x : pvar) (n : nat) : M unit :=
    fun (Q : unit -> predicate) (s : c_store) =>
      Q tt (c_store_update s x n).

  Definition lookup (x : pvar) : M nat :=
    fun (Q : nat -> predicate) (s : c_store) =>
      match s x with Some v => Q v s | _ => l_bottom end.

  Definition match_bool_angelic_choice {A : Type} (b : bool)
                                                  (m1 m2 : M A) : M A :=
    angelic_choice
      (assume (b = true) ;; m1)
      (assume (b = false) ;; m2).

  Definition match_bool_demonic_choice {A : Type} (b : bool)
                                                  (m1 m2 : M A) : M A :=
    demonic_choice
      (assume (b = true) ;; m1)
      (assume (b = false) ;; m2).

  Definition consume (P : hprop) : M unit :=
    fun (Q : unit -> predicate) (s : c_store) =>
      P ∗ Q tt s.

  Definition produce (P : hprop) : M unit :=
    fun (Q : unit -> predicate) (s : c_store) =>
      P −∗ Q tt s.

  Definition get_store : M c_store :=
    fun (Q : c_store -> predicate) (s : c_store) =>
      Q s s.

  Definition put_store (s : c_store) : M unit :=
    fun (Q : unit -> predicate) _ =>
      Q tt s.

End Shallow.
