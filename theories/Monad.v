Section Monad.

  Definition cont (R A : Type) : Type := (A -> R) -> R.

  Class Monad (M : Type -> Type) : Type :=
  {
    ret : forall {A : Type}, A -> M A ;
    bind : forall {A B : Type}, M A -> (A -> M B) -> M B ;
  }.

  Global Instance OptionMonad : Monad option :=
  {
    ret {A : Type} (a : A) := Some a ;
    bind {A B : Type} (m : option A) (f : A -> option B) :=
      match m with
      | Some v => f v
      | None   => None
      end
  }.

  Definition ST (S A : Type) : Type := S -> A * S.

  Global Instance StateMonad (S : Type) : Monad (ST S) :=
  {
    ret {A : Type} (a : A) :=
      fun (s : S) => (a , s) ;
    bind {A B : Type} (m : ST S A) (f : A -> ST S B) :=
      fun (s : S) => let (a, s') := m s in f a s'
  }.

  Definition state_option (S A : Type) : Type := S -> option (A * S).

  Global Instance StateOptionMonad (S : Type) : Monad (state_option S) :=
  {
    ret {A : Type} (a : A) :=
      fun (s : S) => Some (a, s) ;
    bind {A B : Type} (m : state_option S A) (f : A -> state_option S B) :=
      fun (s : S) =>
        match m s with
        | Some (a, s') => f a s'
        | None         => None
        end
  }.

  Definition get_state {S : Type} : state_option S S :=
    fun (s : S) => Some (s, s).

  Definition put_state {S : Type} (s : S) : state_option S unit :=
    fun _ => Some (tt, s).

  Definition fail {A B : Type} : state_option A B :=
    fun _ => None.

End Monad.

Notation "ma ;; mb" :=
  (bind ma (fun _ => mb))
  (at level 100, mb at level 200, right associativity,
    format "'[v' ma ;; '/' mb ']'").
Notation "x <- ma ;; mb" :=
  (bind ma (fun x => mb))
  (right associativity, at level 100, ma at next level).
Notation "' pat <- ma ;; mb" :=
  (bind ma (fun x => match x with pat => mb end))
  (at level 100, pat pattern, ma at next level, right associativity).
