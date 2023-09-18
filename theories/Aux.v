From Thesis Require Import Monad AST Store Separation Shallow.

From Coq Require Import List.
Import ListNotations.

Section Aux.

  Definition lenv : Type := lvar -> option lval.

  Definition lenv_empty : lenv := fun _ => None.

  Definition lvar_eqb (x y : lvar) : bool :=
    match x, y with
    | VarNum s1, VarNum s2 => String.eqb s1 s2
    | VarList s1, VarList s2 => String.eqb s1 s2
    | _, _ => false
    end.

  Definition lenv_insert (e : lenv) (x : lvar) (v : lval) : lenv :=
    fun (y : lvar) => if lvar_eqb x y then Some v else e y.

  Definition demonic_branch_list : M (list nat) :=
    fun (Q : list nat -> predicate) (s : c_store) =>
      l_all (fun (xs : list nat) => Q xs s).

  Definition angelic_branch_list : M (list nat) :=
    fun (Q : list nat -> predicate) (s : c_store) =>
      l_ex (fun (xs : list nat) => Q xs s).

  Fixpoint calculate_lvars_sterm (t : sterm) : M (list lvar) :=
    match t with
    | SymNil => ret []
    | SymConst _ => ret []
    | SymLength t1 =>
      calculate_lvars_sterm t1
    | SymPVar _ => ret []
    | SymLVar l => ret [l]
    | SymApp _ t1 t2 =>
      xs <- calculate_lvars_sterm t1 ;;
      ys <- calculate_lvars_sterm t2 ;;
      ret (xs ++ ys)
    | SymCons t1 t2 =>
      xs <- calculate_lvars_sterm t1 ;;
      ys <- calculate_lvars_sterm t2 ;;
      ret (xs ++ ys)
    end.

  Fixpoint calculate_lvars_assertion (a : assertion) : M (list lvar) :=
    match a with
    | Equal t1 t2 =>
      xs <- calculate_lvars_sterm t1 ;;
      ys <- calculate_lvars_sterm t2 ;;
      ret (xs ++ ys)
    | Star a1 a2 =>
      xs <- calculate_lvars_assertion a1 ;;
      ys <- calculate_lvars_assertion a2 ;;
      ret (xs ++ ys)
    | Pto t1 t2 t3 =>
      xs <- calculate_lvars_sterm t1 ;;
      ys <- calculate_lvars_sterm t2 ;;
      zs <- calculate_lvars_sterm t3 ;;
      ret (xs ++ ys ++ zs)
    | ListAt t1 t2 =>
      xs <- calculate_lvars_sterm t1 ;;
      ys <- calculate_lvars_sterm t2 ;;
      ret (xs ++ ys)
    | Or a1 a2 =>
      xs <- calculate_lvars_assertion a1 ;;
      ys <- calculate_lvars_assertion a2 ;;
      ret (xs ++ ys)
    | Exist x a' =>
      xs <- calculate_lvars_assertion a' ;;
      ret ([x] ++ xs)
    end.

  (** Initialise the logic environment, i.e. assign demonic values to every
      logic variable. We assume the list contains duplicates; we therefore do
      not re-assign a demonic value if a binding is already available. *)
  Fixpoint init_lenv (xs : list lvar) (e : lenv) : M lenv :=
    match xs with
    | nil => ret e
    | x :: t =>
      e' <- init_lenv t e ;;
      match e' x with
      | Some _ => ret e'
      | None =>
        match x with
        | VarNum x' =>
          n <- demonic_branch ;;
          ret (lenv_insert e' x (LogNum n))
        | VarList x' =>
          xs <- demonic_branch_list ;;
          ret (lenv_insert e' x (LogList xs))
        end
      end
    end.

  (** Assign demonic values to every program variable. Assume duplicates; do not
      re-assign if a binding is available. *)
  Fixpoint init_store (xs : list pvar) (s : c_store) : M c_store :=
    match xs with
    | nil => ret s
    | x :: t =>
      match s x with
      | Some _ => ret s
      | None =>
        n <- demonic_branch ;;
        init_store t (c_store_update s x n)
      end
    end.

  Fixpoint calculate_pvars_sterm (t : sterm) : M (list pvar) :=
    match t with
    | SymNil => ret []
    | SymConst _ => ret []
    | SymLength t1 => calculate_pvars_sterm t1
    | SymPVar x => ret [x]
    | SymLVar _ => ret []
    | SymApp _ t1 t2 =>
      xs <- calculate_pvars_sterm t1 ;;
      ys <- calculate_pvars_sterm t2 ;;
      ret (xs ++ ys)
    | SymCons t1 t2 =>
      xs <- calculate_pvars_sterm t1 ;;
      ys <- calculate_pvars_sterm t2 ;;
      ret (xs ++ ys)
    end.

  Fixpoint calculate_pvars_assertion (a : assertion) : M (list pvar) :=
    match a with
    | Equal t1 t2 =>
      xs <- calculate_pvars_sterm t1 ;;
      ys <- calculate_pvars_sterm t2 ;;
      ret (xs ++ ys)
    | Star a1 a2 =>
      xs <- calculate_pvars_assertion a1 ;;
      ys <- calculate_pvars_assertion a2 ;;
      ret (xs ++ ys)
    | Pto t1 t2 t3 =>
      xs <- calculate_pvars_sterm t1 ;;
      ys <- calculate_pvars_sterm t2 ;;
      zs <- calculate_pvars_sterm t3 ;;
      ret (xs ++ ys ++ zs)
    | ListAt t1 t2 =>
      xs <- calculate_pvars_sterm t1 ;;
      ys <- calculate_pvars_sterm t2 ;;
      ret (xs ++ ys)
    | Or a1 a2 =>
      xs <- calculate_pvars_assertion a1 ;;
      ys <- calculate_pvars_assertion a2 ;;
      ret (xs ++ ys)
    | Exist _ a' =>
      calculate_pvars_assertion a'
    end.

  Fixpoint calculate_pvars_com (c : command) : M (list pvar) :=
    match c with
    | ComSkip => ret []
    | ComAssign x _ => ret [x]
    | ComSeq c1 c2 =>
      xs <- calculate_pvars_com c1 ;;
      ys <- calculate_pvars_com c2 ;;
      ret (xs ++ ys)
    | ComIf _ c1 c2 =>
      xs <- calculate_pvars_com c1 ;;
      ys <- calculate_pvars_com c2 ;;
      ret (xs ++ ys)
    | ComWhile inv _ c' =>
      xs <- calculate_pvars_assertion inv ;;
      ys <- calculate_pvars_com c' ;;
      ret (xs ++ ys)
    | ComCons x _ _ => ret [x]
    | ComFree x => ret [x]
    | ComCar x y => ret [x ; y]
    | ComCdr x y => ret [x ; y]
    | ComSetCar x _ => ret [x]
    | ComSetCdr x _ => ret [x]
    end.

  Fixpoint havoc_lenv (xs : list lvar) (e : lenv) : M lenv :=
    match xs with
    | nil => ret e
    | x :: t =>
      match x with
      | VarNum y =>
        n <- Shallow.demonic_branch ;;
        havoc_lenv t (lenv_insert e x (LogNum n))
      | VarList ys =>
        ns <- demonic_branch_list ;;
        havoc_lenv t (lenv_insert e x (LogList ns))
      end
    end.

End Aux.
