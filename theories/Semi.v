From Coq Require Import FunctionalExtensionality Lia List String.

From Thesis Require Import AST Separation Monad Heap
  Shallow Interpreter WP Store Aux.

Import ListNotations.

Section Semi.

  Fixpoint eval_sterm (t : sterm) (e : lenv) : M lval :=
    match t with
    | SymConst v => ret v
    | SymPVar x =>
      n <- lookup x ;;
      ret (LogNum n)
    | SymLVar l =>
      match e l with
      | Some v => ret v
      | _ => error
      end
    | SymApp op t1 t2 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      match v1, v2 with
      | LogNum n1, LogNum n2 =>
        ret (LogNum (nat_op_to_fun op n1 n2))
      | _, _ => error
      end
    | SymCons t1 t2 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      match v1, v2 with
      | LogNum n, LogList ns =>
        ret (LogList ([n] ++ ns))
      | _, _ => error
      end
    | SymNil => ret (LogList [])
    | SymLength t1 => 
      v1 <- eval_sterm t1 e ;;
      match v1 with
      | LogList ns => ret (LogNum (List.length ns))
      | _ => error
      end
    end.
  
  Fixpoint consume_assertion (a : assertion) (e : lenv) : M unit :=
    match a with
    | Equal t1 t2 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      match v1, v2 with
      | LogNum n1, LogNum n2 =>
        assert (n1 = n2)
      | LogList xs, LogList ys =>
        assert (xs = ys)
      | _, _ => error
      end
    | Star a1 a2 =>
      consume_assertion a1 e ;;
      consume_assertion a2 e
    | Pto t1 t2 t3 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      v3 <- eval_sterm t3 e ;;
      match v1, v2, v3 with
      | LogNum p, LogNum n1, LogNum n2 =>
        consume (p |-> (n1, n2))
      | _, _, _ => error
      end
    | ListAt t1 t2 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      match v1, v2 with
      | LogNum p, LogList xs =>
        consume (l_list_at p xs)
      | _, _ => error
      end
    | Or a1 a2 =>
      angelic_choice
        (consume_assertion a1 e)
        (consume_assertion a2 e)
    | Exist x a' =>
      match x with
      | VarNum _ =>
        v <- angelic_branch ;;
        consume_assertion a' (lenv_insert e x (LogNum v))
      | VarList _ =>
        v <- angelic_branch_list ;;
        consume_assertion a' (lenv_insert e x (LogList v))
      end
    end.

  Fixpoint produce_assertion (a : assertion) (e : lenv) : M unit :=
    match a with
    | Equal t1 t2 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      match v1, v2 with
      | LogNum n1, LogNum n2 =>
        assume (n1 = n2)
      | LogList xs, LogList ys =>
        assume (xs = ys)
      | _, _ => error
      end
    | Star c1 c2 =>
      produce_assertion c1 e ;;
      produce_assertion c2 e
    | Pto t1 t2 t3 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      v3 <- eval_sterm t3 e ;;
      match v1, v2, v3 with
      | LogNum p, LogNum n1, LogNum n2 =>
        produce (p |-> (n1, n2))
      | _, _, _ => error
      end
    | ListAt t1 t2 =>
      v1 <- eval_sterm t1 e ;;
      v2 <- eval_sterm t2 e ;;
      match v1, v2 with
      | LogNum p, LogList xs =>
        produce (l_list_at p xs)
      | _, _ => error
      end
    | Or a1 a2 =>
      demonic_choice
        (produce_assertion a1 e)
        (produce_assertion a2 e)
    | Exist x a' =>
      match x with
      | VarNum _ =>
        v <- demonic_branch ;;
        produce_assertion a' (lenv_insert e x (LogNum v))
      | VarList _ =>
        v <- demonic_branch_list ;;
        produce_assertion a' (lenv_insert e x (LogList v))
      end
    end.

  Record program : Type := {
    pre : assertion ;
    com : command ;
    post : assertion
  }.

  Definition with_local_store {A : Type} (m : M A) : M unit :=
    s <- get_store ;; m ;; put_store s.

  Fixpoint havoc_store (xs : list pvar) : M unit :=
    match xs with
    | nil => success
    | x :: t =>
      s <- get_store ;;
      n <- demonic_branch ;;
      put_store (c_store_update s x n) ;;
      havoc_store t
    end.

  Definition leak_check : M unit :=
    fun _ _ => h_emp.

  Definition clear_heap : M unit :=
    fun (Q : unit -> predicate) (s : c_store) _ =>
      Q tt s heaplet_empty.

  Fixpoint sc_wp_com (c : command) (e : lenv) : M unit :=
    match c with
    | ComSeq c1 c2 =>
      sc_wp_com c1 e ;; sc_wp_com c2 e
    | ComIf b c1 c2 =>
      b' <- c_wp_bool_exp b ;;
      match_bool_demonic_choice b' (sc_wp_com c1 e) (sc_wp_com c2 e)
    | ComWhile inv b c' =>
      with_local_store (consume_assertion inv e) ;;
      pvars <- calculate_pvars_com c' ;;
      havoc_store pvars ;;
      demonic_choice
      (
        clear_heap ;;
        (
          with_local_store (produce_assertion inv e) ;;
          b' <- c_wp_bool_exp b ;;
          assume (b' = true) ;;
          sc_wp_com c' e ;;
          with_local_store (consume_assertion inv e)
        ) ;;
        leak_check
      )
      (
        with_local_store (produce_assertion inv e) ;;
        b' <- c_wp_bool_exp b ;;
        assume (b' = false)
      )
    | _ => c_wp_com c
    end.

  Definition aux_sc_vcgen (p : program) : M unit :=
    match p with Build_program pre c post =>
      pre_lvars <- calculate_lvars_assertion pre ;;
      post_lvars <- calculate_lvars_assertion post ;;
      e <- init_lenv (pre_lvars ++ post_lvars) lenv_empty ;;
      pre_pvars <- calculate_pvars_assertion pre ;;
      post_pvars <- calculate_pvars_assertion post ;;
      s <- get_store ;;
      s' <- init_store (pre_pvars ++ post_pvars) s ;;
      _ <- put_store s' ;;
      _ <- produce_assertion pre e ;;
      _ <- sc_wp_com c e ;;
      consume_assertion post e
    end.

  Definition sc_vcgen (p : program) : Prop :=
    |- aux_sc_vcgen p (fun _ _ => h_top) c_store_empty.

End Semi.
