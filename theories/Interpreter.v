From Coq Require Import String.

From Thesis Require Import Monad AST Store Heap.

Section Interpreter.

  Definition c_state : Type := c_store * c_heap.

  Definition nat_op_to_fun (op : nat_op) : nat -> nat -> nat :=
    match op with
    | NatAdd => Nat.add
    | NatSub => Nat.sub
    | NatMul => Nat.mul
    | NatDiv => Nat.div
    end.

  Fixpoint c_eval_nat_exp (e : nat_exp) : state_option c_store nat :=
    match e with
    | NatLit n =>
      ret n
    | NatGet x =>
      s <- get_state ;;
      match s x with Some v => ret v | _ => fail end
    | NatOpApp op n m =>
      n' <- c_eval_nat_exp n ;;
      m' <- c_eval_nat_exp m ;;
      ret (nat_op_to_fun op n' m')
    end.

  Definition c_lift_eval_nat_exp (e : nat_exp) : state_option c_state nat :=
    '(s, h) <- get_state ;;
    match c_eval_nat_exp e s with
    | Some (v, _) => ret v
    | _ => fail
    end.

  Definition rel_op_to_fun (op : rel_op) : nat -> nat -> bool :=
    match op with
    | RelEq  => Nat.eqb
    | RelLte => Nat.leb
    | RelLt  => Nat.ltb
    end.

  Definition bool_op_to_fun (op : bool_op) : bool -> bool -> bool :=
    match op with
    | BoolAnd => andb
    | BoolOr => orb
    end.

  Fixpoint c_eval_bool_exp (e : bool_exp) : state_option c_store bool :=
    match e with
    | BoolLit b =>
      ret b
    | BoolNeg b =>
      b' <- c_eval_bool_exp b ;;
      ret (negb b')
    | BoolRopApp op n1 n2 =>
      n1' <- c_eval_nat_exp n1 ;;
      n2' <- c_eval_nat_exp n2 ;;
      ret (rel_op_to_fun op n1' n2')
    | BoolOpApp op b1 b2 =>
      b1' <- c_eval_bool_exp b1 ;;
      b2' <- c_eval_bool_exp b2 ;;
      ret (bool_op_to_fun op b1' b2')
    end.

  Definition c_lift_eval_bool_exp (e : bool_exp) : state_option c_state bool :=
    '(s, h) <- get_state ;;
    match c_eval_bool_exp e s with
    | Some (v, _) => ret v
    | _ => fail
    end.

  Definition m_heap_load (p : ptr) : state_option c_state chunk :=
    '(_, h) <- get_state ;;
    match contents h p with
    | Some c => ret c
    | _ => fail
    end.

  Definition m_store_lookup (x : pvar) : state_option c_state nat :=
    '(s, _) <- get_state ;;
    match s x with
    | Some v => ret v
    | _ => fail
    end.

  Definition m_store_update (x : pvar) (n : nat) : state_option c_state unit :=
    '(s, h) <- get_state ;;
    put_state (c_store_update s x n, h).

  Definition m_heap_update (p : ptr) (c : chunk) : state_option c_state unit :=
    '(s, h) <- get_state ;;
    put_state (s, c_heap_update h p c).

  Fixpoint c_interp_com (c : command) : state_option c_state unit :=
    match c with
    | ComSkip =>
      ret tt
    | ComCons x e1 e2 =>
      n1 <- c_lift_eval_nat_exp e1 ;;
      n2 <- c_lift_eval_nat_exp e2 ;;
      '(s, h) <- get_state ;;
      put_state (
        c_store_update s x (next h),
        c_heap_alloc h (chunk_make n1 n2)
      )
    | ComSeq c1 c2 =>
      c_interp_com c1 ;;
      c_interp_com c2
    | ComIf e c1 c2 =>
      b <- c_lift_eval_bool_exp e ;;
      c_interp_com (if b then c1 else c2)
    | ComAssign x e =>
      n <- c_lift_eval_nat_exp e ;;
      m_store_update x n
    | ComSetCar x e =>
      p <- m_store_lookup x ;;
      n1 <- c_lift_eval_nat_exp e ;;
      '(_, n2) <- m_heap_load p ;;
      m_heap_update p (chunk_make n1 n2)
    | ComSetCdr x e =>
      p <- m_store_lookup x ;;
      n2 <- c_lift_eval_nat_exp e ;;
      '(n1, _) <- m_heap_load p ;;
      m_heap_update p (chunk_make n1 n2)
    | ComCar x y =>
      p <- m_store_lookup y ;;
      '(n1, _) <- m_heap_load p ;;
      m_store_update x n1
    | ComCdr x y =>
      p <- m_store_lookup y ;;
      '(_, n2) <- m_heap_load p ;;
      m_store_update x n2
    | ComFree x =>
      p <- m_store_lookup x ;;
      '(s, h) <- get_state ;;
      put_state (s, c_heap_dealloc h p)
    | ComWhile _ _ _ =>
      fail
    end.

End Interpreter.
