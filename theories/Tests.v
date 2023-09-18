From Thesis Require Import AST Interpreter Store Heap.

From Coq Require Import String.

Section Tests.

  Definition empty_state : c_state := (c_store_empty, c_heap_empty).

  Definition X : pvar := "X"%string.
  Definition Y : pvar := "Y"%string.
  Definition Z : pvar := "Z"%string.

  (* Evaluate expressions of type `nat_exp`. *)
  Example interp_nat_program1:
    c_lift_eval_nat_exp (NatLit 5) empty_state = Some (5, empty_state).
  Proof. reflexivity. Qed.
  Example interp_nat_program2:
    c_lift_eval_nat_exp (NatGet X) empty_state = None.
  Proof. reflexivity. Qed.
  Example interp_nat_program3:
    let st := (c_store_update c_store_empty X 1, c_heap_empty) in
    c_lift_eval_nat_exp (NatGet X) st = Some (1, st).
  Proof. reflexivity. Qed.
  Example interp_nat_program4:
    c_lift_eval_nat_exp (NatOpApp NatAdd (NatLit 1) (NatLit 1)) empty_state
    = Some (2, empty_state).
  Proof. reflexivity. Qed.

  Open Scope bool_scope.

  (* Evaluate expressions of type `bin_exp`. *)
  Example interp_bool_program1:
    c_lift_eval_bool_exp (BoolLit true) empty_state
    = Some (true, empty_state).
  Proof. reflexivity. Qed.
  Example interp_bool_program2:
    c_lift_eval_bool_exp (BoolNeg (BoolLit true)) empty_state
    = Some (false, empty_state).
  Proof. reflexivity. Qed.
  Example interp_bool_program3:
    c_lift_eval_bool_exp (BoolRopApp RelLte (NatLit 1) (NatLit 1)) empty_state
    = Some (true, empty_state).
  Proof. reflexivity. Qed.
  Example interp_bool_program4:
    c_lift_eval_bool_exp
      (BoolOpApp BoolOr (BoolLit true) (BoolLit false)) empty_state
    = Some (true, empty_state).
  Proof. reflexivity. Qed.

  (* Evaluate statements of type `command`. *)
  Example interp_com_program1:
    c_interp_com (ComSkip) empty_state = Some (tt, empty_state).
  Proof. reflexivity. Qed.
  Example interp_com_program3:
    c_interp_com (ComAssign X (NatLit 1)) empty_state
    = Some (tt, (c_store_update c_store_empty X 1, c_heap_empty)).
  Proof. reflexivity. Qed.
  Example interp_com_program4:
    c_interp_com
      (ComIf (BoolLit true)
        (ComAssign X (NatLit 1))
        (ComAssign Y (NatLit 2)))
      empty_state
    = Some (tt, (c_store_update c_store_empty X 1, c_heap_empty)).
  Proof. reflexivity. Qed. 
  Example interp_com_program5:
    c_interp_com
      (ComIf (BoolLit false)
        (ComAssign X (NatLit 1))
        (ComAssign Y (NatLit 2)))
      empty_state
    = Some (tt, (c_store_update c_store_empty Y 2, c_heap_empty)).
  Proof. reflexivity. Qed.
  Example interp_com_program6:
    let s := c_store_update c_store_empty X 1 in
    let s' := c_store_update s Y 2 in
    c_interp_com
      (ComSeq (ComAssign X (NatLit 1)) (ComAssign Y (NatLit 2)))
      empty_state
    = Some (tt, (s', c_heap_empty)).
  Proof. reflexivity. Qed.
  Example interp_com_program7:
    let h := c_heap_alloc c_heap_empty (chunk_make 2 3) in
    let s := c_store_update c_store_empty X 0 in
    c_interp_com (ComFree X) (s, h)
    = Some (tt, (s, c_heap_dealloc h 0)).
  Proof. reflexivity. Qed.
  Example interp_com_program8:
    let h := c_heap_alloc c_heap_empty (chunk_make 2 3) in
    c_interp_com (ComCons X (NatLit 2) (NatLit 3)) empty_state
    = Some (tt, (c_store_update c_store_empty X 1, h)).
  Proof. reflexivity. Qed.
  Example interp_com_program9:
    let h := c_heap_alloc c_heap_empty (chunk_make 2 3) in
    let s := c_store_update c_store_empty X 1 in
    c_interp_com (ComCar Y X) (s, h)
    = Some (tt, (c_store_update s Y 2, h)).
  Proof. reflexivity. Qed.
  Example interp_com_program10:
    let h := c_heap_alloc c_heap_empty (chunk_make 2 3) in
    let s := c_store_update c_store_empty X 1 in
    c_interp_com (ComCdr Y X) (s, h)
    = Some (tt, (c_store_update s Y 3, h)).
  Proof. reflexivity. Qed.
  Example interp_com_program11:
    let h := c_heap_alloc c_heap_empty (chunk_make 0 0) in
    let s := c_store_update c_store_empty X 1 in
    c_interp_com (ComSetCar X (NatLit 2)) (s, h)
    = Some (tt, (s, c_heap_update h 1 (chunk_make 2 0))).
  Proof. reflexivity. Qed.
  Example interp_statement_program12:
    let h := c_heap_alloc c_heap_empty (chunk_make 0 0) in
    let s := c_store_update c_store_empty X 1 in
    c_interp_com (ComSetCdr X (NatLit 2)) (s, h)
    = Some (tt, (s, c_heap_update h 1 (chunk_make 0 2))).
  Proof. reflexivity. Qed.

End Tests.