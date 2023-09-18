From Coq Require Import String.

Section AST.

  Definition pvar : Type := string.

  Definition ptr : Type := nat.

  Inductive nat_op : Type := NatAdd | NatSub | NatMul | NatDiv.

  (** Represent (universal) logic variables. We shall pick these using the
      demonic branches in the specification monad. We type these in order to
      know when we need to select a `nat` or `list nat` during the
      initialisation phase of the logic environment. *)
  Inductive lvar : Type := VarNum (x : string) | VarList (x : string).

  Inductive lval : Type := LogNum (n : nat) | LogList (xs : list nat).

  (** Symbolic terms. *)
  Inductive sterm : Type :=
    | SymConst : lval -> sterm
    | SymPVar : pvar -> sterm
    | SymLVar : lvar -> sterm
    | SymApp : nat_op -> sterm -> sterm -> sterm
    | SymCons : sterm -> sterm -> sterm
    | SymLength : sterm -> sterm
    | SymNil : sterm.

  (** Deep contracts. *)
  Inductive assertion : Type :=
    | Equal : sterm -> sterm -> assertion
    | Star : assertion -> assertion -> assertion
    | Pto : sterm -> sterm -> sterm -> assertion
    | ListAt : sterm -> sterm -> assertion
    | Or : assertion -> assertion -> assertion
    | Exist : lvar -> assertion -> assertion.

  (** This expression produces a natural number when evaluated. *)
  Inductive nat_exp : Type :=
    | NatLit : nat -> nat_exp                             (* nat literal *)
    | NatGet : pvar -> nat_exp                            (* variable deref *)
    | NatOpApp : nat_op -> nat_exp -> nat_exp -> nat_exp. (* binary operation *)

  Inductive rel_op : Type := RelEq | RelLte | RelLt.

  Inductive bool_op : Type := BoolAnd | BoolOr.

  (** This expression produces a boolean value when evaluated. *)
  Inductive bool_exp : Type :=
    | BoolLit : bool -> bool_exp                              (* bool literal *)
    | BoolNeg : bool_exp -> bool_exp                          (* bool negation *)
    | BoolOpApp : bool_op -> bool_exp -> bool_exp -> bool_exp (* binop (bool) *)
    | BoolRopApp : rel_op -> nat_exp -> nat_exp -> bool_exp.  (* relop (nat) *)

  (** This statement does not produce a value when evaluated. Instead, it is
      executed for its potential side effect on state, i.e. local store and
      heap. *)
  Inductive command : Type :=
    | ComSkip : command                                 (* no effects *)
    | ComAssign : pvar -> nat_exp -> command            (* assignment *)
    | ComSeq : command -> command -> command            (* sequencing *)
    | ComIf : bool_exp -> command -> command -> command (* conditional *)
    | ComWhile : assertion -> bool_exp -> command -> command (* iteration *)
    | ComCons : pvar -> nat_exp -> nat_exp -> command   (* allocate cons cell *)
    | ComFree : pvar -> command                         (* release cons cell *)
    | ComCar : pvar -> pvar -> command                  (* dereference car *)
    | ComCdr : pvar -> pvar -> command                  (* dereference cdr *)
    | ComSetCar : pvar -> nat_exp -> command            (* destructive set car *)
    | ComSetCdr : pvar -> nat_exp -> command.           (* destructive set cdr *)

End AST.
