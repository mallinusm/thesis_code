From Coq Require Import Lia.

From Thesis Require Import AST Store Heap Monad
  Interpreter Shallow Separation.

Section WP.

  Definition c_wp_nat_exp (e : nat_exp) : M nat :=
    fun (Q : nat -> predicate) (s : c_store) =>
      match c_eval_nat_exp e s with
      | Some (v, _) => Q v s
      | _ => l_bottom
      end.

  Definition c_wp_bool_exp (e : bool_exp) : M bool :=
    fun (Q : bool -> predicate) (s : c_store) =>
      match c_eval_bool_exp e s with
      | Some (v, _) => Q v s
      | _ => l_bottom
      end.

  Fixpoint c_wp_com (c : command) : M unit :=
    match c with
    | ComSkip =>
      ret tt
    | ComAssign x e =>
      n <- c_wp_nat_exp e ;;
      n' <- angelic_branch ;;
      _ <- assert (n = n') ;;
      assign x n'
    | ComSeq c1 c2 =>
      c_wp_com c1 ;;
      c_wp_com c2
    | ComIf b c1 c2 =>
      b' <- c_wp_bool_exp b ;;
      match_bool_demonic_choice b' (c_wp_com c1) (c_wp_com c2)
    | ComCons x e1 e2 =>
      n1 <- c_wp_nat_exp e1 ;;
      n2 <- c_wp_nat_exp e2 ;;
      p <- demonic_branch ;;
      _ <- assume (p > 0) ;;
      _ <- consume l_emp ;;
      _ <- produce (p |-> (n1, n2)) ;;
      assign x p
    | ComFree x =>
      p <- lookup x ;;
      consume (l_contains p) ;;
      produce l_emp
    | ComCar x y =>
      p <- lookup y ;;
      n1 <- angelic_branch ;;
      n2 <- angelic_branch ;;
      _ <- consume (p |-> (n1, n2)) ;;
      _ <- produce (p |-> (n1, n2)) ;;
      assign x n1
    | ComCdr x y =>
      p <- lookup y ;;
      n1 <- angelic_branch ;;
      n2 <- angelic_branch ;;
      _ <- consume (p |-> (n1, n2)) ;;
      _ <- produce (p |-> (n1, n2)) ;;
      assign x n2
    | ComSetCar x e =>
      p <- lookup x ;;
      n1' <- c_wp_nat_exp e ;;
      n1 <- angelic_branch ;;
      n2 <- angelic_branch ;;
      _ <- consume (p |-> (n1, n2)) ;;
      produce (p |-> (n1', n2))
    | ComSetCdr x e =>
      p <- lookup x ;;
      n2' <- c_wp_nat_exp e ;;
      n1 <- angelic_branch ;;
      n2 <- angelic_branch ;;
      _ <- consume (p |-> (n1, n2)) ;;
      produce (p |-> (n1, n2'))
    | ComWhile _ _ _ =>
      error
    end.

  Definition c_vcgen (P : predicate) (c : command) (Q : predicate) : Type :=
    forall (s : c_store),
      P s |- c_wp_com c (fun _ => Q) s.

End WP.
