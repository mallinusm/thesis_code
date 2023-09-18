From Thesis Require Import AST.

Section Store.

  Definition c_store : Type := pvar -> option nat.

  Definition c_store_empty : c_store := fun _ => None.

  Definition c_store_update (s : c_store) (x : pvar) (v : nat) : c_store :=
    fun (y : pvar) => if String.eqb x y then Some v else s y.

  Global Arguments c_store_update _ _ _ _ /.

End Store.
