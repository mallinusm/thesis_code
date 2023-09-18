From Thesis Require Import AST Store Separation Interpreter WP Semi.

Section Studies.

  Arguments c_vcgen _ _ _ /.
  Arguments c_wp_nat_exp _ _ _ /.

  Import Separation.proofmode.
  Import Interpreter. (* Reimport for pvar notations. *)

  Definition swap_com (x y : pvar) : command :=
    ComSeq
      (ComAssign x (NatOpApp NatAdd (NatGet x) (NatGet y)))
      (ComSeq
        (ComAssign y (NatOpApp NatSub (NatGet x) (NatGet y)))
         (ComAssign x (NatOpApp NatSub (NatGet x) (NatGet y)))).

  Definition X : pvar := "X"%string.
  Definition Y : pvar := "Y"%string.

  Theorem verify_swap:
    forall (n m : nat),
      c_vcgen
        (fun (s : c_store) =>
          match s X, s Y with
          | Some x, Some y => l_and (l_pure (x = n)) (l_pure (y = m))
          | _, _ => l_bottom
          end)
        (swap_com X Y)
        (fun (s : c_store) =>
          match s X, s Y with
          | Some x, Some y => l_and (l_pure (x = m)) (l_pure (y = n))
          | _, _ => l_bottom
          end).
  Proof.
    cbn.
    intros.
    destruct (s X), (s Y); auto.
    iIntros "[%H1 %H2]".
    iExists (n0 + n1).
    iSplitR; [auto|].
    iExists (n0 + n1 - n1).
    iSplitR; [auto|].
    iExists m.
    repeat iSplit; iPureIntro; lia.
  Qed.

  Theorem verify_cons:
    forall (n : nat) (p : ptr) (l : list nat),
      c_vcgen
        (fun _ => l_list_at p l)
        (ComCons Y (NatLit n) (NatLit p))
        (fun (s : c_store) =>
          match s Y with
          | Some q => l_list_at q (n :: l)
          | _ => l_bottom
        end).
  Proof.
    cbn.
    intros.
    iIntros "Hp %q %Hq".
    iSplitR; auto.
    iIntros "Hq".
    iSplit.
    { iPureIntro. lia. }
    iExists p.
    iFrame.
  Qed.

End Studies.

Section Examples.

  Import Separation.proofmode.

  (** We will be using these logic variables for later examples. *)
  Definition M : lvar := VarNum "M".
  Definition N : lvar := VarNum "N".

  (** Swap program and symbolic contract. *)
  Definition swap_program : program :=
    {|
      pre := Star (Equal (SymPVar X) (SymLVar M))
              (Equal (SymPVar Y) (SymLVar N)) ;
      com := swap_com X Y ;
      post := Star (Equal (SymPVar X) (SymLVar N))
                (Equal (SymPVar Y) (SymLVar M))
    |}.

  (** Verification of the swap program, this time around using a symbolic
    contract. *)
  Lemma sc_swap_example:
    sc_vcgen swap_program.
  Proof.
    cbn. iStartProof. iIntros (n n0 n1 n2 H1 H2).
    iExists (n1 + n2).
    iSplit; [auto|].
    iExists n1.
    iSplit.
    - iPureIntro. lia.
    - iExists n2. iSplit.
      + iPureIntro. lia.
      + repeat iSplit; auto.
  Qed.

  (** The second example is with Separation logic connectives. *)

  Definition P1 : pvar := "P1"%string.  (* pointer to XS *)
  Definition P2 : pvar := "P2"%string.  (* new pointer after cons *)
  Definition XS : lvar := VarList "XS". (* some list *)
  Definition V : pvar := "V"%string.    (* value to add to XS *)

  Definition cons_program : program :=
    {|
      pre := ListAt (SymPVar P1) (SymLVar XS) ;
      (** pvar P1 points to lvar XS *)

      com := ComCons P2 (NatGet V) (NatGet P1) ;
      (** pvar P2 points to (cons V XS) *)

      post := ListAt (SymPVar P2) (SymCons (SymPVar V) (SymLVar XS))
      (** pvar P2 points to (V :: XS) *)
    |}.

  Lemma sc_verify_cons:
    sc_vcgen cons_program.
  Proof.
    cbn. iStartProof. iIntros ([|xs] p x y).
    - iIntros "Hp".
      iIntros (q Hq).
      iSplitR; auto.
      iIntros "Hq".
      repeat iSplit; auto.
      iPureIntro. lia.
    - cbn.
      iIntros "Hp".
      iIntros (q Hq).
      iSplitR; auto.
      iIntros "Hq".
      repeat iSplit; auto.
      iPureIntro. lia.
      iExists p.
      iFrame.
  Qed.

  Definition LIST : lvar := VarList "LIST". (** full list *)
  Definition REF : pvar := "REF"%string. (** ref to current list segment *)
  Definition OUT : pvar := "OUT"%string. (** accumulator *)

  Definition LISTSEG : lvar := VarList "LISTSEG".
  Definition CAR : lvar := VarNum "CAR"%string.

  Definition INV : assertion :=
  Exist LISTSEG
    (*
    (Star
      (Exist CAR (Pto (SymPVar REF) (SymLVar CAR) (SymLVar LISTSEG)))
    *)
      (Equal
        (SymApp NatAdd (SymLength (SymLVar LISTSEG)) (SymPVar OUT))
        (SymLength (SymLVar LIST))).

  Definition CURRENT : pvar := "CURRENT"%string.

  Definition list_length (REF OUT : pvar) : command :=
  ComSeq
    (ComAssign OUT (NatLit 0))
    (ComSeq
      (ComAssign CURRENT (NatGet REF))
      (ComWhile INV (BoolNeg (BoolRopApp RelEq (NatGet REF) (NatLit 0)))
        (ComSeq
          (ComAssign OUT (NatOpApp NatAdd (NatGet OUT) (NatLit 1)))
          (ComCdr CURRENT CURRENT)))).

  Definition list_length_program : program :=
  {|
    pre := ListAt (SymPVar REF) (SymLVar LIST) ;

    com := list_length REF OUT ;

    post := Equal (SymPVar OUT) (SymLength (SymLVar LIST))
  |}.

  Lemma verify_list_length:
  sc_vcgen list_length_program.
  Proof.
  cbn. iStartProof. iIntros ([|n'] n).
  - iIntros (m).
    iIntros "H".
    iExists 0.
    iSplitR; auto.
  - cbn.
    iIntros (m).
    iIntros "H".
    iExists 0.
    iSplitR; auto.
    iExists n.
    iSplitR; auto.
    iExists (cons n' l).
    auto.
  Qed.

End Examples.
