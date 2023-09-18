From Thesis Require Import AST.

From Coq Require Import PeanoNat Arith Lia FunctionalExtensionality.

Section Heap.

  Definition chunk : Type := nat * nat.

  Definition chunk_make (n1 n2 : nat) : chunk := (n1, n2).

  Definition heaplet : Type := ptr -> option chunk.

  Definition heaplet_empty : heaplet := fun _ => None.

  Global Arguments heaplet_empty _ /.

  Definition heaplet_update (h : heaplet) (p : ptr) (c : chunk) : heaplet :=
    fun (q : ptr) => if Nat.eq_dec p q then Some c else h q.

  Global Arguments heaplet_update _ _ _ /.

  Definition heaplet_union (h1 h2 : heaplet) : heaplet :=
    fun (p : ptr) =>
      match h1 p with Some c => Some c | _ => h2 p end.

  Global Arguments heaplet_union _ _ /.

  Definition heaplet_disjoint (h1 h2 : heaplet) : Prop :=
    forall (p : ptr), h1 p = None \/ h2 p = None.

  Global Arguments heaplet_disjoint _ _ /.

  (** For our heap, we ensure an invariant to guarantee that the first pointer,
      i.e. 0, is reserved as null pointer. Furthermore, we keep track of the
      upper bound of the heap. It turns out that in some proofs we need explicit
      information about the allocation status of pointers beyond reach in order
      to show contradictions. Essentially, here we reuse the heaplet type
      definition for the heap content because we already have implementation
      for working with it. *)
  Record c_heap : Type := {
    contents : heaplet ;
    next : ptr ;
    inv : next > 0 ;
    bound : forall (p : ptr), (p >= next) -> contents p = None
  }.

  Program Definition c_heap_empty : c_heap :=
    {| contents := heaplet_empty ; next := 1 |}.

  Program Definition c_heap_alloc (h : c_heap) (c : chunk) : c_heap :=
    {|
      contents := heaplet_update (contents h) (next h) c ;
      next := S (next h)
    |}.
  Next Obligation. lia. Qed.
  Next Obligation.
    destruct h as [contents next inv bound].
    simpl. simpl in H. specialize (bound p).
    destruct (Nat.eq_dec next p); try apply bound; lia.
  Qed.

  Program Definition c_heap_update (h : c_heap)
                                   (p : ptr)
                                   (c : chunk) : c_heap :=
    {|
      contents := if Nat.ltb p (next h)
                  then heaplet_update (contents h) p c
                  else contents h ;
      next := next h
    |}.
  Next Obligation. set (H := inv h). assumption. Qed.
  Next Obligation.
    destruct h as [contents next inv bound].
    simpl. simpl in H. specialize (bound p0 H).
    destruct (Nat.ltb p next) eqn:H1.
    - destruct (Nat.eq_dec p p0).
      + apply Nat.ltb_lt in H1. lia.
      + assumption.
    - assumption.
  Qed.

  Program Definition c_heap_dealloc (h : c_heap) (p : ptr) : c_heap :=
    {|
      contents := if Nat.ltb p (next h)
                  then (fun (q : ptr) =>
                    if Nat.eq_dec p q
                    then None
                    else contents h q)
                  else contents h ;
      next := next h
    |}.
  Next Obligation. set (H := inv h). assumption. Qed.
  Next Obligation.
    destruct h as [contents next inv bound].
    simpl. simpl in H. specialize (bound p0 H).
    destruct (Nat.ltb p next).
    - destruct (Nat.eq_dec p p0).
      + reflexivity.
      + assumption.
    - assumption.
  Qed.

  (** The heap refinement relation. Concretely, the heap h1 refines the heaplet
      h2 if h2 can be obtained from h1 by closing some finite number of chunks.
      It thus states that h1 refines h2 if for every pointer chunk pair in h2,
      that pair is also present in h1. In other words, h1 contains all the
      allocated chunks that h2 contains, making it a refined version of h2. *)
  Definition c_heap_refines (h1 : c_heap) (h2 : heaplet) : Prop :=
    forall (p : ptr),
      (p < next h1) /\ (match contents h1 p with
                        | Some c => h2 p = Some c
                        | _      => True
                        end).

  Arguments c_heap_refines _ _ /.

  Lemma heaplet_extensionality:
    forall (h1 h2 : heaplet),
      (forall (p : ptr), h1 p = h2 p) ->
      h1 = h2.
  Proof.
    intros. apply functional_extensionality. assumption.
  Qed.

  Lemma heaplet_disjoint_sym:
    forall (h1 h2 : heaplet),
      heaplet_disjoint h1 h2 <-> heaplet_disjoint h2 h1.
  Proof.
    intros. cbn.
    split; intros; specialize (H p); apply or_comm; assumption.
  Qed.

  Lemma heaplet_disjoint_empty_l:
    forall (h : heaplet),
      heaplet_disjoint heaplet_empty h.
  Proof.
    cbn. intros. left. reflexivity.
  Qed.

  Lemma heaplet_disjoint_empty_r:
    forall (h : heaplet),
      heaplet_disjoint h heaplet_empty.
  Proof.
    intros. rewrite heaplet_disjoint_sym.
    apply heaplet_disjoint_empty_l.
  Qed.

  Lemma heaplet_union_comm:
    forall (h1 h2 : heaplet),
      heaplet_disjoint h1 h2 ->
      heaplet_union h1 h2 = heaplet_union h2 h1.
  Proof.
    cbn. intros. apply heaplet_extensionality. intros.
    specialize (H p). destruct H, (h1 p), (h2 p); easy.
  Qed.

  Lemma heaplet_union_empty_l:
    forall (h : heaplet),
      heaplet_union heaplet_empty h = h.
  Proof.
    cbn. intros. apply heaplet_extensionality. reflexivity.
  Qed.

  Lemma heaplet_union_empty_r:
    forall (h : heaplet),
      heaplet_union h heaplet_empty = h.
  Proof.
    intros.
    rewrite heaplet_union_comm.
    - apply heaplet_union_empty_l.
    - apply heaplet_disjoint_empty_r.
  Qed.

End Heap.

Notation "h1 '<|' h2" := (c_heap_refines h1 h2) (at level 70).
