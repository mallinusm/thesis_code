From Thesis Require Import
  AST Monad Store Shallow Heap
  Separation WP Interpreter.

From Coq Require Import PeanoNat Lia.

From Coq Require Import FunctionalExtensionality.

Section Soundness.

  Definition wp_com_interp (c : command)
                           (Q : unit -> predicate)
                           (s : c_store)
                           (hli : heaplet) : Prop :=
    forall (s' : c_store)
           (hi ho : c_heap),
      c_interp_com c (s, hi) = Some (tt, (s', ho)) ->
      hi <| hli ->
      exists (hlo : heaplet),
        Q tt s' hlo /\ ho <| hlo.

  Global Arguments wp_com_interp _ _ _ _ /.

  Lemma soundness_skip_com:
    forall (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com ComSkip Q s h ->
      wp_com_interp ComSkip Q s h.
  Proof.
    cbn. intros. inversion H0. subst.
    exists h. split; assumption.
  Qed.

  Lemma soundness_seq_com:
    forall (c1 c2 : command)
           (IHc1 : forall (Q : unit -> predicate)
                          (s : c_store)
                          (h : heaplet),
            c_wp_com c1 Q s h ->
            wp_com_interp c1 Q s h)
           (IHc2 : forall (Q : unit -> predicate)
                          (s : c_store)
                          (h : heaplet),
            c_wp_com c2 Q s h ->
            wp_com_interp c2 Q s h)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComSeq c1 c2) Q s h ->
      wp_com_interp (ComSeq c1 c2) Q s h.
  Proof.
    cbn. intros.
    specialize (IHc1 (fun _ => c_wp_com c2 Q) s h H).
    destruct (c_interp_com c1) eqn:Hc1; try discriminate.
    destruct p, u, c. specialize (IHc1 c hi c0 Hc1 H1).
    destruct IHc1 as (h1 & H2 & H3).
    specialize (IHc2 Q c h1 H2 s' c0 ho H0 H3).
    assumption.
  Qed.

  Arguments h_ex _ /.
  Arguments h_and _ _ /.
  Arguments h_pure _ /.
  Arguments assign _ _ _ _ _ /.
  Arguments c_store_update _ _ _ /.
  Arguments angelic_branch _ /.
  Arguments c_wp_nat_exp _ /.

  Lemma soundness_assign_com:
    forall (x : pvar)
           (e : nat_exp)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComAssign x e) Q s h ->
      wp_com_interp (ComAssign x e) Q s h.
  Proof.
    cbn. intros.
    destruct (c_eval_nat_exp e s); try discriminate.
    destruct p.
    destruct H as (? & H2 & ?).
    hnf in H2. inversion H0. subst.
    exists h. split; assumption.
  Qed.

  Lemma soundness_cons_com:
    forall (x : pvar)
           (e1 e2 : nat_exp)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComCons x e1 e2) Q s h ->
      wp_com_interp (ComCons x e1 e2) Q s h.
  Proof.
    cbn. intros.
    destruct (c_eval_nat_exp e1 s); try discriminate. destruct p.
    destruct (c_eval_nat_exp e2 s); try discriminate. destruct p.
    hnf in H. specialize (H (next hi)). set (H_inv := inv hi).
    specialize (H H_inv). destruct H as (h1 & h2 & H6 & H7 & H8 & H9).
    hnf in H6. inversion H0. set (H_c := (n, n0)).
    specialize (H7 (heaplet_update heaplet_empty (next hi) H_c)).
    subst. rewrite heaplet_union_empty_l in H1.
    specialize (H7 (heap_refines_disjoint_update hi h2 H_c H1) eq_refl).
    rewrite (heap_refines_union_update hi h2 H_c H1) in H7.
    exists h2. split.
    + assumption.
    + (* exact (heap_refines_alloc hi h2 H_c H1). *)
      unfold assign in H7. cbn in H8.
      unfold c_heap_refines in H1.
      unfold c_heap_refines. intros.
      specialize (H1 p). destruct H1.
      specialize (H8 p). split.
      * cbn. lia.
      * cbn.
        destruct (Nat.eq_dec (next hi) p) eqn:H10,
          (contents hi p) eqn:H11, (h2 p) eqn:H12, H8; try easy; lia.
  Qed.

  Global Arguments lookup _ /.

  Lemma soundness_free_com:
    forall (x : pvar)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComFree x) Q s h ->
      wp_com_interp (ComFree x) Q s h.
  Proof.
    cbn. intros.
    destruct (s x); try discriminate. hnf in H.
    unfold h_star, h_contains, h_wand, h_emp in H.
    unfold h_ex, h_pto in H.
    destruct H as (h1 & h2 & H2 & H3 & H4 & H5). destruct H2.
    destruct x0.
    specialize (H3 heaplet_empty (heaplet_disjoint_empty_r h2) eq_refl).
    rewrite heaplet_union_empty_r in H3. inversion H0. subst.
    exists h2. split.
    - assumption.
    - set (H_c := chunk_make n0 n1).
      (* 
      exact (heap_refines_union_dealloc hi h2 n H_c H1).
      *)
      unfold c_heap_refines. intros.
      unfold c_heap_refines in H1. specialize (H1 p). destruct H1.
      split.
      + cbn. assumption.
      + cbn. cbn in H1. cbn in H4. specialize (H4 p).
        destruct (next hi) eqn:H10,
          (contents hi p) eqn:H11,
          (Nat.eq_dec n p) eqn:H12,
          H4; try easy;
          destruct (Nat.leb n p0) eqn:H13;
          try rewrite H12;
          try rewrite H11; auto.
        * apply Nat.leb_gt in H13. lia.
  Qed.

  Lemma soundness_set_car_com:
    forall (x : pvar)
           (e : nat_exp)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComSetCar x e) Q s h ->
      wp_com_interp (ComSetCar x e) Q s h.
  Proof.
    cbn. intros.
    destruct (s x) eqn:H2; try discriminate.
    destruct (c_eval_nat_exp e s) eqn:H3; try discriminate.
    destruct p eqn:H4.
    destruct (contents hi n) eqn:H5; try discriminate.
    destruct c0 eqn:H6.
    destruct H as (n3 & n4 & h2 & h3 & H7 & H8 & H9 & H10).
    unfold h_pto in H8.
    specialize (H8
     (heaplet_update heaplet_empty n (chunk_make n0 n4))).
    inversion H0. subst.
    exists (heaplet_union h3
    (heaplet_update heaplet_empty n (chunk_make n0 n4))).
    split.
    - apply H8.
      + cbn. intros. cbn in H9. specialize (H9 p).
        destruct (Nat.eq_dec n p) eqn:H13, H9; auto.
        * subst. unfold h_pto in H7.
          rewrite H7 in H. cbn in H.
          rewrite H13 in H. discriminate.
      + reflexivity.
    - cbn. unfold c_heap_refines. intros.
      cbn in H9. specialize (H9 p).
      unfold c_heap_refines in H1. specialize (H1 p).
      destruct H1. split.
      + cbn. assumption.
      + cbn. cbn in H1. unfold h_pto in H7.
        subst. cbn in H9. cbn in H1.
        destruct (next hi) eqn:H18,
          (contents hi p) eqn:H19,
          (Nat.eq_dec n p) eqn:H20,
          (h3 p) eqn:H21,
          H9; try easy;
          destruct (Nat.leb n p0) eqn:H22;
          try rewrite H20;
          try rewrite H19; try easy.
          * subst. apply Nat.leb_le in H22.
            rewrite H5 in H19. inversion H19.
            subst. inversion H1. reflexivity.
          * subst. apply Nat.leb_gt in H22. lia.
          * subst. rewrite H5 in H19. discriminate.
  Qed.

  (** This proof is identical to the previous one for setting the car. *)
  Lemma soundness_set_cdr_com:
    forall (x : pvar)
           (e : nat_exp)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComSetCdr x e) Q s h ->
      wp_com_interp (ComSetCdr x e) Q s h.
  Proof.
    cbn. intros.
    destruct (s x) eqn:H2; try discriminate.
    destruct (c_eval_nat_exp e s) eqn:H3; try discriminate.
    destruct p eqn:H4.
    destruct (contents hi n) eqn:H5; try discriminate.
    destruct c0 eqn:H6.
    destruct H as (n3 & n4 & h2 & h3 & H7 & H8 & H9 & H10).
    unfold h_pto in H8.
    specialize (H8
     (heaplet_update heaplet_empty n (chunk_make n3 n0))).
    inversion H0. subst.
    exists (heaplet_union h3
      (heaplet_update heaplet_empty n (chunk_make n3 n0))).
    split.
    - apply H8.
      + cbn. intros. cbn in H9. specialize (H9 p).
        destruct (Nat.eq_dec n p) eqn:H13, H9; auto.
        * subst. unfold h_pto in H7.
          rewrite H7 in H. cbn in H.
          rewrite H13 in H. discriminate.
      + reflexivity.
    - cbn. unfold c_heap_refines. intros.
      cbn in H9. specialize (H9 p).
      unfold c_heap_refines in H1. specialize (H1 p).
      destruct H1. split.
      + cbn. assumption.
      + cbn. cbn in H1. unfold h_pto in H7.
        subst. cbn in H9. cbn in H1.
        destruct (next hi) eqn:H18,
          (contents hi p) eqn:H19,
          (Nat.eq_dec n p) eqn:H20,
          (h3 p) eqn:H21,
          H9; try easy;
          destruct (Nat.leb n p0) eqn:H22;
          try rewrite H20;
          try rewrite H19; try easy.
          * subst. apply Nat.leb_le in H22.
            rewrite H5 in H19. inversion H19.
            subst. inversion H1. reflexivity.
          * subst. apply Nat.leb_gt in H22. lia.
          * subst. rewrite H5 in H19. discriminate.
  Qed.

  Arguments c_store_update _ _ _ _ /.

  (** TODO cleanup *)
  Lemma soundness_car_com:
    forall (x y : pvar)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComCar x y) Q s h ->
      wp_com_interp (ComCar x y) Q s h.
  Proof.
    cbn. intros.
    destruct (s y); try discriminate.
    destruct (contents hi n) eqn:H4; try discriminate.
    destruct c.
    unfold h_ex, h_star, h_pto, h_wand, assign in H.
    destruct H as (n2 & n3 & h1 & h2 & H5 & H6 & H7 & H8).
    apply heaplet_disjoint_sym in H7.
    specialize (H6 h1 H7 H5).
    rewrite (heaplet_union_comm h2 h1 H7) in H6.
    rewrite <- H8 in H6. inversion H0.
    exists h. split.
    + subst. unfold c_heap_refines in H1.
      specialize (H1 n). destruct H1.
      rewrite H4 in H1. cbn in H1.
      destruct (Nat.eq_dec n n) eqn:H9.
      * subst. inversion H1. subst. apply H6.
      * easy.
    + subst. assumption.
  Qed.

  Lemma soundness_cdr_com:
    forall (x y : pvar)
          (Q : unit -> predicate)
          (s : c_store)
          (h : heaplet),
      c_wp_com (ComCdr x y) Q s h ->
      wp_com_interp (ComCdr x y) Q s h.
  Proof.
    cbn. intros. 
    destruct (s y); try discriminate.
    destruct (contents hi n) eqn:H4; try discriminate.
    destruct c.
    (** TODO Remove unfolding ... *)
    unfold h_ex, h_star, h_pto, h_wand, assign in H.
    destruct H as (n2 & n3 & h1 & h2 & H5 & H6 & H7 & H8).
    apply heaplet_disjoint_sym in H7.
    specialize (H6 h1 H7 H5).
    rewrite (heaplet_union_comm h2 h1 H7) in H6.
    rewrite <- H8 in H6. inversion H0.
    exists h. split.
    + subst. unfold c_heap_refines in H1.
      specialize (H1 n). destruct H1.
      rewrite H4 in H1. cbn in H1.
      destruct (Nat.eq_dec n n) eqn:H9.
      * subst. inversion H1. subst. apply H6.
      * easy.
    + subst. assumption.
  Qed.

  Arguments c_wp_bool_exp _ /.

  Lemma soundness_if_com:
    forall (e : bool_exp)
           (c1 c2 : command)
           (IHc1 : forall (Q : unit -> predicate)
                          (s : c_store)
                          (h : heaplet),
            c_wp_com c1 Q s h ->
            wp_com_interp c1 Q s h)
           (IHc2 : forall (Q : unit -> predicate)
                          (s : c_store)
                          (h : heaplet),
            c_wp_com c2 Q s h ->
            wp_com_interp c2 Q s h)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com (ComIf e c1 c2) Q s h ->
      wp_com_interp (ComIf e c1 c2) Q s h.
  Proof.
    cbn. intros.
    destruct (c_eval_bool_exp e s) eqn:H2; try discriminate.
    destruct p, H, b.
    + specialize (H eq_refl).
      specialize (IHc1 Q s h H s' hi ho H0 H1).
      assumption.
    + specialize (H3 eq_refl).
      specialize (IHc2 Q s h H3 s' hi ho H0 H1).
      assumption.
  Qed.

  (** A soundness proof for the shallow specification monad. *)
  Theorem soundness_wp_sta:
    forall (c : command)
           (Q : unit -> predicate)
           (s : c_store)
           (h : heaplet),
      c_wp_com c Q s h ->
      wp_com_interp c Q s h.
  Proof.
    intros c. induction c.
    - (* ComSkip *)
      apply soundness_skip_com.
    - (* Assign *)
      apply soundness_assign_com.
    - (* ComSeq *)
      apply (soundness_seq_com c1 c2 IHc1 IHc2).
    - (* If *)
      apply (soundness_if_com b c1 c2 IHc1 IHc2).
    - (* While *)
      admit.
    - (* Cons *)
      apply soundness_cons_com.
    - (* Delete *)
      apply soundness_free_com.
    - (* Car *)
      apply soundness_car_com.
    - (* Cdr *)
      apply soundness_cdr_com.
    - (* SetCar *)
      apply soundness_set_car_com.
    - (* SetCdr *)
      apply soundness_set_cdr_com.
  Admitted.

End Soundness.
