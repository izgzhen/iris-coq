From prelude Require Export countable co_pset.
From algebra Require Export base.

Definition namespace := list positive.
Definition nroot : namespace := nil.
Definition ndot `{Countable A} (N : namespace) (x : A) : namespace :=
  encode x :: N.
Coercion nclose (N : namespace) : coPset := coPset_suffixes (encode N).

Infix ".@" := ndot (at level 19, left associativity) : C_scope.
Notation "(.@)" := ndot (only parsing) : C_scope.

Instance ndot_inj `{Countable A} : Inj2 (=) (=) (=) (@ndot A _ _).
Proof. by intros N1 x1 N2 x2 ?; simplify_eq. Qed.
Lemma nclose_nroot : nclose nroot = ⊤.
Proof. by apply (sig_eq_pi _). Qed.
Lemma encode_nclose N : encode N ∈ nclose N.
Proof. by apply elem_coPset_suffixes; exists xH; rewrite (left_id_L _ _). Qed.
Lemma nclose_subseteq `{Countable A} N x : nclose (N .@ x) ⊆ nclose N.
Proof.
  intros p; rewrite /nclose !elem_coPset_suffixes; intros [q ->].
  destruct (list_encode_suffix N (N .@ x)) as [q' ?]; [by exists [encode x]|].
  by exists (q ++ q')%positive; rewrite <-(assoc_L _); f_equal.
Qed.
Lemma ndot_nclose `{Countable A} N x : encode (N .@ x) ∈ nclose N.
Proof. apply nclose_subseteq with x, encode_nclose. Qed.

Instance ndisjoint : Disjoint namespace := λ N1 N2,
  ∃ N1' N2', N1' `suffix_of` N1 ∧ N2' `suffix_of` N2 ∧
             length N1' = length N2' ∧ N1' ≠ N2'.
Typeclasses Opaque ndisjoint.

Section ndisjoint.
  Context `{Countable A}.
  Implicit Types x y : A.

  Global Instance ndisjoint_comm : Comm iff ndisjoint.
  Proof. intros N1 N2. rewrite /disjoint /ndisjoint; naive_solver. Qed.

  Lemma ndot_ne_disjoint N (x y : A) : x ≠ y → N .@ x ⊥ N .@ y.
  Proof. intros Hxy. exists (N .@ x), (N .@ y); naive_solver. Qed.

  Lemma ndot_preserve_disjoint_l N1 N2 x : N1 ⊥ N2 → N1 .@ x ⊥ N2.
  Proof.
    intros (N1' & N2' & Hpr1 & Hpr2 & Hl & Hne). exists N1', N2'.
    split_and?; try done; []. by apply suffix_of_cons_r.
  Qed.

  Lemma ndot_preserve_disjoint_r N1 N2 x : N1 ⊥ N2 → N1 ⊥ N2 .@ x .
  Proof. rewrite ![N1 ⊥ _]comm. apply ndot_preserve_disjoint_l. Qed.

  Lemma ndisj_disjoint N1 N2 : N1 ⊥ N2 → nclose N1 ∩ nclose N2 = ∅.
  Proof.
    intros (N1' & N2' & [N1'' ->] & [N2'' ->] & Hl & Hne).
    apply elem_of_equiv_empty_L=> p; unfold nclose.
    rewrite elem_of_intersection !elem_coPset_suffixes; intros [[q ->] [q' Hq]].
    rewrite !list_encode_app !assoc in Hq.
    by eapply Hne, list_encode_suffix_eq.
  Qed.
End ndisjoint.

(* This tactic solves goals about inclusion and disjointness
   of masks (i.e., coPsets) with set_solver, taking
   disjointness of namespaces into account. *)
(* TODO: This tactic is by far now yet as powerful as it should be.
   For example, given N1 ⊥ N2, it should be able to solve
   nclose (ndot N1 x) ∩ N2 ≡ ∅. It should also solve
   (ndot N x) ∩ (ndot N y) ≡ ∅ if x ≠ y is in the context or
   follows from [discriminate]. *)
Ltac set_solver_ndisj :=
  repeat match goal with
         (* TODO: Restrict these to have type namespace *)
         | [ H : (?N1 ⊥ ?N2) |-_ ] => apply ndisj_disjoint in H
         end;
  set_solver.
(* TODO: restrict this to match only if this is ⊆ of coPset *)
Hint Extern 500 (_ ⊆ _) => set_solver_ndisj : ndisj.
(* The hope is that registering these will suffice to solve most goals
   of the form N1 ⊥ N2.
   TODO: Can this prove x ≠ y if discriminate can? *)
Hint Resolve ndot_ne_disjoint : ndisj.
Hint Resolve ndot_preserve_disjoint_l : ndisj.
Hint Resolve ndot_preserve_disjoint_r : ndisj.
