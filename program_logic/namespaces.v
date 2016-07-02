From iris.prelude Require Export countable co_pset.
From iris.algebra Require Export base.

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

  Lemma ndot_ne_disjoint N x y : x ≠ y → N .@ x ⊥ N .@ y.
  Proof. intros Hxy. exists (N .@ x), (N .@ y); naive_solver. Qed.

  Lemma ndot_preserve_disjoint_l N1 N2 x : N1 ⊥ N2 → N1 .@ x ⊥ N2.
  Proof.
    intros (N1' & N2' & Hpr1 & Hpr2 & Hl & Hne). exists N1', N2'.
    split_and?; try done; []. by apply suffix_of_cons_r.
  Qed.

  Lemma ndot_preserve_disjoint_r N1 N2 x : N1 ⊥ N2 → N1 ⊥ N2 .@ x .
  Proof. rewrite ![N1 ⊥ _]comm. apply ndot_preserve_disjoint_l. Qed.

  Lemma ndisj_disjoint N1 N2 : N1 ⊥ N2 → nclose N1 ⊥ nclose N2.
  Proof.
    intros (N1' & N2' & [N1'' ->] & [N2'' ->] & Hl & Hne) p; unfold nclose.
    rewrite !elem_coPset_suffixes; intros [q ->] [q' Hq]; destruct Hne.
    by rewrite !list_encode_app !assoc in Hq; apply list_encode_suffix_eq in Hq.
  Qed.

  Lemma ndisj_subseteq_difference N1 N2 E :
    N1 ⊥ N2 → nclose N1 ⊆ E → nclose N1 ⊆ E ∖ nclose N2.
  Proof. intros ?%ndisj_disjoint. set_solver. Qed.
End ndisjoint.

(* The hope is that registering these will suffice to solve most goals
of the form [N1 ⊥ N2] and those of the form [((N1 ⊆ E ∖ N2) ∖ ..) ∖ Nn]. *)
Hint Resolve ndisj_subseteq_difference : ndisj.
Hint Extern 0 (_ ⊥ _) => apply ndot_ne_disjoint; congruence : ndisj.
Hint Resolve ndot_preserve_disjoint_l : ndisj.
Hint Resolve ndot_preserve_disjoint_r : ndisj.

Ltac solve_ndisj := solve [eauto with ndisj].
