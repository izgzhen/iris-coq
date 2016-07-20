From iris.prelude Require Export countable co_pset.
From iris.algebra Require Export base.

Definition namespace := list positive.
Definition nroot : namespace := nil.

Definition ndot_def `{Countable A} (N : namespace) (x : A) : namespace :=
  encode x :: N.
Definition ndot_aux : { x | x = @ndot_def }. by eexists. Qed.
Definition ndot {A A_dec A_count}:= proj1_sig ndot_aux A A_dec A_count.
Definition ndot_eq : @ndot = @ndot_def := proj2_sig ndot_aux.

Definition nclose_def (N : namespace) : coPset := coPset_suffixes (encode N).
Definition nclose_aux : { x | x = @nclose_def }. by eexists. Qed.
Coercion nclose := proj1_sig nclose_aux.
Definition nclose_eq : @nclose = @nclose_def := proj2_sig nclose_aux.

Infix ".@" := ndot (at level 19, left associativity) : C_scope.
Notation "(.@)" := ndot (only parsing) : C_scope.

Instance ndot_inj `{Countable A} : Inj2 (=) (=) (=) (@ndot A _ _).
Proof. intros N1 x1 N2 x2; rewrite !ndot_eq=> ?; by simplify_eq. Qed.
Lemma nclose_nroot : nclose nroot = ⊤.
Proof. rewrite nclose_eq. by apply (sig_eq_pi _). Qed.
Lemma encode_nclose N : encode N ∈ nclose N.
Proof.
  rewrite nclose_eq.
  by apply elem_coPset_suffixes; exists xH; rewrite (left_id_L _ _).
Qed.
Lemma nclose_subseteq `{Countable A} N x : nclose (N .@ x) ⊆ nclose N.
Proof.
  intros p; rewrite nclose_eq /nclose !ndot_eq !elem_coPset_suffixes.
  intros [q ->]. destruct (list_encode_suffix N (ndot_def N x)) as [q' ?].
  { by exists [encode x]. }
  by exists (q ++ q')%positive; rewrite <-(assoc_L _); f_equal.
Qed.
Lemma ndot_nclose `{Countable A} N x : encode (N .@ x) ∈ nclose N.
Proof. apply nclose_subseteq with x, encode_nclose. Qed.
Lemma nclose_infinite N : ¬set_finite (nclose N).
Proof. rewrite nclose_eq. apply coPset_suffixes_infinite. Qed.

Instance ndisjoint : Disjoint namespace := λ N1 N2,
  ∃ N1' N2', N1' `suffix_of` N1 ∧ N2' `suffix_of` N2 ∧
             length N1' = length N2' ∧ N1' ≠ N2'.
Typeclasses Opaque ndisjoint.

Section ndisjoint.
  Context `{Countable A}.
  Implicit Types x y : A.

  Global Instance ndisjoint_symmetric : Symmetric ndisjoint.
  Proof. intros N1 N2. rewrite /disjoint /ndisjoint; naive_solver. Qed.

  Lemma ndot_ne_disjoint N x y : x ≠ y → N .@ x ⊥ N .@ y.
  Proof. intros. exists (N .@ x), (N .@ y); rewrite ndot_eq; naive_solver. Qed.

  Lemma ndot_preserve_disjoint_l N1 N2 x : N1 ⊥ N2 → N1 .@ x ⊥ N2.
  Proof.
    intros (N1' & N2' & Hpr1 & Hpr2 & Hl & Hne). exists N1', N2'.
    split_and?; try done; []. rewrite ndot_eq. by apply suffix_of_cons_r.
  Qed.

  Lemma ndot_preserve_disjoint_r N1 N2 x : N1 ⊥ N2 → N1 ⊥ N2 .@ x .
  Proof. intros. by apply symmetry, ndot_preserve_disjoint_l. Qed.

  Lemma ndisj_disjoint N1 N2 : N1 ⊥ N2 → nclose N1 ⊥ nclose N2.
  Proof.
    intros (N1' & N2' & [N1'' ->] & [N2'' ->] & Hl & Hne) p.
    rewrite nclose_eq /nclose.
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
