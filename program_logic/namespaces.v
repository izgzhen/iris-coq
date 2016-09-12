From iris.prelude Require Export countable coPset.
From iris.algebra Require Export base.

Definition namespace := list positive.
Instance namespace_dec (N1 N2 : namespace) : Decision (N1 = N2) := _.
Instance namespace_countable : Countable namespace := _.
Typeclasses Opaque namespace.

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

Instance ndisjoint : Disjoint namespace := λ N1 N2, nclose N1 ⊥ nclose N2.

Section ndisjoint.
  Context `{Countable A}.
  Implicit Types x y : A.

  Lemma ndot_ne_disjoint N x y : x ≠ y → N .@ x ⊥ N .@ y.
  Proof.
    intros Hxy a. rewrite !nclose_eq !elem_coPset_suffixes !ndot_eq.
    intros [qx ->] [qy]. by intros [= ?%encode_inj]%list_encode_suffix_eq.
  Qed.

  Lemma ndot_preserve_disjoint_l N E x : nclose N ⊥ E → nclose (N .@ x) ⊥ E.
  Proof. intros. pose proof (nclose_subseteq N x). set_solver. Qed.

  Lemma ndot_preserve_disjoint_r N E x : E ⊥ nclose N → E ⊥ nclose (N .@ x).
  Proof. intros. by apply symmetry, ndot_preserve_disjoint_l. Qed.

  Lemma ndisj_subseteq_difference N E F :
    E ⊥ nclose N → E ⊆ F → E ⊆ F ∖ nclose N.
  Proof. set_solver. Qed.
End ndisjoint.

(* The hope is that registering these will suffice to solve most goals
of the form [N1 ⊥ N2] and those of the form [N1 ⊆ E ∖ N2 ∖ .. ∖ Nn]. *)
Hint Resolve ndisj_subseteq_difference : ndisj.
Hint Extern 0 (_ ⊥ _) => apply ndot_ne_disjoint; congruence : ndisj.
Hint Resolve ndot_preserve_disjoint_l : ndisj.
Hint Resolve ndot_preserve_disjoint_r : ndisj.

Ltac solve_ndisj := solve [eauto with ndisj].
