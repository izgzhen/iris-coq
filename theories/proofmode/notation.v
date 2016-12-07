From iris.proofmode Require Import coq_tactics environments.
From iris.prelude Require Export strings.
Set Default Proof Using "Type".

Delimit Scope proof_scope with env.
Arguments Envs _ _%proof_scope _%proof_scope.
Arguments Enil {_}.
Arguments Esnoc {_} _%proof_scope _%string _%uPred_scope.

Notation "​" := Enil (format "​", only printing) : proof_scope.
Notation "Γ H : P" := (Esnoc Γ H P)
  (at level 1, P at level 200,
   left associativity, format "Γ H  :  P '//'", only printing) : proof_scope.
Notation "Γ '--------------------------------------' □ Δ '--------------------------------------' ∗ Q" :=
  (of_envs (Envs Γ Δ) ⊢ Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Δ '--------------------------------------' ∗ '//' Q '//'", only printing) :
  C_scope.
Notation "Δ '--------------------------------------' ∗ Q" :=
  (of_envs (Envs Enil Δ) ⊢ Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Δ '--------------------------------------' ∗ '//' Q '//'", only printing) : C_scope.
Notation "Γ '--------------------------------------' □ Q" :=
  (of_envs (Envs Γ Enil) ⊢ Q%I)
  (at level 1, Q at level 200, left associativity,
  format "Γ '--------------------------------------' □ '//' Q '//'", only printing)  : C_scope.
Notation "​​ Q" := (of_envs (Envs Enil Enil) ⊢ Q%I)
  (at level 1, Q at level 200, format "​​ Q", only printing) : C_scope.
