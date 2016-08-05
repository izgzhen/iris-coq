From iris.program_logic Require Export ghost_ownership language.
From iris.prelude Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset upred_big_op.

Class irisPreG (Λ : language) (Σ : gFunctors) : Set := IrisPreG {
  state_inG :> inG Σ (authUR (optionUR (exclR (stateC Λ))));
  invariant_inG :> inG Σ (authUR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
  enabled_inG :> inG Σ coPset_disjUR;
  disabled_inG :> inG Σ (gset_disjUR positive);
}.

Class irisG (Λ : language) (Σ : gFunctors) : Set := IrisG {
  iris_pre_inG :> irisPreG Λ Σ;
  state_name : gname;
  invariant_name : gname;
  enabled_name : gname;
  disabled_name : gname;
}.

Definition irisGF (Λ : language) : gFunctorList :=
  [GFunctor (constRF (authUR (optionUR (exclR (stateC Λ)))));
   GFunctor (authRF (gmapURF positive (agreeRF (laterCF idCF))));
   GFunctor (constRF coPset_disjUR);
   GFunctor (constRF (gset_disjUR positive))].

Instance inGF_barrierG `{H : inGFs Σ (irisGF Λ)} : irisPreG Λ Σ.
Proof.
  by destruct H as (?%inGF_inG & ?%inGF_inG & ?%inGF_inG & ?%inGF_inG & _).
Qed.
