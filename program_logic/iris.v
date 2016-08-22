From iris.program_logic Require Export ghost_ownership language.
From iris.prelude Require Export coPset.
From iris.algebra Require Import gmap auth agree gset coPset upred_big_op.

Class irisPreG (Λ : language) (Σ : gFunctors) : Set := IrisPreG {
  state_inG :> inG Σ (authR (optionUR (exclR (stateC Λ))));
  invariant_inG :> inG Σ (authR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
  enabled_inG :> inG Σ coPset_disjR;
  disabled_inG :> inG Σ (gset_disjR positive);
}.

Class irisG (Λ : language) (Σ : gFunctors) : Set := IrisG {
  iris_pre_inG :> irisPreG Λ Σ;
  state_name : gname;
  invariant_name : gname;
  enabled_name : gname;
  disabled_name : gname;
}.

Definition irisΣ (Λ : language) : gFunctors :=
  #[GFunctor (constRF (authUR (optionUR (exclR (stateC Λ)))));
    GFunctor (authRF (gmapURF positive (agreeRF (laterCF idCF))));
    GFunctor (constRF coPset_disjUR);
    GFunctor (constRF (gset_disjUR positive))].

Instance subG_irisΣ {Σ Λ} : subG (irisΣ Λ) Σ → irisPreG Λ Σ.
Proof.
  intros [?%subG_inG [?%subG_inG
    [?%subG_inG ?%subG_inG]%subG_inv]%subG_inv]%subG_inv; by constructor.
Qed.