From iris.program_logic Require Export pviewshifts.
Import uPred.

(* Some notation for linear view shifts. *)

Definition lvs {Λ Σ} (E1 E2 : coPset) (P Q : iProp Λ Σ) : iProp Λ Σ :=
  (P -★ |={E1,E2}=> Q)%I.
Arguments lvs {_ _} _ _ _%I _%I.
Instance: Params (@lvs) 4.
Notation "P ={ E1 , E2 }=★ Q" := (lvs E1 E2 P%I Q%I)
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=★  Q") : uPred_scope.
Notation "P ={ E1 , E2 }=★ Q" := (True ⊢ (P ={E1,E2}=★ Q)%I)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=★  Q") : C_scope.
Notation "P ={ E }=★ Q" := (P ={E,E}=★ Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=★  Q") : uPred_scope.
Notation "P ={ E }=★ Q" := (True ⊢ (P ={E}=★ Q)%I)
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=★  Q") : C_scope.

(* TODO: Also prove some lemmas. *)
