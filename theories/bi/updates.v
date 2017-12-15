From stdpp Require Import coPset.
From iris.bi Require Import interface.

Class BUpd (A : Type) : Type := bupd : A → A.
Instance : Params (@bupd) 2.

Notation "|==> Q" := (bupd Q)
  (at level 99, Q at level 200, format "|==>  Q") : bi_scope.
Notation "P ==∗ Q" := (P ⊢ |==> Q)
  (at level 99, Q at level 200, only parsing) : stdpp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q)%I
  (at level 99, Q at level 200, format "P  ==∗  Q") : bi_scope.

Class FUpd (A : Type) : Type := fupd : coPset → coPset → A → A.
Instance: Params (@fupd) 4.

Notation "|={ E1 , E2 }=> Q" := (fupd E1 E2 Q)
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q") : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)%I
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }=∗  Q") : bi_scope.
Notation "P ={ E1 , E2 }=∗ Q" := (P -∗ |={E1,E2}=> Q)
  (at level 99, E1, E2 at level 50, Q at level 200, only parsing) : stdpp_scope.

Notation "|={ E }=> Q" := (fupd E E Q)
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q") : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }=∗  Q") : bi_scope.
Notation "P ={ E }=∗ Q" := (P -∗ |={E}=> Q)
  (at level 99, E at level 50, Q at level 200, only parsing) : stdpp_scope.

(** Fancy updates that take a step. *)

Notation "|={ E1 , E2 }▷=> Q" := (|={E1,E2}=> (▷ |={E2,E1}=> Q))%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }▷=>  Q") : bi_scope.
Notation "P ={ E1 , E2 }▷=∗ Q" := (P -∗ |={ E1 , E2 }▷=> Q)%I
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "P  ={ E1 , E2 }▷=∗  Q") : bi_scope.
Notation "|={ E }▷=> Q" := (|={E,E}▷=> Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q") : bi_scope.
Notation "P ={ E }▷=∗ Q" := (P ={E,E}▷=∗ Q)%I
  (at level 99, E at level 50, Q at level 200,
   format "P  ={ E }▷=∗  Q") : bi_scope.
