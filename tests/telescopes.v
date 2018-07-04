From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

Section accessor.
(* Just playing around a bit with a telescope version
   of accessors with just one binder list. *)
Definition accessor `{!BiFUpd PROP} {X : tele} (E1 E2 : coPset)
           (α β γ : X → PROP) : PROP :=
  (|={E1,E2}=> ∃.. x, α x ∗ (β x -∗ |={E2,E1}=> (γ x)))%I.

Notation "'ACC' @ E1 , E2 {{ ∃ x1 .. xn , α | β | γ } }" :=
  (accessor (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            E1 E2
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..)
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => β%I) ..)
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => γ%I) ..))
  (at level 20, α, β, γ at level 200, x1 binder, xn binder, only parsing).

(* Working with abstract telescopes. *)
Section tests.
Context `{!BiFUpd PROP} {X : tele}.
Implicit Types α β γ : X → PROP.

Lemma acc_mono E1 E2 α β γ1 γ2 :
  (∀.. x, γ1 x -∗ γ2 x) -∗
  accessor E1 E2 α β γ1 -∗ accessor E1 E2 α β γ2.
Proof.
  iIntros "Hγ12 >Hacc". iDestruct "Hacc" as (x') "[Hα Hclose]". Show.
  iModIntro. iExists x'. iFrame. iIntros "Hβ".
  iMod ("Hclose" with "Hβ") as "Hγ". iApply "Hγ12". auto.
Qed.
End tests.

Section printing_tests.
Context `{!BiFUpd PROP}.

(* Working with concrete telescopes: Testing the reduction into normal quantifiers. *)
Lemma acc_elim_test_1 E1 E2 :
  ACC @ E1, E2 {{ ∃ a b : nat, <affine> ⌜a = b⌝ | True | <affine> ⌜a ≠ b⌝ }}
    ⊢@{PROP} |={E1}=> False.
Proof.
  iIntros ">H". Show.
  iDestruct "H" as (a b) "[% Hclose]". iMod ("Hclose" with "[//]") as "%".
  done.
Qed.
End printing_tests.
End accessor.

(* Robbert's tests *)
Section telescopes_and_tactics.

Definition test1 {PROP : sbi} {X : tele} (α : X → PROP) : PROP :=
  (∃.. x, α x)%I.

Notation "'TEST1' {{ ∃ x1 .. xn , α } }" :=
  (test1 (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..))
  (at level 20, α at level 200, x1 binder, xn binder, only parsing).

Definition test2 {PROP : sbi} {X : tele} (α : X → PROP) : PROP :=
  (▷ ∃.. x, α x)%I.

Notation "'TEST2' {{ ∃ x1 .. xn , α } }" :=
  (test2 (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..))
  (at level 20, α at level 200, x1 binder, xn binder, only parsing).

Definition test3 {PROP : sbi} {X : tele} (α : X → PROP) : PROP :=
  (◇ ∃.. x, α x)%I.

Notation "'TEST3' {{ ∃ x1 .. xn , α } }" :=
  (test3 (X:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. ))
            (tele_app (TT:=TeleS (fun x1 => .. (TeleS (fun xn => TeleO)) .. )) $
                      fun x1 => .. (fun xn => α%I) ..))
  (at level 20, α at level 200, x1 binder, xn binder, only parsing).

Check "test1_test".
Lemma test1_test {PROP : sbi}  :
  TEST1 {{ ∃ a b : nat, <affine> ⌜a = b⌝ }} ⊢@{PROP} ▷ False.
Proof.
  iIntros "H". iDestruct "H" as (x) "H". Show.
Restart.
  iIntros "H". unfold test1. iDestruct "H" as (x) "H". Show.
Abort.

Check "test2_test".
Lemma test2_test {PROP : sbi}  :
  TEST2 {{ ∃ a b : nat, <affine> ⌜a = b⌝ }} ⊢@{PROP} ▷ False.
Proof.
  iIntros "H". iModIntro. Show.
  iDestruct "H" as (x) "H". Show.
Restart.
  iIntros "H". iDestruct "H" as (x) "H". Show.
Abort.

Check "test3_test".
Lemma test3_test {PROP : sbi}  :
  TEST3 {{ ∃ a b : nat, <affine> ⌜a = b⌝ }} ⊢@{PROP} ▷ False.
Proof.
  iIntros "H". iMod "H".
  iDestruct "H" as (x) "H".
  Show.
Restart.
  iIntros "H". iDestruct "H" as (x) "H". Show.
Abort.

End telescopes_and_tactics.
