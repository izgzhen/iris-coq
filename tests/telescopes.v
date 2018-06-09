From stdpp Require Import coPset namespaces.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".

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
