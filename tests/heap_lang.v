From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.heap_lang Require Import lang adequacy proofmode notation.
(* Import lang *again*. This used to break notation. *)
From iris.heap_lang Require Import lang.
Set Default Proof Using "Type".

Section tests.
  Context `{heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.

  Definition simpl_test :
    ⌜(10 = 4 + 6)%nat⌝ -∗
    WP let: "x" := ref #1 in "x" <- !"x";; !"x" {{ v, ⌜v = #1⌝ }}.
  Proof.
    iIntros "?". wp_alloc l. repeat (wp_pure _) || wp_load || wp_store.
    match goal with
    | |- context [ (10 = 4 + 6)%nat ] => done
    end.
  Qed.

  Definition val_scope_test_1 := SOMEV (#(), #()).

  Definition heap_e : expr :=
    let: "x" := ref #1 in "x" <- !"x" + #1 ;; !"x".

  Lemma heap_e_spec E : WP heap_e @ E {{ v, ⌜v = #2⌝ }}%I.
  Proof.
    iIntros "". rewrite /heap_e. Show.
    wp_alloc l. wp_let. wp_load. Show.
    wp_op. wp_store. by wp_load.
  Qed.

  Definition heap_e2 : expr :=
    let: "x" := ref #1 in
    let: "y" := ref #1 in
    "x" <- !"x" + #1 ;; !"x".

  Lemma heap_e2_spec E : WP heap_e2 @ E [{ v, ⌜v = #2⌝ }]%I.
  Proof.
    iIntros "". rewrite /heap_e2.
    wp_alloc l. wp_let. wp_alloc l'. wp_let.
    wp_load. wp_op. wp_store. wp_load. done.
  Qed.

  Definition heap_e3 : expr :=
    let: "x" := #true in
    let: "f" := λ: "z", "z" + #1 in
    if: "x" then "f" #0 else "f" #1.

  Lemma heap_e3_spec E : WP heap_e3 @ E [{ v, ⌜v = #1⌝ }]%I.
  Proof.
    iIntros "". rewrite /heap_e3.
    by repeat (wp_pure _).
  Qed.

  Definition heap_e4 : expr :=
    let: "x" := (let: "y" := ref (ref #1) in ref "y") in
    ! ! !"x".

  Lemma heap_e4_spec : WP heap_e4 [{ v, ⌜ v = #1 ⌝ }]%I.
  Proof.
    rewrite /heap_e4. wp_alloc l. wp_alloc l'. wp_let.
    wp_alloc l''. wp_let. by repeat wp_load.
  Qed.

  Definition heap_e5 : expr :=
    let: "x" := ref (ref #1) in FAA (!"x") (#10 + #1) + ! !"x".

  Lemma heap_e5_spec E : WP heap_e5 @ E [{ v, ⌜v = #13⌝ }]%I.
  Proof.
    rewrite /heap_e5. wp_alloc l. wp_alloc l'. wp_let.
    wp_load. wp_op. wp_faa. do 2 wp_load. wp_op. done.
  Qed.

  Definition heap_e6 : val := λ: "v", "v" = "v".

  Lemma heap_e6_spec (v : val) : (WP heap_e6 v {{ w, ⌜ w = #true ⌝ }})%I.
  Proof. wp_lam. wp_op. by case_bool_decide. Qed.

  Definition FindPred : val :=
    rec: "pred" "x" "y" :=
      let: "yp" := "y" + #1 in
      if: "yp" < "x" then "pred" "x" "yp" else "y".
  Definition Pred : val :=
    λ: "x",
      if: "x" ≤ #0 then -FindPred (-"x" + #2) #0 else FindPred "x" #0.

  Lemma FindPred_spec n1 n2 E Φ :
    n1 < n2 →
    Φ #(n2 - 1) -∗ WP FindPred #n2 #n1 @ E [{ Φ }].
  Proof.
    iIntros (Hn) "HΦ".
    iInduction (Z.gt_wf n2 n1) as [n1' _] "IH" forall (Hn).
    wp_rec. wp_let. wp_op. wp_let.
    wp_op; case_bool_decide; wp_if.
    - iApply ("IH" with "[%] [%] HΦ"); omega.
    - by assert (n1' = n2 - 1) as -> by omega.
  Qed.

  Lemma Pred_spec n E Φ : Φ #(n - 1) -∗ WP Pred #n @ E [{ Φ }].
  Proof.
    iIntros "HΦ". wp_lam.
    wp_op. case_bool_decide; wp_if.
    - wp_op. wp_op.
      wp_apply FindPred_spec; first omega.
      wp_op. by replace (n - 1) with (- (-n + 2 - 1)) by omega.
    - wp_apply FindPred_spec; eauto with omega.
  Qed.

  Lemma Pred_user E :
    WP let: "x" := Pred #42 in Pred "x" @ E [{ v, ⌜v = #40⌝ }]%I.
  Proof. iIntros "". wp_apply Pred_spec. wp_let. by wp_apply Pred_spec. Qed.

  Lemma wp_apply_evar e P :
    P -∗ (∀ Q Φ, Q -∗ WP e {{ Φ }}) -∗ WP e {{ _, True }}.
  Proof. iIntros "HP HW". wp_apply "HW". iExact "HP". Qed.

End tests.

Section printing_tests.
  Context `{heapG Σ}.

  (* These terms aren't even closed, but that's not what this is about.  The
  length of the variable names etc. has been carefully chosen to trigger
  particular behavior of the Coq pretty printer. *)

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"  {{ _, True }}.
  Proof.
    iIntros "_". Show.
  Abort.

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) Φ :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "v" := fun3 "v" in
       if: "v" = "v" then "v" else "v"  {{ Φ }}.
  Proof.
    iIntros "_". Show.
  Abort.

  Lemma wp_print_long_expr (fun1 fun2 fun3 : expr) Φ E :
    True -∗ WP let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "v" := fun3 "v" in
       if: "v" = "v" then "v" else "v" @ E {{ Φ }}.
  Proof.
    iIntros "_". Show.
  Abort.

  Lemma texan_triple_long_expr (fun1 fun2 fun3 : expr) :
    {{{ True }}}
       let: "val1" := fun1 #() in
       let: "val2" := fun2 "val1" in
       let: "val3" := fun3 "val2" in
       if: "val1" = "val2" then "val" else "val3"
    {{{ (x y : val) (z : Z), RET (x, y, #z); True }}}.
  Proof. Show. Abort.

End printing_tests.

Section error_tests.
  Context `{heapG Σ}.

  Check "not_cas".
  Lemma not_cas :
    (WP #() {{ _, True }})%I.
  Proof.
    Fail wp_cas_suc.
  Abort.
End error_tests.

Lemma heap_e_adequate σ : adequate NotStuck heap_e σ (= #2).
Proof. eapply (heap_adequacy heapΣ)=> ?. by apply heap_e_spec. Qed.
