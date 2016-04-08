From iris.algebra Require Import one_shot dec_agree.
From iris.program_logic Require Import hoare.
From iris.heap_lang Require Import heap assert wp_tactics notation.
Import uPred.

Definition one_shot_example : val := λ: <>,
  let: "x" := ref (InjL #0) in (
  (* tryset *) (λ: "n",
    CAS '"x" (InjL #0) (InjR '"n")),
  (* check  *) (λ: <>,
    let: "y" := !'"x" in λ: <>,
    match: '"y" with
      InjL <> => #()
    | InjR "n" =>
       match: !'"x" with
         InjL <> => Assert #false
       | InjR "m" => Assert ('"n" = '"m")
       end
    end)).

Class one_shotG Σ :=
  OneShotG { one_shot_inG :> inG heap_lang Σ (one_shotR (dec_agreeR Z)) }.
Definition one_shotGF : gFunctorList :=
  [GFunctor (constRF (one_shotR (dec_agreeR Z)))].
Instance inGF_one_shotG Σ : inGFs heap_lang Σ one_shotGF → one_shotG Σ.
Proof. intros [? _]; split; apply: inGF_inG. Qed.

Section proof.
Context {Σ : gFunctors} `{!heapG Σ, !one_shotG Σ}.
Context (heapN N : namespace) (HN : heapN ⊥ N).
Local Notation iProp := (iPropG heap_lang Σ).

Definition one_shot_inv (γ : gname) (l : loc) : iProp :=
  (l ↦ InjLV #0 ★ own γ OneShotPending ∨
  ∃ n : Z, l ↦ InjRV #n ★ own γ (Shot (DecAgree n)))%I.

Lemma wp_one_shot (Φ : val → iProp) :
  (heap_ctx heapN ★ ∀ f1 f2 : val,
    (∀ n : Z, □ WP f1 #n {{ λ w, w = #true ∨ w = #false }}) ★
    □ WP f2 #() {{ λ g, □ WP g #() {{ λ _, True }} }} -★ Φ (f1,f2)%V)
  ⊢ WP one_shot_example #() {{ Φ }}.
Proof.
  wp_let.
  wp eapply wp_alloc; eauto with I.
  apply forall_intro=> l; apply wand_intro_l.
  eapply sep_elim_True_l; first by apply (own_alloc OneShotPending).
  rewrite !pvs_frame_r; apply wp_strip_pvs.
  rewrite !sep_exist_r; apply exist_elim=>γ.
  (* TODO: this is horrible *)
  trans (heap_ctx heapN ★ (|==> inv N (one_shot_inv γ l)) ★
    (∀ f1 f2 : val,
      (∀ n : Z, □ WP f1 #n {{ λ w, w = #true ∨ w = #false }}) ★
      □ WP f2 #() {{ λ g, □ WP g #() {{ λ _, True }} }} -★ Φ (f1, f2)%V))%I.
  { ecancel [heap_ctx _; ∀ _, _]%I. rewrite -inv_alloc // -later_intro.
    apply or_intro_l'. solve_sep_entails. }
  rewrite pvs_frame_r pvs_frame_l; apply wp_strip_pvs; wp_let.
  rewrite -pvs_intro.
  rewrite !assoc 2!forall_elim; eapply wand_apply_r'; first done.
  rewrite (always_sep_dup (_ ★ _)); apply sep_mono.
  - apply forall_intro=>n. apply: always_intro. wp_let.
    eapply (wp_inv_timeless _ _ _ (one_shot_inv γ l)); eauto 10 with I.
    rewrite (True_intro (inv _ _)) right_id.
    apply wand_intro_r; rewrite sep_or_l; apply or_elim.
    + rewrite -wp_pvs.
      wp eapply wp_cas_suc; eauto with I ndisj.
      rewrite (True_intro (heap_ctx _)) left_id.
      ecancel [l ↦ _]%I; apply wand_intro_l.
      rewrite (own_update); (* FIXME: canonical structures are not working *)
        last by apply (one_shot_update_shoot (DecAgree n : dec_agreeR _)).
      rewrite pvs_frame_l; apply pvs_mono, sep_intro_True_r; eauto with I.
      rewrite /one_shot_inv -or_intro_r -(exist_intro n).
      solve_sep_entails.
    + rewrite sep_exist_l; apply exist_elim=>m.
      eapply wp_cas_fail with (v':=InjRV #m) (q:=1%Qp);
        eauto with I ndisj; strip_later.
      ecancel [l ↦ _]%I; apply wand_intro_l, sep_intro_True_r; eauto with I.
      rewrite /one_shot_inv -or_intro_r -(exist_intro m).
      solve_sep_entails.
  - apply: always_intro. wp_seq.
    wp_focus (Load (%l))%I.
    eapply (wp_inv_timeless _ _ _ (one_shot_inv γ l)); eauto 10 with I.
    apply wand_intro_r.
    trans (heap_ctx heapN ★ inv N (one_shot_inv γ l) ★ ∃ v, l ↦ v ★
      ((v = InjLV #0 ★ own γ OneShotPending) ∨
       ∃ n : Z, v = InjRV #n ★ own γ (Shot (DecAgree n))))%I.
    { rewrite assoc. apply sep_mono_r, or_elim.
      + rewrite -(exist_intro (InjLV #0)). rewrite -or_intro_l const_equiv //.
        solve_sep_entails.
      + apply exist_elim=> n. rewrite -(exist_intro (InjRV #n)) -(exist_intro n).
        apply sep_mono_r, or_intro_r', sep_intro_True_l; eauto with I. }
    rewrite !sep_exist_l; apply exist_elim=> w.
    eapply wp_load with (q:=1%Qp) (v:=w); eauto with I ndisj.
    rewrite -later_intro; cancel [l ↦ w]%I.
    rewrite -later_intro; apply wand_intro_l.
    trans (heap_ctx heapN ★ inv N (one_shot_inv γ l) ★ one_shot_inv γ l ★
      (w = InjLV #0 ∨ (∃ n : Z, w = InjRV #n ★ own γ (Shot (DecAgree n)))))%I.
    { cancel [heap_ctx heapN]. rewrite !sep_or_l; apply or_elim.
      + rewrite -or_intro_l. ecancel [inv _ _]%I.
        rewrite [(_ ★ _)%I]comm -assoc. apply const_elim_sep_l=>->.
        rewrite const_equiv // right_id /one_shot_inv -or_intro_l .
        solve_sep_entails.
      + rewrite -or_intro_r !sep_exist_l; apply exist_elim=> n.
        rewrite -(exist_intro n). ecancel [inv _ _]%I.
        rewrite [(_ ★ _)%I]comm -assoc. apply const_elim_sep_l=>->.
        rewrite const_equiv // left_id /one_shot_inv -or_intro_r.
        rewrite -(exist_intro n) {1}(always_sep_dup (own _ _)).
        solve_sep_entails. }
    cancel [one_shot_inv γ l].
    wp_let. rewrite -pvs_intro. apply: always_intro. wp_seq.
    rewrite !sep_or_l; apply or_elim.
    { rewrite assoc.
      apply const_elim_sep_r=>->. wp_case; wp_seq; rewrite -pvs_intro; eauto with I. }
    rewrite !sep_exist_l; apply exist_elim=> n.
    rewrite [(w=_ ★ _)%I]comm !assoc; apply const_elim_sep_r=>->.
    (* FIXME: why do we need to fold? *)
    wp_case; fold of_val. wp_let. wp_focus (Load (%l))%I.
    eapply (wp_inv_timeless _ _ _ (one_shot_inv γ l)); eauto 10 with I.
    rewrite (True_intro (inv _ _)) right_id.
    apply wand_intro_r; rewrite sep_or_l; apply or_elim.
    + rewrite (True_intro (heap_ctx _)) (True_intro (l ↦ _)) !left_id.
      rewrite -own_op own_valid_l one_shot_validI /= left_absorb.
      apply False_elim.
    + rewrite !sep_exist_l; apply exist_elim=> m.
      eapply wp_load with (q:=1%Qp) (v:=InjRV #m); eauto with I ndisj; strip_later.
      cancel [l ↦ InjRV #m]%I. apply wand_intro_r.
      rewrite (True_intro (heap_ctx heapN)) left_id.
      rewrite -own_op own_valid_l one_shot_validI Shot_op /= discrete_valid.
      rewrite -assoc. apply const_elim_sep_l=> /dec_agree_op_inv [->].
      rewrite dec_agree_idemp. apply sep_intro_True_r.
      { rewrite /one_shot_inv -or_intro_r -(exist_intro m). solve_sep_entails. }
      wp_case; fold of_val. wp_let. rewrite -wp_assert'.
      wp_op; by eauto using later_intro with I.
Qed.

Lemma hoare_one_shot (Φ : val → iProp) :
  heap_ctx heapN ⊢ {{ True }} one_shot_example #()
    {{ λ ff,
      (∀ n : Z, {{ True }} Fst ff #n {{ λ w, w = #true ∨ w = #false }}) ★
      {{ True }} Snd ff #() {{ λ g, {{ True }} g #() {{ λ _, True }} }}
    }}.
Proof.
  apply: always_intro; rewrite left_id -wp_one_shot /=.
  cancel [heap_ctx heapN].
  apply forall_intro=> f1; apply forall_intro=> f2.
  apply wand_intro_l; rewrite right_id; apply sep_mono.
  - apply forall_mono=>n. apply always_mono; rewrite left_id. by wp_proj.
  - apply always_mono; rewrite left_id. wp_proj.
    apply wp_mono=> v. by apply always_mono; rewrite left_id.
Qed.
End proof.
