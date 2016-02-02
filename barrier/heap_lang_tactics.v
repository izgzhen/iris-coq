Require Export barrier.heap_lang.
Require Import prelude.fin_maps.
Import heap_lang.

Ltac inv_step :=
  repeat match goal with
  | _ => progress simplify_map_equality' (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : prim_step _ _ _ _ _ |- _ => destruct H; subst
  | H : _ = fill ?K ?e |- _ =>
     destruct K as [|[]];
     simpl in H; first [subst e|discriminate H|injection' H]
     (* ensure that we make progress for each subgoal *)
  | H : head_step ?e _ _ _ _, Hv : of_val ?v = fill ?K ?e |- _ =>
    apply values_head_stuck, (fill_not_val K) in H;
    by rewrite -Hv to_of_val in H (* maybe use a helper lemma here? *)
  | H : head_step ?e _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if e is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac (reverse K) e
  | App ?e1 ?e2 =>
     lazymatch e1 with
     | of_val ?v1 => go (AppRCtx v1 :: K) e2 | _ => go (AppLCtx e2 :: K) e1
     end
  | Plus ?e1 ?e2 =>
     lazymatch e1 with
     | of_val ?v1 => go (PlusRCtx v1 :: K) e2 | _ => go (PlusLCtx e2 :: K) e1
     end
  | Le ?e1 ?e2 =>
     lazymatch e1 with
     | of_val ?v1 => go (LeRCtx v1 :: K) e2 | _ => go (LeLCtx e2 :: K) e1
     end
  | Pair ?e1 ?e2 =>
     lazymatch e1 with
     | of_val ?v1 => go (PairRCtx v1 :: K) e2 | _ => go (PairLCtx e2 :: K) e1
     end
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e1 ?e2 => go (StoreLCtx e2 :: K) e1 || go (StoreRCtx e1 :: K) e2
  | Cas ?e0 ?e1 ?e2 =>
     lazymatch e0 with
     | of_val ?v0 =>
        lazymatch e1 with
        | of_val ?v1 => go (CasRCtx v0 v1 :: K) e2
        | _ => go (CasMCtx v0 e2 :: K) e1
        end
     | _ => go (CasLCtx e1 e2 :: K) e0
     end
  end in go (@nil ectx_item) e.

Ltac do_step tac :=
  try match goal with |- language.reducible _ _ => eexists _, _, _ end;
  simpl;
  match goal with
  | |- prim_step ?e1 ?σ1 ?e2 ?σ2 ?ef =>
     reshape_expr e1 ltac:(fun K e1' =>
       eapply Ectx_step with K e1' _; [reflexivity|reflexivity|];
       first [apply alloc_fresh|econstructor];
       rewrite ?to_of_val; tac; fail)
  end.
