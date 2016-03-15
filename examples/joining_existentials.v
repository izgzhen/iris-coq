From iris.program_logic Require Import saved_one_shot.
From iris.barrier Require Import proof specification.
From iris.heap_lang Require Import notation par.

Definition client (eM eW1 eW2 : expr []) : expr [] :=
  (let: "b" := newbarrier #() in (^^eM ;; ^signal '"b") ||
                              ((^wait '"b" ;; ^^eW1) || (^wait '"b" ;; ^^eW2))).
