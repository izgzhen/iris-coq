From program_logic Require Export sts.
From heap_lang Require Export derived heap wp_tactics notation.

Definition newchan := (λ: "", ref '0)%L.
Definition signal := (λ: "x", "x" <- '1)%L.
Definition wait := (rec: "wait" "x" := if: !"x" = '1 then '() else "wait" "x")%L.

(** The STS describing the main barrier protocol. *)
Module barrier_proto.
  Inductive state := Low (I : gset gname) | High (I : gset gname).
  Inductive token := Change (i : gname) | Send.

  Definition change_tokens (I : gset gname) : set token :=
    mkSet (λ t, match t with Change i => i ∈ I | Send => False end).

  Inductive trans : relation state :=
  | LowChange I1 I2 : trans (Low I1) (Low I2)
  | HighChange I2 I1 : trans (High I1) (High I2)
  | LowHigh I : trans (Low I) (High I).

  Definition tok (s : state) : set token :=
    match s with
    | Low I' => change_tokens I'
    | High I' => change_tokens I' ∪ {[ Send ]}
    end.

  Definition sts := sts.STS trans tok.
End barrier_proto.

