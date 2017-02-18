From stdpp Require Export strings.
From iris.proofmode Require Import tokens.
Set Default Proof Using "Type".

Record spec_goal := SpecGoal {
  spec_goal_modal : bool;
  spec_goal_negate : bool;
  spec_goal_frame : list string;
  spec_goal_hyps : list string
}.

Inductive spec_pat :=
  | SGoal : spec_goal → spec_pat
  | SGoalPersistent : spec_pat
  | SGoalPure : spec_pat
  | SName : string → spec_pat
  | SForall : spec_pat.

Definition spec_pat_modal (p : spec_pat) : bool :=
  match p with SGoal g => spec_goal_modal g | _ => false end.

Module spec_pat.
Inductive state :=
  | StTop : state
  | StAssert : spec_goal → state.

Fixpoint parse_go (ts : list token) (k : list spec_pat) : option (list spec_pat) :=
  match ts with
  | [] => Some (reverse k)
  | TName s :: ts => parse_go ts (SName s :: k)
  | TBracketL :: TAlways :: TBracketR :: ts => parse_go ts (SGoalPersistent :: k)
  | TBracketL :: TPure :: TBracketR :: ts => parse_go ts (SGoalPure :: k)
  | TBracketL :: ts => parse_goal ts (SpecGoal false false [] []) k
  | TModal :: TBracketL :: ts => parse_goal ts (SpecGoal true false [] []) k
  | TModal :: ts => parse_go ts (SGoal (SpecGoal true true [] []) :: k)
  | TForall :: ts => parse_go ts (SForall :: k)
  | _ => None
  end
with parse_goal (ts : list token) (g : spec_goal)
    (k : list spec_pat) : option (list spec_pat) :=
  match ts with
  | TMinus :: ts =>
     guard (¬spec_goal_negate g ∧ spec_goal_frame g = [] ∧ spec_goal_hyps g = []);
     parse_goal ts (SpecGoal (spec_goal_modal g) true
       (spec_goal_frame g) (spec_goal_hyps g)) k
  | TName s :: ts =>
     parse_goal ts (SpecGoal (spec_goal_modal g) (spec_goal_negate g)
       (spec_goal_frame g) (s :: spec_goal_hyps g)) k
  | TFrame :: TName s :: ts =>
     parse_goal ts (SpecGoal (spec_goal_modal g) (spec_goal_negate g)
       (s :: spec_goal_frame g) (spec_goal_hyps g)) k
  | TBracketR :: ts =>
     parse_go ts (SGoal (SpecGoal (spec_goal_modal g) (spec_goal_negate g)
       (reverse (spec_goal_frame g)) (reverse (spec_goal_hyps g))) :: k)
  | _ => None
  end.
Definition parse (s : string) : option (list spec_pat) :=
  parse_go (tokenize s) [].

Ltac parse s :=
  lazymatch type of s with
  | list spec_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some ?pats => pats | _ => fail "invalid list spec_pat" s
              end
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | spec_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some [?pat] => pat | _ => fail "invalid spec_pat" s
              end
  end.
End spec_pat.
