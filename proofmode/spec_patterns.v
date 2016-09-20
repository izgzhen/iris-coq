From iris.prelude Require Export strings.

Record spec_goal := SpecGoal {
  spec_goal_vs : bool;
  spec_goal_negate : bool;
  spec_goal_hyps : list string
}.

Inductive spec_pat :=
  | SGoal : spec_goal → spec_pat
  | SGoalPersistent : spec_pat
  | SGoalPure : spec_pat
  | SName : string → spec_pat
  | SForall : spec_pat.

Module spec_pat.
Inductive token :=
  | TName : string → token
  | TMinus : token
  | TBracketL : token
  | TBracketR : token
  | TPersistent : token
  | TPure : token
  | TForall : token
  | TVs : token.

Fixpoint cons_name (kn : string) (k : list token) : list token :=
  match kn with "" => k | _ => TName (string_rev kn) :: k end.
Fixpoint tokenize_go (s : string) (k : list token) (kn : string) : list token :=
  match s with
  | "" => rev (cons_name kn k)
  | String " " s => tokenize_go s (cons_name kn k) ""
  | String "-" s => tokenize_go s (TMinus :: cons_name kn k) ""
  | String "[" s => tokenize_go s (TBracketL :: cons_name kn k) ""
  | String "]" s => tokenize_go s (TBracketR :: cons_name kn k) ""
  | String "#" s => tokenize_go s (TPersistent :: cons_name kn k) ""
  | String "%" s => tokenize_go s (TPure :: cons_name kn k) ""
  | String "*" s => tokenize_go s (TForall :: cons_name kn k) ""
  | String "=" (String "=" (String ">" s)) => tokenize_go s (TVs :: cons_name kn k) ""
  | String a s => tokenize_go s k (String a kn)
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] "".

Inductive state :=
  | StTop : state
  | StAssert : spec_goal → state.

Fixpoint parse_go (ts : list token) (k : list spec_pat) : option (list spec_pat) :=
  match ts with
  | [] => Some (rev k)
  | TName s :: ts => parse_go ts (SName s :: k)
  | TBracketL :: TPersistent :: TBracketR :: ts => parse_go ts (SGoalPersistent :: k)
  | TBracketL :: TPure :: TBracketR :: ts => parse_go ts (SGoalPure :: k)
  | TBracketL :: ts => parse_goal ts (SpecGoal false false []) k
  | TVs :: TBracketL :: ts => parse_goal ts (SpecGoal true false []) k
  | TVs :: ts => parse_go ts (SGoal (SpecGoal true true []) :: k)
  | TForall :: ts => parse_go ts (SForall :: k)
  | _ => None
  end
with parse_goal (ts : list token) (g : spec_goal)
    (k : list spec_pat) : option (list spec_pat) :=
  match ts with
  | TMinus :: ts =>
     guard (¬spec_goal_negate g ∧ spec_goal_hyps g = []);
     parse_goal ts (SpecGoal (spec_goal_vs g) true (spec_goal_hyps g)) k
  | TName s :: ts =>
     parse_goal ts (SpecGoal (spec_goal_vs g) (spec_goal_negate g)
                             (s :: spec_goal_hyps g)) k
  | TBracketR :: ts =>
     parse_go ts (SGoal (SpecGoal (spec_goal_vs g) (spec_goal_negate g)
                                  (reverse (spec_goal_hyps g))) :: k)
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
