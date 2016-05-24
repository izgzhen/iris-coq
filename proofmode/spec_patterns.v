From iris.prelude Require Export strings.

Inductive spec_goal_kind := GoalStd | GoalPvs.

Inductive spec_pat :=
  | SGoal : spec_goal_kind → bool → list string → spec_pat
  | SGoalPersistent : spec_pat
  | SGoalPure : spec_pat
  | SName : bool → string → spec_pat (* first arg = persistent *)
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
  | TPvs : token.

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
  | String "=" (String ">" s) => tokenize_go s (TPvs :: cons_name kn k) ""
  | String a s => tokenize_go s k (String a kn)
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] "".

Inductive state :=
  | StTop : state
  | StAssert : spec_goal_kind → bool → list string → state.

Fixpoint parse_go (ts : list token) (s : state)
    (k : list spec_pat) : option (list spec_pat) :=
  match s with
  | StTop =>
     match ts with
     | [] => Some (rev k)
     | TName s :: ts => parse_go ts StTop (SName false s :: k)
     | TBracketL :: TPersistent :: TBracketR :: ts => parse_go ts StTop (SGoalPersistent :: k)
     | TBracketL :: TPure :: TBracketR :: ts => parse_go ts StTop (SGoalPure :: k)
     | TBracketL :: ts => parse_go ts (StAssert GoalStd false []) k
     | TPvs :: TBracketL :: ts => parse_go ts (StAssert GoalPvs false []) k
     | TPvs :: ts => parse_go ts StTop (SGoal GoalPvs true [] :: k)
     | TPersistent :: TName s :: ts => parse_go ts StTop (SName true s :: k)
     | TForall :: ts => parse_go ts StTop (SForall :: k)
     | _ => None
     end
  | StAssert kind neg ss =>
     match ts with
     | TMinus :: ts => guard (¬neg ∧ ss = []); parse_go ts (StAssert kind true ss) k
     | TName s :: ts => parse_go ts (StAssert kind neg (s :: ss)) k
     | TBracketR :: ts => parse_go ts StTop (SGoal kind neg (rev ss) :: k)
     | _ => None
     end
  end.
Definition parse (s : string) : option (list spec_pat) :=
  parse_go (tokenize s) StTop [].

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
