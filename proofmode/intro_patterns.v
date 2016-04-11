From iris.prelude Require Export strings.

Inductive intro_pat :=
  | IName : string → intro_pat
  | IAnom : intro_pat
  | IAnomPure : intro_pat
  | IClear : intro_pat
  | IPersistent : intro_pat → intro_pat
  | IList : list (list intro_pat) → intro_pat
  | ISimpl : intro_pat
  | IAlways : intro_pat.

Module intro_pat.
Inductive token :=
  | TName : string → token
  | TAnom : token
  | TAnomPure : token
  | TClear : token
  | TPersistent : token
  | TBar : token
  | TBracketL : token
  | TBracketR : token
  | TAmp : token
  | TParenL : token
  | TParenR : token
  | TSimpl : token
  | TAlways : token.

Fixpoint cons_name (kn : string) (k : list token) : list token :=
  match kn with "" => k | _ => TName (string_rev kn) :: k end.
Fixpoint tokenize_go (s : string) (k : list token) (kn : string) : list token :=
  match s with
  | "" => rev (cons_name kn k)
  | String " " s => tokenize_go s (cons_name kn k) ""
  | String "?" s => tokenize_go s (TAnom :: cons_name kn k) ""
  | String "%" s => tokenize_go s (TAnomPure :: cons_name kn k) ""
  | String "_" s => tokenize_go s (TClear :: cons_name kn k) ""
  | String "#" s => tokenize_go s (TPersistent :: cons_name kn k) ""
  | String "[" s => tokenize_go s (TBracketL :: cons_name kn k) ""
  | String "]" s => tokenize_go s (TBracketR :: cons_name kn k) ""
  | String "|" s => tokenize_go s (TBar :: cons_name kn k) ""
  | String "(" s => tokenize_go s (TParenL :: cons_name kn k) ""
  | String ")" s => tokenize_go s (TParenR :: cons_name kn k) ""
  | String "&" s => tokenize_go s (TAmp :: cons_name kn k) ""
  | String "!" s => tokenize_go s (TAlways :: cons_name kn k) ""
  | String "/" (String "=" s) => tokenize_go s (TSimpl :: cons_name kn k) ""
  | String a s => tokenize_go s k (String a kn)
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] "".

Inductive stack_item :=
  | SPat : intro_pat → stack_item
  | SPersistent : stack_item
  | SList : stack_item
  | SConjList : stack_item
  | SBar : stack_item
  | SAmp : stack_item.
Notation stack := (list stack_item).

Fixpoint close_list (k : stack)
    (ps : list intro_pat) (pss : list (list intro_pat)) : option stack :=
  match k with
  | [] => None
  | SList :: k => Some (SPat (IList (ps :: pss)) :: k)
  | SPat pat :: k => close_list k (pat :: ps) pss
  | SPersistent :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IPersistent p :: ps) pss
  | SBar :: k => close_list k [] (ps :: pss)
  | (SAmp | SConjList) :: _ => None
  end.

Fixpoint big_conj (ps : list intro_pat) : intro_pat :=
  match ps with
  | [] => IList [[]]
  | [p] => IList [[ p ]]
  | [p1;p2] => IList [[ p1 ; p2 ]]
  | p :: ps => IList [[ p ; big_conj ps ]]
  end.

Fixpoint close_conj_list (k : stack)
    (cur : option intro_pat) (ps : list intro_pat) : option stack :=
  match k with
  | [] => None
  | SConjList :: k =>
     ps ← match cur with
          | None => guard (ps = []); Some [] | Some p => Some (p :: ps)
          end;
     Some (SPat (big_conj ps) :: k)
  | SPat pat :: k => guard (cur = None); close_conj_list k (Some pat) ps
  | SPersistent :: k => p ← cur; close_conj_list k (Some (IPersistent p)) ps
  | SAmp :: k => p ← cur; close_conj_list k None (p :: ps)
  | (SBar | SList) :: _ => None
  end.

Fixpoint parse_go (ts : list token) (k : stack) : option stack :=
  match ts with
  | [] => Some k
  | TName s :: ts => parse_go ts (SPat (IName s) :: k)
  | TAnom :: ts => parse_go ts (SPat IAnom :: k)
  | TAnomPure :: ts => parse_go ts (SPat IAnomPure :: k)
  | TClear :: ts => parse_go ts (SPat IClear :: k)
  | TPersistent :: ts => parse_go ts (SPersistent :: k)
  | TBracketL :: ts => parse_go ts (SList :: k)
  | TBar :: ts => parse_go ts (SBar :: k)
  | TBracketR :: ts => close_list k [] [] ≫= parse_go ts
  | TParenL :: ts => parse_go ts (SConjList :: k)
  | TAmp :: ts => parse_go ts (SAmp :: k)
  | TParenR :: ts => close_conj_list k None [] ≫= parse_go ts
  | TSimpl :: ts => parse_go ts (SPat ISimpl :: k)
  | TAlways :: ts => parse_go ts (SPat IAlways :: k)
  end.
Definition parse (s : string) : option (list intro_pat) :=
  match k ← parse_go (tokenize s) [SList]; close_list k [] [] with
  | Some [SPat (IList [ps])] => Some ps
  | _ => None
  end.

Ltac parse s :=
  lazymatch type of s with
  | list intro_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some ?pats => pats | _ => fail "invalid list intro_pat" s
              end
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | intro_pat => s
  | string => lazymatch eval vm_compute in (parse s) with
              | Some [?pat] => pat | _ => fail "invalid intro_pat" s
              end
  end.
End intro_pat.
