From iris.prelude Require Export strings.
Set Default Proof Using "Type".

Inductive intro_pat :=
  | IName : string → intro_pat
  | IAnom : intro_pat
  | IDrop : intro_pat
  | IFrame : intro_pat
  | IList : list (list intro_pat) → intro_pat
  | IPureElim : intro_pat
  | IAlwaysElim : intro_pat → intro_pat
  | IModalElim : intro_pat → intro_pat
  | IPureIntro : intro_pat
  | IAlwaysIntro : intro_pat
  | IModalIntro : intro_pat
  | ISimpl : intro_pat
  | IForall : intro_pat
  | IAll : intro_pat
  | IClear : list (bool * string) → intro_pat. (* true = frame, false = clear *)

Module intro_pat.
Inductive token :=
  | TName : string → token
  | TAnom : token
  | TFrame : token
  | TBar : token
  | TBracketL : token
  | TBracketR : token
  | TAmp : token
  | TParenL : token
  | TParenR : token
  | TPureElim : token
  | TAlwaysElim : token
  | TModalElim : token
  | TPureIntro : token
  | TAlwaysIntro : token
  | TModalIntro : token
  | TSimpl : token
  | TForall : token
  | TAll : token
  | TClearL : token
  | TClearR : token.

Fixpoint cons_name (kn : string) (k : list token) : list token :=
  match kn with "" => k | _ => TName (string_rev kn) :: k end.
Fixpoint tokenize_go (s : string) (k : list token) (kn : string) : list token :=
  match s with
  | "" => rev (cons_name kn k)
  | String "?" s => tokenize_go s (TAnom :: cons_name kn k) ""
  | String "$" s => tokenize_go s (TFrame :: cons_name kn k) ""
  | String "[" s => tokenize_go s (TBracketL :: cons_name kn k) ""
  | String "]" s => tokenize_go s (TBracketR :: cons_name kn k) ""
  | String "|" s => tokenize_go s (TBar :: cons_name kn k) ""
  | String "(" s => tokenize_go s (TParenL :: cons_name kn k) ""
  | String ")" s => tokenize_go s (TParenR :: cons_name kn k) ""
  | String "&" s => tokenize_go s (TAmp :: cons_name kn k) ""
  | String "%" s => tokenize_go s (TPureElim :: cons_name kn k) ""
  | String "#" s => tokenize_go s (TAlwaysElim :: cons_name kn k) ""
  | String ">" s => tokenize_go s (TModalElim :: cons_name kn k) ""
  | String "!" (String "%" s) => tokenize_go s (TPureIntro :: cons_name kn k) ""
  | String "!" (String "#" s) => tokenize_go s (TAlwaysIntro :: cons_name kn k) ""
  | String "!" (String ">" s) => tokenize_go s (TModalIntro :: cons_name kn k) ""
  | String "{" s => tokenize_go s (TClearL :: cons_name kn k) ""
  | String "}" s => tokenize_go s (TClearR :: cons_name kn k) ""
  | String "/" (String "=" s) => tokenize_go s (TSimpl :: cons_name kn k) ""
  | String "*" (String "*" s) => tokenize_go s (TAll :: cons_name kn k) ""
  | String "*" s => tokenize_go s (TForall :: cons_name kn k) ""
  | String a s =>
     if is_space a then tokenize_go s (cons_name kn k) ""
     else tokenize_go s k (String a kn)
  (* TODO: Complain about invalid characters, to future-proof this against making more characters special. *)
  end.
Definition tokenize (s : string) : list token := tokenize_go s [] "".

Inductive stack_item :=
  | SPat : intro_pat → stack_item
  | SList : stack_item
  | SConjList : stack_item
  | SBar : stack_item
  | SAmp : stack_item
  | SAlwaysElim : stack_item
  | SModalElim : stack_item.
Notation stack := (list stack_item).

Fixpoint close_list (k : stack)
    (ps : list intro_pat) (pss : list (list intro_pat)) : option stack :=
  match k with
  | SList :: k => Some (SPat (IList (ps :: pss)) :: k)
  | SPat pat :: k => close_list k (pat :: ps) pss
  | SAlwaysElim :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IAlwaysElim p :: ps) pss
  | SModalElim :: k =>
     '(p,ps) ← maybe2 (::) ps; close_list k (IModalElim p :: ps) pss
  | SBar :: k => close_list k [] (ps :: pss)
  | _ => None
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
  | SConjList :: k =>
     ps ← match cur with
          | None => guard (ps = []); Some [] | Some p => Some (p :: ps)
          end;
     Some (SPat (big_conj ps) :: k)
  | SPat pat :: k => guard (cur = None); close_conj_list k (Some pat) ps
  | SAlwaysElim :: k => p ← cur; close_conj_list k (Some (IAlwaysElim p)) ps
  | SModalElim :: k => p ← cur; close_conj_list k (Some (IModalElim p)) ps
  | SAmp :: k => p ← cur; close_conj_list k None (p :: ps)
  | _ => None
  end.

Fixpoint parse_go (ts : list token) (k : stack) : option stack :=
  match ts with
  | [] => Some k
  | TName "_" :: ts => parse_go ts (SPat IDrop :: k)
  | TName s :: ts => parse_go ts (SPat (IName s) :: k)
  | TAnom :: ts => parse_go ts (SPat IAnom :: k)
  | TFrame :: ts => parse_go ts (SPat IFrame :: k)
  | TBracketL :: ts => parse_go ts (SList :: k)
  | TBar :: ts => parse_go ts (SBar :: k)
  | TBracketR :: ts => close_list k [] [] ≫= parse_go ts
  | TParenL :: ts => parse_go ts (SConjList :: k)
  | TAmp :: ts => parse_go ts (SAmp :: k)
  | TParenR :: ts => close_conj_list k None [] ≫= parse_go ts
  | TPureElim :: ts => parse_go ts (SPat IPureElim :: k)
  | TAlwaysElim :: ts => parse_go ts (SAlwaysElim :: k)
  | TModalElim :: ts => parse_go ts (SModalElim :: k)
  | TPureIntro :: ts => parse_go ts (SPat IPureIntro :: k)
  | TAlwaysIntro :: ts => parse_go ts (SPat IAlwaysIntro :: k)
  | TModalIntro :: ts => parse_go ts (SPat IModalIntro :: k)
  | TSimpl :: ts => parse_go ts (SPat ISimpl :: k)
  | TAll :: ts => parse_go ts (SPat IAll :: k)
  | TForall :: ts => parse_go ts (SPat IForall :: k)
  | TClearL :: ts => parse_clear ts [] k
  | _ => None
  end
with parse_clear (ts : list token)
    (ss : list (bool * string)) (k : stack) : option stack :=
  match ts with
  | TFrame :: TName s :: ts => parse_clear ts ((true,s) :: ss) k
  | TName s :: ts => parse_clear ts ((false,s) :: ss) k
  | TClearR :: ts => parse_go ts (SPat (IClear (reverse ss)) :: k)
  | _ => None
  end.

Definition parse (s : string) : option (list intro_pat) :=
  match k ← parse_go (tokenize s) [SList]; close_list k [] [] with
  | Some [SPat (IList [ps])] => Some ps
  | _ => None
  end.

Ltac parse s :=
  lazymatch type of s with
  | list intro_pat => s
  | list string =>
     lazymatch eval vm_compute in (mjoin <$> mapM parse s) with
     | Some ?pats => pats | _ => fail "invalid list intro_pat" s
     end
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some ?pats => pats | _ => fail "invalid list intro_pat" s
     end
  end.
Ltac parse_one s :=
  lazymatch type of s with
  | intro_pat => s
  | string =>
     lazymatch eval vm_compute in (parse s) with
     | Some [?pat] => pat | _ => fail "invalid intro_pat" s
     end
  end.
End intro_pat.

Fixpoint intro_pat_persistent (p : intro_pat) :=
  match p with
  | IPureElim => true
  | IAlwaysElim _ => true
  | IList pps => forallb (forallb intro_pat_persistent) pps
  | _ => false
  end.

Ltac intro_pat_persistent p :=
  lazymatch type of p with
  | intro_pat => eval cbv in (intro_pat_persistent p)
  | string =>
     let pat := intro_pat.parse_one p in
     eval cbv in (intro_pat_persistent pat)
  | _ => p
  end.
