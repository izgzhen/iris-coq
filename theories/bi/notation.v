(** Just reserve the notation. *)

(** Turnstiles *)
Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P '⊢@{' PROP } Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "('⊢@{' PROP } )" (at level 99).
Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "P '⊣⊢@{' PROP } Q" (at level 95, no associativity).
Reserved Notation "('⊣⊢@{' PROP } )" (at level 95).

(** BI connectives *)
Reserved Notation "'emp'".
Reserved Notation "'⌜' φ '⌝'" (at level 1, φ at level 200, format "⌜ φ ⌝").
Reserved Notation "P ∗ Q" (at level 80, right associativity).
Reserved Notation "P -∗ Q"
  (at level 99, Q at level 200, right associativity,
   format "'[' P  '/' -∗  Q ']'").

Reserved Notation "⎡ P ⎤".

(** Modalities *)
Reserved Notation "'<pers>' P" (at level 20, right associativity).
Reserved Notation "'<pers>?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'<pers>?' p  P").

Reserved Notation "▷ P" (at level 20, right associativity).
Reserved Notation "▷? p P" (at level 20, p at level 9, P at level 20,
   format "▷? p  P").
Reserved Notation "▷^ n P" (at level 20, n at level 9, P at level 20,
   format "▷^ n  P").

Reserved Infix "∗-∗" (at level 95, no associativity).

Reserved Notation "'<affine>' P" (at level 20, right associativity).
Reserved Notation "'<affine>?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'<affine>?' p  P").

Reserved Notation "'<absorb>' P" (at level 20, right associativity).

Reserved Notation "□ P" (at level 20, right associativity).
Reserved Notation "'□?' p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "'□?' p  P").

Reserved Notation "◇ P" (at level 20, right associativity).

Reserved Notation "■ P" (at level 20, right associativity).
Reserved Notation "■? p P" (at level 20, p at level 9, P at level 20,
   right associativity, format "■? p  P").

Reserved Notation "'<obj>' P" (at level 20, right associativity).
Reserved Notation "'<subj>' P" (at level 20, right associativity).

(** Update modalities *)
Reserved Notation "|==> Q" (at level 99, Q at level 200, format "|==>  Q").
Reserved Notation "P ==∗ Q"
  (at level 99, Q at level 200, format "'[' P  '/' ==∗  Q ']'").

Reserved Notation "|={ E1 , E2 }=> Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }=>  Q").
Reserved Notation "P ={ E1 , E2 }=∗ Q"
  (at level 99, E1,E2 at level 50, Q at level 200,
   format "'[' P  '/' ={ E1 , E2 }=∗  Q ']'").

Reserved Notation "|={ E }=> Q"
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }=>  Q").
Reserved Notation "P ={ E }=∗ Q"
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  '/' ={ E }=∗  Q ']'").

Reserved Notation "|={ E1 , E2 , E3 }▷=> Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 , E3 }▷=>  Q").
Reserved Notation "P ={ E1 , E2 , E3 }▷=∗ Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "'[' P  '/' ={ E1 , E2 , E3 }▷=∗  Q ']'").
Reserved Notation "|={ E1 , E2 }▷=> Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "|={ E1 , E2 }▷=>  Q").
Reserved Notation "P ={ E1 , E2 }▷=∗ Q"
  (at level 99, E1, E2 at level 50, Q at level 200,
   format "'[' P  '/' ={ E1 , E2 }▷=∗  Q ']'").
Reserved Notation "|={ E }▷=> Q"
  (at level 99, E at level 50, Q at level 200,
   format "|={ E }▷=>  Q").
Reserved Notation "P ={ E }▷=∗ Q"
  (at level 99, E at level 50, Q at level 200,
   format "'[' P  '/' ={ E }▷=∗  Q ']'").

(** Big Ops *)
Reserved Notation "'[∗' 'list]' k ↦ x ∈ l , P"
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∗  list]  k ↦ x  ∈  l ,  P").
Reserved Notation "'[∗' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∗  list]  x  ∈  l ,  P").

Reserved Notation "'[∗' 'list]' k ↦ x1 ; x2 ∈ l1 ; l2 , P"
  (at level 200, l1, l2 at level 10, k, x1, x2 at level 1, right associativity,
   format "[∗  list]  k ↦ x1 ; x2  ∈  l1 ; l2 ,  P").
Reserved Notation "'[∗' 'list]' x1 ; x2 ∈ l1 ; l2 , P"
  (at level 200, l1, l2 at level 10, x1, x2 at level 1, right associativity,
   format "[∗  list]  x1 ; x2  ∈  l1 ; l2 ,  P").

Reserved Notation "'[∗]' Ps" (at level 20).

Reserved Notation "'[∧' 'list]' k ↦ x ∈ l , P"
  (at level 200, l at level 10, k, x at level 1, right associativity,
   format "[∧  list]  k ↦ x  ∈  l ,  P").
Reserved Notation "'[∧' 'list]' x ∈ l , P"
  (at level 200, l at level 10, x at level 1, right associativity,
   format "[∧  list]  x  ∈  l ,  P").

Reserved Notation "'[∧]' Ps" (at level 20).

Reserved Notation "'[∗' 'map]' k ↦ x ∈ m , P"
  (at level 200, m at level 10, k, x at level 1, right associativity,
   format "[∗  map]  k ↦ x  ∈  m ,  P").
Reserved Notation "'[∗' 'map]' x ∈ m , P"
  (at level 200, m at level 10, x at level 1, right associativity,
   format "[∗  map]  x  ∈  m ,  P").

Reserved Notation "'[∗' 'set]' x ∈ X , P"
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  set]  x  ∈  X ,  P").

Reserved Notation "'[∗' 'mset]' x ∈ X , P"
  (at level 200, X at level 10, x at level 1, right associativity,
   format "[∗  mset]  x  ∈  X ,  P").

(** Define the scope *)
Delimit Scope bi_scope with I.
