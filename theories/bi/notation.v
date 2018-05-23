(** Just reserve the notation. *)
Reserved Notation "P ⊢ Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "P '⊢@{' PROP } Q" (at level 99, Q at level 200, right associativity).
Reserved Notation "('⊢@{' PROP } )" (at level 99).
Reserved Notation "P ⊣⊢ Q" (at level 95, no associativity).
Reserved Notation "P '⊣⊢@{' PROP } Q" (at level 95, no associativity).
Reserved Notation "('⊣⊢@{' PROP } )" (at level 95).
Reserved Notation "'emp'".
Reserved Notation "'⌜' φ '⌝'" (at level 1, φ at level 200, format "⌜ φ ⌝").
Reserved Notation "P ∗ Q" (at level 80, right associativity).
Reserved Notation "P -∗ Q" (at level 99, Q at level 200, right associativity).

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

Reserved Notation "|==> Q" (at level 99, Q at level 200, format "|==>  Q").
Reserved Notation "P ==∗ Q" (at level 99, Q at level 200, format "P  ==∗  Q").

(** Define the scope *)
Delimit Scope bi_scope with I.
