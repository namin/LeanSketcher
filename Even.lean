set_option grind.warning false

inductive Even : Nat → Prop where
  | zero : Even 0
  | step (n : Nat) : Even n → Even (n + 2)

theorem even_plus_two (n : Nat) (h : Even n) : Even (n + 2) := by
  induction h with
  | zero =>
    apply Even.step
    apply Even.zero
  | step n ih1 ih2 =>
    apply Even.step
    apply ih2

theorem even_plus_two_grind (n : Nat) (h : Even n) : Even (n + 2) := by
  induction h <;> grind [Even]
