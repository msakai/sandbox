#check Prop

#check (1 + 1 = 3 : Prop)

#check (fun n => n + 3 = 39 : Nat → Prop)

#check True

#check False

example : True := by trivial

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

example (h : False) : ∀ x y z n : Nat,
  n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True

#eval True → False

#eval False → True

#eval False → False

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  apply hp

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

example (P Q : Prop) (hq : Q) : P → Q := by
  intro hp
  exact hq

#eval ¬True

#eval ¬False

example (P : Prop) : (¬ P) = (P → False) := by
  rfl

example (P : Prop) (hnp : ¬ P) (hp: P) : False := by
  apply hnp
  exact hp

example (P Q : Prop) (h : P → ¬ Q) : Q → ¬ P := by
  intro hq
  intro hp
  apply h
  apply hp
  apply hq

example (P : Prop) (hnp : ¬ P) (hp : P) : False := by
  contradiction

example (P Q : Prop) (hnp : ¬ P) (hp : P) : Q := by
  exfalso
  contradiction

#eval True ↔ True

#eval True ↔ False

#eval False ↔ True

#eval False ↔ False

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P): P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor

  · case mp =>
      intro h
      exact h hq
  · case mpr =>
      intro hp
      intro hq
      exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  <;>
  intro h

  case mp =>
    exact h hq
  case mpr =>
    intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  rw[h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw[← h]
  exact hp

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw[h]

#eval True ∧ True

#eval True ∧ False

#eval False ∧ True

#eval False ∧ False

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  exact h.right

example (P Q : Prop) (h : P ∧ Q) : P := h.left

example (P Q : Prop) (h : P ∧ Q) : Q := h.right

#eval True ∨ True

#eval True ∨ False

#eval False ∨ True

#eval False ∨ False

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  right
  exact hq

example (P Q : Prop) (hp : P) : P ∨ Q := by
  exact Or.inl hp

example (P Q : Prop) (hq : Q) : P ∨ Q := by
  exact Or.inr hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P  := by
  cases h with
  | inl hp =>
      right
      exact hp
  | inr hq =>
      left
      exact hq

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P  := by
  cases h
  case inl hp =>
    right
    exact hp
  case inr hq =>
    left
    exact hq

-- example (P Q : Prop) (h : P ∨ Q) : Q ∨ P  := by
--   cases h
--   · right
--     exact ht
--   · left
--     exact hq

example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  -- sorry
  intro h
  intro hp
  cases h
  case inl hnp =>
    contradiction
  case inr hq =>
    exact hq

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  --sorry
  constructor
  ·case mp =>
    intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq
  ·case mpr =>
    intro h
    intro hpq
    cases hpq with
    | inl hp =>
        apply h.left
        exact hp
    | inr hq =>
        apply h.right
        exact hq
