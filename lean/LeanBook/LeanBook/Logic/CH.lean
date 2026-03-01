-- 3.6 カリー・ハワード同型対応

theorem one_add_one_eq_two : 1 + 1 = 2 := by
  rfl

#check one_add_one_eq_two

#check (by rfl : 1 + 1 = 2)

example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  exact h hp

def idOnNat : Nat → Nat := by?
  intro n
  exact n

#eval idOnNat 42

example (P Q : Prop) (hp : P) : Q → P := by?
  intro hq
  exact hp

#check Nat.add_zero

#check Nat.add_zero 0

#check Nat.add_zero 42

#check (Nat.add_zero : (n : Nat) → n + 0 = n)

example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by
  rfl

set_option pp.foralls false in

#check (∀ n : Nat, n + 0 = n)

-- inductive List (α : Type) : Type where
--   | nil
--   | cons (a : α) (l : List α)

example : List Nat := [0, 1, 2, 3]

example : List Nat := [0, 1]

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons {n : Nat}: α → Vect α n → Vect α (n + 1)

example : Vect Nat 0 := Vect.nil

example : Vect Nat 1 := Vect.cons 42 Vect.nil

example : (α : Type) × α := ⟨Nat, 1⟩

example : (α : Type) × α := ⟨Bool, true⟩

example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩]

example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) :=
  Vect.cons
