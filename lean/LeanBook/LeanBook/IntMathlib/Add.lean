-- 8.3 整数が足し算に関してアーベル群であることを利用する

import LeanBook.Int.Basic
import Mathlib.Tactic

-- 8.3.1 整数の足し算を定義する

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ + n₁, m₂ + n₂)⟧

def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m₁, m₂) (n₁, n₂) (m'₁, m'₂) (n'₁, n'₂) rm rn
  dsimp [PreInt.add]
  apply Quotient.sound
  notation_simp at *
  calc
    _ = (m₁ + m'₂) + (n₁ + n'₂) := by ac_rfl
    _ = (m₂ + m'₁) + (n₂ + n'₁) := by rw [rm, rn]
    _ = m₂ + n₂ + (m'₁ + n'₁) := by ac_rfl

instance instaAddMyInt : Add MyInt where
  add := MyInt.add

#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x₁ x₂ y₁ y₂ : MyNat)
    : ⟦(x₁, y₁)⟧ + ⟦(x₂, y₂)⟧ = (⟦(x₁ + x₂, y₁ + y₂)⟧ : MyInt) := by
  dsimp [(· + ·), Add.add, MyInt.add, PreInt.add]
