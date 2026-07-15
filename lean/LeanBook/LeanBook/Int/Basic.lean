-- 7.3 整数を作る

import LeanBook.NatOrder.DecidableOrd

-- 7.3.1 MyNat を元に整数を構成する

abbrev PreInt := MyNat × MyNat

def PreInt.r (m n : PreInt) : Prop :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => m₁ + n₂ = m₂ + n₁

theorem PreInt.r.refl : ∀ (m : PreInt), r m m := by
  intro (m₁, m₂)
  dsimp [r]
  ac_rfl

theorem PreInt.r.symm : ∀ {m n : PreInt}, r m n → r n m := by
  intro (m₁, m₂) (n₁, n₂) h
  dsimp [r] at *
  calc
  _ = n₁ + m₂ := by rfl
  _ = m₂ + n₁ := by ac_rfl
  _ = m₁ + n₂ := by rw [<- h]
  _ = n₂ + m₁ := by ac_rfl

theorem PreInt.r.trans : ∀ {l m n : PreInt}, r l m → r m n → r l n := by
  intro (l₁, l₂) (m₁, m₂) (n₁, n₂) hlm hmn
  dsimp [r] at *
  have : m₁ + (l₁ + n₂) = m₁ + (l₂ + n₁) := by calc
    _ = m₁ + n₂ + l₁ := by ac_rfl
    _ = m₂ + n₁ + l₁ := by rw [hmn]
    _ = l₁ + m₂ + n₁ := by ac_rfl
    _ = l₂ + m₁ + n₁ := by rw [hlm]
    _ = m₁ + (l₂ + n₁) := by ac_rfl
  simp_all

theorem PreInt.r.equiv : Equivalence r :=
  { refl := r.refl
  , symm := r.symm
  , trans := r.trans
  }

@[instance] def PreInt.sr : Setoid PreInt := ⟨r, r.equiv⟩

abbrev MyInt := Quotient PreInt.sr

-- 7.3.2 同値類のための記法を用意する

#check
  let a : PreInt := (1, 3)
  (Quotient.mk PreInt.sr a : MyInt)

#check
  let a : PreInt := (1, 3)
  Quotient.mk _ a

notation:arg (priority := low) "⟦" a "⟧" => Quotient.mk _ a

#check (⟦ (1, 3) ⟧ : MyInt)
