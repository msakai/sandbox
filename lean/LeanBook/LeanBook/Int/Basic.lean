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

-- 7.3.3 数値リテラルが使えるようにする

def MyInt.ofNat (n : Nat) : MyInt := ⟦ (MyNat.ofNat n, 0) ⟧

instance {n : Nat} : OfNat MyInt n where
  ofNat := MyInt.ofNat n

#check (4 : MyInt)

#check_failure (-4 : MyInt)

def PreInt.neg : PreInt → MyInt
  | (m, n) => ⟦ (n, m) ⟧

@[notation_simp]
theorem MyInt.sr_def (m n : PreInt) : m ≈ n ↔ m.1 + n.2 = m.2 + n.1 := by
  rfl

def MyInt.neg : MyInt → MyInt := Quotient.lift PreInt.neg <| by
  intro (a₁, a₂) (b₁, b₂) hab

  have : (a₂, a₁) ≈ (b₂, b₁) := by
    notation_simp at *
    simp_all

  dsimp [PreInt.neg]
  rw [Quotient.sound]
  assumption

instance : Neg MyInt where
  neg := MyInt.neg

@[simp]
theorem MyInt.neg_def (x y : MyNat) : - ⟦ (x,y)⟧ = (⟦(y, x)⟧ : MyInt) := by
  dsimp [Neg.neg, MyInt.neg, PreInt.neg]
  rfl

#check (-4 : MyInt)

#check_failure -4

-- テキストでこれを check しているのは何故?
#check Setoid

-- 7.3.4 練習問題 （回答は206 ページ）

variable {α : Type} {r : α → α → Prop}

private theorem Ex.symm (refl : ∀ x, r x x) (h : ∀ x y z, r x y → r y z → r z x)
    : ∀ {x y : α}, r x y → r y x := by
  intro x y rxy
  exact h x y y rxy (refl y)

private theorem Ex.equiv (refl : ∀ x, r x x)
    (h : ∀ x y z, r x y → r y z → r z x) : Equivalence r := by
  constructor

  case refl =>
    intro x
    exact refl x

  case symm =>
    intro x y rxy
    exact Ex.symm refl h rxy

  case trans =>
    intro x y z rxy ryz
    exact Ex.symm refl h (h x y z rxy ryz)
