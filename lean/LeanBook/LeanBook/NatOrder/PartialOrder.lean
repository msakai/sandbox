-- 6.6 a ≤ b → b ≤ a → a = b を示す
import LeanBook.NatOrder.OrdMonoid

-- 6.6.1 狭義順序と広義順序の推移律

variable {n m k : MyNat}

theorem MyNat.lt_trans (h₁ : n < m) (h₂ : m < k) : n < k := by
  notation_simp at *
  calc n + 1
      ≤ m := by exact h₁
    _ ≤ m + 1 := by simp
    _ ≤ k := by exact h₂

theorem MyNat.lt_of_le_of_lt (h₁ : n ≤ m) (h₂ : m < k) : n < k := by
  notation_simp at *
  calc n + 1
      ≤ m + 1 := by compatible
    _ ≤ k := by exact h₂

theorem MyNat.lt_of_lt_of_le (h₁ : n < m)  (h₂ : m ≤ k) : n < k := by
  notation_simp at *
  calc n + 1
    ≤ m := h₁
  _ ≤ k := h₂

instance: Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance: Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance: Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le

-- 6.6.2 狭義順序の非反射律
@[simp]
theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
  intro h
  notation_simp at h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [show n + 1 + k = n + (k + 1) by ac_rfl] at hk
  simp_all

-- 6.6.3 反対称律
theorem MyNat.le_antisymm (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  induction h₁ with
  | refl => rfl
  | @step m h ih =>
    have : n < n := calc
      _ ≤ m := h
      _ < m + 1 := by notation_simp; rfl
      _ ≤ n := h₂
    simp at this

-- 6.6.4 練習問題 （回答は204 ページ）
example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  cases h with
  | inl h1 =>
      calc a
          ≤ a + 1 := by simp
        _ ≤ b := h1
  | inr h2 => simp_all
