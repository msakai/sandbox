-- 6.3 狭義順序を定義する
import LeanBook.NatOrder.OrderDef

-- 6.3.1 狭義順序の定義

def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(·<·), MyNat.lt]
  rfl

-- 6.3.2 狭義順序と広義順序、等号の関係

@[simp] theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h

@[simp] theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  simp

theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  cases h with
  | refl => rfl

@[simp] theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  · apply MyNat.zero_of_le_zero h
  · rw [h]

-- これは書籍にはなかった定理
theorem MyNat.le_succ_monotone {n : MyNat} (h : n ≤ m) : n.succ ≤ m.succ := by
   induction h with
   | refl => rfl
   | step h ih => apply MyNat.le.step ih

theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  cases n with
  | zero => left; rfl
  | succ n =>
    right;
    apply MyNat.le_succ_monotone
    apply MyNat.zero_le

theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  cases h with
  | refl => left; rfl
  | step h => right; apply MyNat.le_succ_monotone; apply h

theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := calc
    _ ≤ a + 1 := by apply MyNat.le_add_one_right
    _ ≤ b     := by exact h

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h => rw [h]
  | inr h => exact MyNat.le_of_lt h

theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  · apply MyNat.eq_or_lt_of_le
  · apply MyNat.le_of_eq_or_lt

theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  dsimp [(·<·), MyNat.lt]
  induction b with
  | zero => right; apply MyNat.zero_le
  | succ b ih =>
      cases ih with
      | inl lt =>
          left
          apply MyNat.le_succ_monotone
          exact MyNat.le_of_lt lt
      | inr ge =>
          rw [MyNat.le_iff_eq_or_lt] at ge
          cases ge with
          | inl eq => left; rw [eq]
          | inr gt => right; exact gt

theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  cases (MyNat.lt_or_ge b a) with
  | inl h2 => exact h2
  | inr h2 => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro hle
  dsimp [(·<·), MyNat.lt] at h
  rw [MyNat.le_iff_add] at h
  rw [MyNat.le_iff_add] at hle
  obtain ⟨k, h1⟩ := h
  obtain ⟨l, h2⟩ := hle
  rw [← h2] at h1
  rw [show (b + l + 1 + k = b + ((l + k) + 1)) by ac_rfl] at h1
  have lem : (l + k) + 1 = 0 := by
          apply MyNat.add_left_cancel h1
  injection lem

theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases MyNat.lt_or_ge a b with
  | inl lt => left; exact MyNat.le_of_lt lt
  | inr ge => right; exact ge

-- 6.3.3 練習問題（回答は203 ページ）

example (a : MyNat) : a ≠ a + 1 := by
  intro h
  have lem1 : a + 0 = a + 1 := calc
    _ = a := by rfl
    _ = a + 1 := by exact h
  have lem2 : 0 = 1 := by
    apply MyNat.add_left_cancel lem1
  injection lem2

example (n : MyNat) : ¬ n + 1 ≤ n := by
  intro h
  exact MyNat.not_le_of_lt h MyNat.le.refl
