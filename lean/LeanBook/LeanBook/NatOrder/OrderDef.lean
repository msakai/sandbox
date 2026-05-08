-- 6.2 順序を定義する

import LeanBook.NatOrder.AddCancel

-- 6.2.1 順序関係を帰納的に定義する

inductive MyNat.le (n : MyNat) : MyNat → Prop
  | refl : MyNat.le n n
  | step {m : MyNat} : MyNat.le n m → MyNat.le n (m + 1)

instance : LE MyNat where
  le := MyNat.le

-- 6.2.2 帰納型では帰納法が使える

example (m n : MyNat) (P : MyNat → MyNat → Prop) (h : m ≤ n) : P m n := by
  induction h with
  | refl =>
      guard_target =ₛ P m m
      sorry
  | @step n h ih =>
      guard_hyp ih : P m n
      guard_target =ₛ P m (n + 1)
      sorry

#check MyNat.le.rec

def MyNat.le.recAux {n b : MyNat}
  {motive : (a : MyNat) → n ≤ a → Prop}
  (refl : motive n MyNat.le.refl)
  (step : ∀ {m : MyNat} (a : n ≤ m),
    motive m a → motive (m + 1) (MyNat.le.step a))
  (t : n ≤ b)
  : motive b t := by
  induction t with
  | refl => exact refl
  | @step c h ih =>
    exact step (a := h) ih

-- 6.2.3 反射律と推移律を示す

theorem MyNat.le_refl (n : MyNat) : n ≤ n := by
  exact MyNat.le.refl

variable {m n k : MyNat}

theorem MyNat.le_step (h : n ≤ m) : n ≤ m + 1 := by
  exact MyNat.le.step h

theorem MyNat.le_trans (hnm : n ≤ m) (hmk : m ≤ k) : n ≤ k := by
  induction hmk with
  | refl => exact hnm
  | @step k hmk ih =>
      apply MyNat.le_step
      apply ih

attribute [refl] MyNat.le_refl

theorem MyNat.le_add_one_right (n : MyNat) : n ≤ n + 1 := by
  apply MyNat.le_step
  rfl

instance : Trans (·≤· : MyNat → MyNat → Prop) (·≤·) (·≤·) where
  trans := MyNat.le_trans

theorem MyNat.le_add_one_left (n : MyNat) : n ≤ 1 + n := calc
  _ ≤ n + 1 := by apply le_add_one_right
  _ = 1 + n := by ac_rfl

attribute [simp] MyNat.le_refl MyNat.le_add_one_right MyNat.le_add_one_left

-- 6.2.4 順序関係を和の等式に書き換える

theorem MyNat.le.dest (h : n ≤ m) : ∃ k, n + k = m := by
  induction h with
  | refl => exists 0
  | @step l h ih =>
     obtain ⟨k, ih⟩ := ih
     exists k + 1
     rw [← ih]
     ac_rfl

theorem MyNat.le_add_right (n m : MyNat) : n ≤ n + m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show n + (m + 1) = (n + m) + 1 from by ac_rfl]
      exact MyNat.le_step ih

theorem MyNat.le.intro (h : n + k = m) : n ≤ m := by
  rw [← h]
  apply MyNat.le_add_right

theorem MyNat.le_iff_add : n ≤ m ↔ ∃ k, n + k = m := by
  constructor <;> intro h
  case mp => exact MyNat.le.dest h
  case mpr =>
    obtain ⟨k, h⟩ := h
    exact MyNat.le.intro h

-- 6.2.5 練習問題（回答は203 ページ）

example : 1 ≤ 4 := by
  exact MyNat.le_add_right 1 3
