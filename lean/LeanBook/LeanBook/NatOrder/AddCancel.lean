-- 6.1 a + b = a + c → b = c を証明する
import LeanBook.NatSemiring.Distrib

-- 6.1.1 ペアノの公理再び

example (n : MyNat) : MyNat.succ n ≠ MyNat.zero := by
  intro h
  injection h

example (m n : MyNat) (h : MyNat.succ m = MyNat.succ n) : m = n := by
  injection h

example (m n : MyNat) (h : m + 1 = n + 1) : m = n := by
  injection h

-- 6.1.2 足し算のキャンセル可能性の証明

variable {l m n : MyNat}

theorem MyNat.add_right_cancel (h : l + m = n + m) : l = n := by
  induction m with
  | zero => simp_all
  | succ m ih =>
    have lem : (l + m) + 1 = (n + m) + 1 := calc
      _ = l + (m + 1) := by ac_rfl
      _ = n + (m + 1) := by rw [h]
      _ = (n + m) + 1 := by ac_rfl
    have : l + m = n + m := by
      injection lem
    exact ih this

theorem MyNat.add_left_cancel (h : l + m = l + n) : m = n := by
  rw [MyNat.add_comm l m, MyNat.add_comm l n] at h
  apply MyNat.add_right_cancel h

-- 6.1.3 simp タクティクで利用できるようにする

section
  attribute [local simp] MyNat.add_left_cancel

  example : l + m = l + n → m = n := by
    fail_if_success simp
    sorry

end

@[simp↓] theorem MyNat.add_right_cancel_iff : l + m = n + m ↔ l = n := by
  constructor
  · apply MyNat.add_right_cancel
  · intro h
    rw [h]

@[simp↓] theorem MyNat.add_left_cancel_iff : l + m = l + n ↔ m = n := by
  constructor
  · apply MyNat.add_left_cancel
  · intro h
    rw [h]

@[simp] theorem MyNat.add_right_eq_self : m + n = m ↔ n = 0 := by
  constructor <;> intro h
  case mpr => simp_all
  case mp =>
    have lem : m + n = m + 0 := by
      rw [h]
      simp
    -- exact MyNat.add_left_cancel lem
    simp_all

@[simp] theorem MyNat.add_left_eq_self : n + m = m ↔ n = 0 := by
  rw [MyNat.add_comm n m, MyNat.add_right_eq_self]

@[simp] theorem MyNat.self_eq_add_right : m = m + n ↔ n = 0 := by
  rw [eq_comm]
  simp

@[simp] theorem MyNat.self_eq_add_left : m = n + m ↔ n = 0 := by
  rw [eq_comm]
  simp

-- 6.1.4 応用： a * b = 0 ↔ a = 0 ∨ b = 0

theorem MyNat.eq_zero_of_add_eq_zero : m + n = 0 → m = 0 ∧ n = 0 := by
  intro h
  cases n
  case zero =>
    constructor
    case left => exact h
    case right => rfl
  case succ =>
    rw [MyNat.add_succ] at h
    injection h

theorem MyNat.add_eq_zero_of_eq_zero : m = 0 ∧ n = 0 → m + n = 0 := by
  intro h
  simp_all

@[simp]
theorem MyNat.add_eq_zero_iff_eq_zero : m + n = 0 ↔ m = 0 ∧ n = 0 := by
  constructor
  case mp => exact MyNat.eq_zero_of_add_eq_zero
  case mpr => exact MyNat.add_eq_zero_of_eq_zero

@[simp]
theorem MyNat.mul_eq_zero (m n : MyNat) : m * n = 0 ↔ m = 0 ∨ n = 0 := by
  constructor <;> intro h

  case mpr =>
    cases h <;> simp_all

  case mp =>
    cases n
    case zero => right; rfl
    case succ n' =>
      rw [show n'.succ = n' + 1 by rfl, MyNat.mul_add_one m n'] at h
      simp_all

-- 6.1.5 練習問題（回答は203 ページ）

example (n m : MyNat) : n + (1 + m) = n + 2 → m = 1 := by
  intro h
  rw [show 2 = 1 + 1 by rfl] at h
  simp_all
