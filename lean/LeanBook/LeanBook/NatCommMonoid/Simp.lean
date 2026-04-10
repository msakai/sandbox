import LeanBook.NatCommMonoid.Induction

example (n : MyNat) : 0 + (n + 0) = n := by
  fail_if_success simp
  rw [MyNat.add_zero, MyNat.zero_add]

attribute [simp] MyNat.add_zero MyNat.zero_add

example (n : MyNat) : 0 + (n + 0) = n := by
  simp

theorem MyNat.ctor_eq_zero : MyNat.zero = 0 := by
  rfl

example : MyNat.zero = 0 := by
  simp [MyNat.ctor_eq_zero]

attribute [simp] MyNat.add_succ

example (m n : MyNat) (h : m + n + 0 = n + m) : m + n = n + m := by
  simp at h
  guard_hyp h : m + n = n + m
  rw [h]

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp at *
  guard_hyp h : m = n
  guard_target =ₛ m = n
  rw [h] -- apply h でも良い

example (m n : MyNat) (h : m + 0 = n) : (m + 0) + 0 = n := by
  simp_all

@[simp] theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp [ih]

example (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with
  | zero => rfl
  | succ n' ih => calc
    _ = (m.succ + n').succ := by rw [MyNat.add_succ]
    _ = (m + n').succ.succ := by rw [ih]

example (n : MyNat) : 1 + n = n + 1 := calc
  _ = .succ 0 + n := by rfl
  _ = .succ (0 + n) := by rw [MyNat.succ_add]
  _ = .succ n := by rw [MyNat.zero_add]
  _ = n + 1 := by rfl

example (n : MyNat) : MyNat.zero.succ.succ + n = (1 + n).succ := by
  rw [MyNat.succ_add]
  rfl

example (n : MyNat) : 2 + n = n + 2 := calc
  _ = MyNat.zero.succ.succ + n := by rfl
  _ = (MyNat.zero.succ + n).succ := by rw [MyNat.succ_add]
  _ = (MyNat.zero + n).succ.succ := by rw [MyNat.succ_add]
  _ = (0 + n).succ.succ := by rfl
  _ = n.succ.succ := by rw [MyNat.zero_add]
  _ = n + 2 := by rfl
