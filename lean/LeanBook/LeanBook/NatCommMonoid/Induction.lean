import LeanBook.NatCommMonoid.TypeClass

-- example (n : MyNat) : 0 + n = n := by
--   rfl

#reduce fun (n : MyNat) => n + 0

#reduce fun (n : MyNat) => 0 + n

theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [<- MyNat.add_zero_rev]

example (m n : MyNat) (h : m + 0 = n) : n + m = m + n := by
  rw [MyNat.add_zero] at h
  rw [h]

theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

set_option pp.fieldNotation.generalized false in

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    guard_target =ₛ 0 + MyNat.zero = MyNat.zero
    rfl
  | succ n' ih =>
      guard_target =ₛ 0 + MyNat.succ n' = MyNat.succ n'
      guard_hyp ih : 0 + n' = n'
      rw [MyNat.add_succ]
      rw [ih]

example (n : MyNat) : 1 + n = .succ n := by
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    rw [MyNat.add_succ]
    rw [ih]
