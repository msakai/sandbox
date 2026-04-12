-- import LeanBook.NatCommMonoid.Induction
import LeanBook.NatCommMonoid.AcRfl

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    guard_target =ₛ m + MyNat.zero = MyNat.zero + m
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    guard_target =ₛ m + MyNat.succ n = MyNat.succ n + m
    simp [ih]

#check MyNat.rec

def MyNat.recAux.{u} {motive : MyNat -> Sort u}
  (zero : motive 0)
  (succ : (n :MyNat) -> motive n -> motive (n + 1))
  (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    guard_target =ₛ m + 0 = 0 + m
    simp []
  | succ n ih =>
    guard_target =ₛ m + (n + 1) = (n + 1) + m
    ac_rfl

private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  cases n <;> rfl
