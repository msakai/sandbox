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
