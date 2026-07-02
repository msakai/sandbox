-- 6.7 順序関係を決定可能にする
import LeanBook.NatOrder.PartialOrder

example : 0 ≤ 1 := by
  apply MyNat.le.step
  apply MyNat.le.refl

example : 0 ≤ 3 := by
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.refl

-- 6.7.1 Decidable 型クラス

-- 6.7.2 例：等号を決定可能にする

deriving instance DecidableEq for MyNat

example : 32 + 13 ≠ 46 := by
  decide

#eval 1 ≠ 2

-- 6.7.3 順序関係を計算する

def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | a + 1, 0 => false
  | a + 1, b + 1 => MyNat.ble a b

#eval MyNat.ble 0 1

#eval MyNat.ble 4 3

#eval MyNat.ble 3 12

-- 6.7.4 functional induction

#check decidable_of_iff

instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  guard_target =ₛ MyNat.ble a b = true ↔ a ≤ b
  sorry

#check MyNat.ble.induct

@[simp]
theorem MyNat.ble_zero_left (n : MyNat) : MyNat.ble 0 n = true := by
  rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) : MyNat.ble (n + 1) 0 = false := by
  rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat)
  : MyNat.ble (m + 1) (n + 1) = MyNat.ble m n := by rfl

def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
    (case1 : ∀ (n : MyNat), motive 0 n)
    (case2 : ∀ (n : MyNat), motive (n + 1) 0)
    (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
    (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n = true ↔ m ≤ n := by
  induction m, n using MyNat.ble.inductAux with
  | case1 n =>
      simp
  | case2 n =>
      -- テキストではここで dsimp [MyNat.ble]　が使われているが、効果がない
      suffices ¬ n + 1 ≤ 0 from by simp_all
      intro
      simp_all
  | case3 m n ih =>
      -- テキストではここで dsimp [MyNat.ble]　が使われているが、効果がない
      simp [ih]

-- 6.7.5 順序関係を決定可能にする

#check DecidableLE

#check decidable_of_iff

instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m = true) (MyNat.le_impl n m)

#eval 1 ≤ 3

#eval 12 ≤ 13

example : 1 ≤ 9 := by
  decide

example : 32 ≤ 47 := by
  decide

example : 2 ≤ 1 := by
  -- decide
  -- tactic 'decide' proved that the proposition
  --   fail_if_success2 ≤ 1
  -- is false
  fail_if_success decide
  sorry

theorem MyNat.lt_impl (m n : MyNat) : MyNat.ble (m + 1) n ↔ m < n := by
  rw [MyNat.le_impl]
  rfl

instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m = true) (MyNat.lt_impl n m)

example : 1 < 4 := by
  decide

-- 6.7.6 練習問題

example : 23 < 32 ∧ 12 ≤ 24 := by
  decide
