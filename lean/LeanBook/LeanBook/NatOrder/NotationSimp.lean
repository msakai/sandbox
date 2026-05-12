-- 6.4 記法の展開を楽にする
import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

-- 6.4.1 simp による方法
theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by
  rfl

-- section
--   attribute [local simp] MyNat.lt_def
--
--   example (m n : MyNat) : m < n := by
--     simp
--     guard_target =ₛ m + 1 ≤ n
--     sorry

-- 6.4.2 simp ラッパーを作成する
section

open Lean Parser Tactic

syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)
end

attribute [notation_simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  notation_simp
  guard_target =ₛ m + 1 ≤ n
  sorry

example (m n : MyNat) (h : m < n) : m + 1 ≤ n := by
  notation_simp at *
  assumption

-- example (m n : MyNat) : m < n := by
--   simp

-- 6.4.3 notation_simp? を定義する
section

open Lean Parser Tactic

syntax "notation_simp?" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)
end

example (m n : MyNat) : m < n := by
  notation_simp?
  sorry

-- 6.4.4 練習問題 （回答は204 ページ）
example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  have h3 : ¬ (b ≤ a) := MyNat.not_le_of_lt h1
  have h4 : b ≤ a := MyNat.le_of_lt h2
  contradiction
