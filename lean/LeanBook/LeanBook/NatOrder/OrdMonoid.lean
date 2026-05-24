-- 6.5 足し算が順序を保つことを示す
import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

-- 6.5.1 足し算は順序を保つ

variable {a b m n : MyNat}

theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, h⟩  := h
  exists k
  rw [<- h]
  ac_rfl

theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := by apply MyNat.add_le_add_left h l
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := calc
  _ ≤ m + b := by apply MyNat.add_le_add_left h2 m
  _ ≤ n + b := by apply MyNat.add_le_add_right h1 b

-- 6.5.2 足し算が順序を保つことを再利用可能にする

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left h

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  apply MyNat.add_le_add_right hle

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  apply MyNat.add_le_add_right <;> assumption

example (h1 : m ≤ n) (l2 : a ≤ b) : m + a ≤ n + b := by
  apply MyNat.add_le_add <;> assumption

syntax "compatible" : tactic

section
  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_left <;> assumption)

  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
    fail_if_success compatible
    sorry

end

section
  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_left <;> assumption)

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add_right <;> assumption)

  local macro_rules
    | `(tactic| compatible) =>
      `(tactic| apply MyNat.add_le_add <;> assumption)

  example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
    compatible

  example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
    compatible

  example (h : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
    compatible

end

open Lean Elab Tactic in

elab "compatible" : tactic => do
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "`[compatible]` が付与された定理はありません。"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)
      return ()
    catch _ =>
      pure ()
  throwError "ゴールを閉じることができませんでした。"

attribute [compatible] MyNat.add_le_add_left MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by  compatible

example (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by  compatible

example (h : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by  compatible

-- 6.5.3 足し算は狭義順序を保つ

@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat) : k + m < k + n := by
  notation_simp at *
  rw [show k + m + 1 = k + (m + 1) by ac_rfl]
  compatible

-- 6.5.4 順序についても足し算はキャンセル可能

section

variable (m n k : MyNat)

theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
  intro h
  rw [le_iff_add] at *
  obtain ⟨d, h⟩ := h
  rw [show k + m + d = k + (m + d) by ac_rfl] at h
  have h2 : m + d = n := by apply MyNat.add_left_cancel h
  exists d

theorem MyNat.le_of_add_le_add_right : m + k ≤ n + k → m ≤ n := by
  rw [MyNat.add_comm m k, MyNat.add_comm n k]
  apply MyNat.le_of_add_le_add_left

@[simp] theorem MyNat.le_of_add_le_iff_left : k + m ≤ k + n ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_left
  · intro h
    compatible

@[simp] theorem MyNat.le_of_add_le_iff_right : m + k ≤ n + k ↔ m ≤ n := by
  constructor
  · apply MyNat.le_of_add_le_add_right
  · intro h
    compatible

end

-- 6.5.5 練習問題 （回答は204ページ）

variable (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat)

example (h1 : m₁ ≤ m₂) (h2 : n₁ ≤ n₂) (h3 : l₁ ≤ l₂) : l₁ + m₁ + n₁ ≤ l₂ + n₂ + m₂ := calc
  _ ≤ l₁ + m₁ + n₂ := by compatible
  _ ≤ l₁ + m₂ + n₂ := by apply MyNat.add_le_add_right; compatible
  _ ≤ l₂ + m₂ + n₂ := by apply MyNat.add_le_add_right; compatible
  _ = l₂ + n₂ + m₂ := by ac_rfl
