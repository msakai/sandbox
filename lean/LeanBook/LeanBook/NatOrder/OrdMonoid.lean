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
