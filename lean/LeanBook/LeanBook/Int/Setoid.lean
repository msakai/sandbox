-- 第7章 同値関係で割って整数を作る

-- 7.1 同値関係

-- 7.1.1 Lean の構造体

structure Point where
  x : Int
  y : Int

#check { x := 1, y := 2 : Point }

#check Point.mk

#check Point.mk 1 2

#check Point.x

#check Point.y

#eval
  let p : Point := { x := 1, y := 2 }
  p.x

-- 7.1.2 Equivalence

#print Equivalence

example {α : Type} (r : α → α → Prop) (h : Equivalence r) : ∀ x, r x x := by
  exact h.refl

example (α : Type) : Equivalence (fun x y : α => x = y) := by
  constructor

  case refl =>
    intro x
    rfl

  case symm =>
    intro x y h
    rw [h]

  case trans =>
    intro x y z hxy hyz
    rw [hxy, hyz]

-- 7.1.3 Setoid

#print Setoid

example {α : Type} (sr : Setoid α) (x y : α) : sr.r x y = (x ≈ y) :=
  rfl

-- 7.1.4 練習問題（回答は205 ページ）

example {α : Type} : Equivalence (fun _x _y : α => True) := by
  constructor

  case refl =>
    simp

  case symm =>
    intro x y hxy
    simp

  case trans =>
    intro x y z hxy hyz
    simp
