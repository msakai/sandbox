
-- 7.2 商とQuotient

-- 7.2.1 Quotient.mk：同値類を取る操作

section
  variable {α : Type} (sr : Setoid α)
  #check (Quotient.mk sr : α → Quotient sr)
  #print Quotient.mk
end

-- 7.2.2 Quotient.inductionOn：同値類の代表元を取る

section
  variable {α : Type} (sr : Setoid α)

  example (a : Quotient sr) : True := by
    induction a using Quotient.inductionOn with
    | h x =>
      guard_hyp x : α
      trivial
end

-- 7.2.3 Quotient.lift：関数を商へ持ち上げる操作

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : β → α)

  #check (Quotient.mk sr ∘ f : β → Quotient sr)
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)
  -- variable (f : α → β) (h : ∀ x y, (·≈·) x y → f x = f y)

  -- ≈ は HasEquiv.Equiv に対する notation らしい。
  #print HasEquiv
  #synth HasEquiv α
  #print instHasEquivOfSetoid

  #print Quotient.lift

  #check (Quotient.lift f h : Quotient sr → β)
end

section
  variable {α β : Type} (sr : Setoid α)
  variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)

  example : ∀ x , (Quotient.lift f h) (Quotient.mk sr x) = f x := by
    intro x
    rfl
end

-- 7.2.4 Quotient.sound：同値なら商へ送って等しい

section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α) (h : x ≈ y)

  example : Quotient.mk sr x = Quotient.mk sr y := by
    apply Quotient.sound
    exact h

  #print Quotient.sound
end

-- 7.2.5 Quotient.exact：商に送って等しいなら同値

section
  variable {α : Type} (sr : Setoid α)
  variable (x y : α)

  example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
    exact Quotient.exact h

  #print Quotient.exact
end

-- 7.2.6 練習問題（回答は205 ページ）

private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop) : α → α → Prop :=
  fun x y => r (f x) (f y)

#print Equivalence

private def Setoid.comap {α β : Type} (f : α → β) (sr : Setoid β) : Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    constructor

    case refl =>
      intro x
      dsimp [Rel.comap]
      apply sr.iseqv.refl

    case symm =>
      intro x y
      dsimp [Rel.comap]
      apply sr.iseqv.symm

    case trans =>
      intro x y z
      dsimp [Rel.comap]
      apply sr.iseqv.trans
