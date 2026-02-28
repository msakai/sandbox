-- 3.3 述語論理
def P (n : Nat) : Prop := n = n

example : ∀ a : Nat, P a := by
  intro x
  dsimp [P]
  -- rfl を入れたくなるがそうするとエラーになる

example (P : Nat → Prop) (h : ∀ x : Nat, P x) : P 0 := by
  exact h 0

def even (n : Nat) : Prop := ∃ m : Nat, n = m + m

example : even 4 := by
  exists 2
  -- ここでも 4 = 2 + 2 というゴールは消えてしまう

example (α : Type) (P Q : α → Prop) (h : ∃ x : α, P x ∧ Q x) : ∃ x : α, Q x := by
  obtain ⟨y, hy⟩ := h
  exists y
  exact hy.right

opaque Human : Type

opaque Love : Human → Human → Prop

@[inherit_doc] infix:50 " -❤️→ " => Love

def IdolExists : Prop := ∃ idol : Human, ∀ h : Human, h -❤️→ idol

def EveryoneLovesSomeone : Prop := ∀ h : Human, ∃ tgt, h -❤️→ tgt

#check ∃ philan : Human, ∀ h : Human, philan -❤️→ h

def PhilanExists : Prop := ∃ philan : Human, ∀ h : Human, philan -❤️→ h

#check ∀ h : Human, ∃ lover : Human, lover -❤️→ h

def EveryoneLoved : Prop := ∀ h : Human, ∃ lover : Human, lover -❤️→ h

example : PhilanExists → EveryoneLoved := by
  intro h
  obtain ⟨philan, hphilan⟩ := h
  dsimp [EveryoneLoved]
  intro human
  exists philan
  exact hphilan human

example : IdolExists → EveryoneLovesSomeone := by
  intro h
  intro human
  obtain ⟨idol, hidol⟩ := h
  exists idol
  exact hidol human
