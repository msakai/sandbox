-- 3.2 証明を楽にするコツ

example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  intro hn3p hp

  have hn2p : ¬ ¬ P := by
    intro hnp
    contradiction

  contradiction

example (P : Prop) : ¬ ¬ ¬ P → ¬ P := by
  intro hn3p hp

  have : ¬ ¬ P := by
    intro hnp
    contradiction

  guard_hyp this : ¬ ¬ P

  contradiction

example (P : Prop) : ¬ ¬ (P ∨ ¬ P) := by
  intro h

  suffices hyp : ¬ P from by
    have : P ∨ ¬ P := by
      right
      exact hyp

    contradiction

  guard_target =ₛ ¬ P

  intro hp

  have : P ∨ ¬ P := by
    left
    exact hp

  contradiction

example (P : Prop) : (P → True) ↔ True := by
  -- exact?
  exact imp_true_iff P

example (P : Prop) : (True → P) ↔ P := by
  -- exact?
  exact true_imp_iff

example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  -- exact h
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h

  have : ¬ P := by
    intro hp
    apply h.mp
    exact hp
    exact hp

  have : P := by
    apply h.mpr
    exact this

  contradiction
