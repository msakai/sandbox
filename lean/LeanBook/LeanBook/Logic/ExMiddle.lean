-- 3.4 排中律と直観主義論理

example (P : Prop) : ¬ ¬ P → P := by
  intro hn2p

  by_cases h : P
  · exact h
  · contradiction

example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  · intro hnpq
    by_cases hp : P
    · right
      intro hq
      apply hnpq
      constructor
      · exact hp
      · exact hq
    ·left
     exact hp
  · intro h
    intro hpq
    cases h with
    | inl hnp =>
      apply hnp
      exact hpq.left
    | inr hnq =>
      apply hnq
      exact hpq.right

example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬  P) := by
  constructor
  · intro h
    intro hnq
    intro hp
    exact hnq (h hp)
  · intro h
    intro hp
    by_cases hh : Q
    · exact hh
    · have : ¬ P := by exact h hh
      contradiction
