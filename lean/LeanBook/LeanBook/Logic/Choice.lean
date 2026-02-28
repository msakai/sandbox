-- 3.5 選択原理

#check Classical.em

#print axioms Classical.em

#check Classical.choice

def Surjective {X Y : Type} (f : X → Y) : Prop :=
  ∀ y : Y, ∃ x : X, f x = y

example : Surjective (fun x : Nat => x) := by
  intro y
  exists y

variable {X Y : Type}

noncomputable def inverse (f : X → Y) (hf : Surjective f) : Y → X := by
  intro y

  -- let ⟨x, hx⟩ := hf y とすることはできず、
  -- tactic 'induction' failed, recursor 'Exists.casesOn' can only eliminate into Prop
  -- といったエラーになる。

  have : Nonempty {x // f x = y} := by
    obtain ⟨x, hx⟩ := hf y
    exists x

  have x := Classical.choice this
  exact x.val

theorem double_negation_of_contra_equiv (P : Prop)
  (contra_equiv : ∀ (P Q : Prop), (¬ P → ¬ Q) ↔ (Q → P)) : ¬ ¬ P → P := by
  intro hn2p
  apply (contra_equiv P True).mp
  intro hnt
  intro ht
  contradiction
  constructor
