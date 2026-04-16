-- 3.3 述語論理
module LeanBook.Logic.PredLogic where

open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

P : (n : ℕ) → Set
P n = n ≡ n

example1 : ∀ a → P a
example1 a = refl

example2 : (P : ℕ → Set) (h : ∀ x → P x) → P 0
example2 P h = h 0

even : (n : ℕ) → Set
even n = ∃[ m ] n ≡ m + m

example3 : even 4
example3 = (2 , refl)

example4 : (α : Set) (P Q : α → Set) (h : ∃[ x ] P x × Q x) → ∃[ x ] Q x
example4 α P Q (x , (px , qx)) = (x , qx)

module _ (Human : Set) (Love : Human → Human → Set) where
  infix 5 _-❤️→_

  _-❤️→_ : Human → Human → Set
  _-❤️→_ = Love

  IdolExists : Set
  IdolExists = ∃[ idol ] ∀ h → h -❤️→ idol

  EveryoneLovesSomeone : Set
  EveryoneLovesSomeone = ∀ h → ∃[ tgt ] h -❤️→ tgt

  PhilanExists : Set
  PhilanExists = ∃[ philan ] (∀ h → (philan -❤️→ h))

  EveryoneLoved : Set
  EveryoneLoved = ∀ h → ∃[ lover ] lover -❤️→ h

  example5 : PhilanExists → EveryoneLoved
  example5 ( philan , hphilan ) human = (philan , hphilan human)

  example6 : IdolExists → EveryoneLovesSomeone
  example6 ( idol , hidol ) human =  (idol , hidol human)
