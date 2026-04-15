-- 3.2 証明を楽にするコツ
module LeanBook.Logic.Tips where

open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

example1 : (P : Set) → ¬ ¬ ¬ P → ¬ P
example1 P hn3p hp = hn3p hn2p
  where
    hn2p : ¬ ¬ P
    hn2p hnp = hnp hp

example2 : (P : Set) → ¬ ¬ (P ⊎ ¬ P)
example2 P h = h (inj₂ hyp)
  where
    hyp : ¬ P
    hyp hp = h (inj₁ hp)

-- Thare are no 'exact?' in Agda?
example3 : (P : Set) → (P → ⊤) ⇔ ⊤
example3 P = mk⇔ (λ _ →  tt) (λ _ _ → tt)

-- Thare are no 'exact?' in Agda?
example4 : (P : Set) → (⊤ → P) ⇔ P
example4 P = mk⇔ (λ h → h tt) (λ hp _ → hp)

example5 : (P Q : Set) → ((¬ P) ⇔ Q) → (P → ⊥) ⇔ Q
example5 P Q h = h

example6 : (P : Set) → ¬ (P ⇔ (¬ P))
example6 P h = hnp hp
  where
    hnp : ¬ P
    hnp hp = Equivalence.to h hp hp

    hp : P
    hp = Equivalence.from h hnp
