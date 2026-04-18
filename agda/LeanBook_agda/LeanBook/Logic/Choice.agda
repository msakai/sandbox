-- 3.5 選択原理
module LeanBook.Logic.Choice where

open import Data.Unit
open import Data.Product
open import Function hiding (Surjective)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

Surjective : {X Y : Set} (f : X → Y) → Set
Surjective {X} f = ∀ y → ∃[ x ] (f x ≡ y)

variable
  X Y : Set

inverse : (f : X → Y) → Surjective f → (Y → X)
inverse f hf y with hf y
... | (x , _) = x

double_negation_of_contra_equiv
  : (P : Set)
  → (∀ (P Q : Set) → ((¬ P → ¬ Q) ⇔ (Q → P)))
  → ¬ ¬ P → P
double_negation_of_contra_equiv P contra_equiv ¬¬p =  Equivalence.to (contra_equiv P ⊤) h tt
  where
    h : ¬ P → ¬ ⊤
    h ¬p _ = ¬¬p ¬p
