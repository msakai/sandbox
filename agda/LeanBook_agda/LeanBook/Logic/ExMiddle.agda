-- 3.4 排中律と直観主義論理
module LeanBook.Logic.ExMiddle where

open import Axiom.ExcludedMiddle
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function
open import Level
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable

module _ (em : ExcludedMiddle 0ℓ) where

  example1 : (P : Set) → ¬ ¬ P → P
  example1 P ¬¬p with em {P}
  ... | yes p = p
  ... | no ¬p = ⊥-elim (¬¬p ¬p)

  example2 : (P Q : Set) → (¬ (P × Q)) ⇔ (¬ P ⊎ ¬ Q)
  example2 P Q = mk⇔ to from
    where
      to : ¬ (P × Q) → (¬ P ⊎ ¬ Q)
      to ¬pq with em {P}
      ... | yes p = inj₂ (λ q → ¬pq (p , q))
      ... | no ¬p = inj₁ ¬p

      from : (¬ P ⊎ ¬ Q) → ¬ (P × Q)
      from (inj₁ ¬p) (p , _) = ¬p p
      from (inj₂ ¬q) (_ , q) = ¬q q

  example3 :  (P Q : Set) → ((P → Q) ⇔ (¬ Q → ¬ P))
  example3 P Q = mk⇔ to from
    where
      to : (P → Q) → (¬ Q → ¬ P)
      to p→q ¬q p = ¬q (p→q p)

      from : (¬ Q → ¬ P) → (P → Q)
      from ¬q→¬p p with em {Q}
      ... | yes q = q
      ... | no ¬q = ⊥-elim (¬q→¬p ¬q p)
