-- 3.1 命題論理
module LeanBook.Logic.PropLogic where

open import Data.Empty
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

-- 3.1.1 命題

-- C-c C-d Set

-- C-c C-d (λ n → n + 3 ≡ 39)

-- C-c C-d ⊤

-- C-d C-d ⊥

example1 : ⊤
example1 = tt

-- 3.1.2 仮定を使う

example2 : (P : Set) → P → P
example2 P h = h

example3 : ⊥ → ∀ x y z n → n ≥ 3 → x ^ n + y ^ n + z ^ n ≡ 0
example3 ()

-- 3.1.3 含意 (→)

example4 : (P Q R : Set) → (P → Q → R) ≡ (P → (Q → R))
example4 P Q R = refl

example5 : (P Q : Set) → (P → Q) → P → Q
example5 P Q h hp = h hp

example6 : (P Q : Set) → Q → P → Q
example6 P Q hq hp = hq

-- 3.1.4 否定 (¬)

example7 : (P : Set) → (¬ P) ≡ (P → ⊥)
example7 P = refl

example8 : (P : Set) → ¬ P → P → ⊥
example8 P hnp hp = hnp hp

example9 : (P Q : Set) → (P → ¬ Q) → Q → ¬ P
example9 P Q h hq hp = h hp hq

example10 : (P : Set) → ¬ P → P → ⊥
example10 P hnp hp = hnp hp

example11 : (P Q : Set) → ¬ P → P → Q
example11 P Q hnp hp = ⊥-elim (hnp hp)

-- 3.1.5 同値性 (↔)

example12 : (P Q : Set) → (P → Q) → (Q → P) → P ⇔ Q
example12 P Q h1 h2 = mk⇔ h1 h2

example13 : (P Q : Set) → Q → (Q → P) ⇔ P
example13 P Q hq = mk⇔ (λ f → f hq) (λ hp hq → hp)

example14 : (P Q : Set) → (P ⇔ Q) → Q → P
example14 P Q h = Equivalence.from h

example15 : (P Q : Set) → (P ⇔ Q) → P → Q
example15 P Q h = Equivalence.to h

-- -- propositional extensinality does not hold in Agda
-- example16 : (P Q : Set) → (P ⇔ Q) → P ≡ Q
-- example16 P Q h = {!!}

-- 3.1.6 論理積 (∧)

example17 : (P Q : Set) → P → Q → P × Q
example17 P Q hp hq = (hp , hq)

example18 : (P Q : Set) → P × Q → P
example18 P Q h = proj₁ h

example19 : (P Q : Set) → P × Q → Q
example19 P Q h = proj₂ h

example20 : (P Q : Set) → P → P ⊎ Q
example20 P Q hp = inj₁ hp

example21 : (P Q : Set) → Q → P ⊎ Q
example21 P Q hq = inj₂ hq

-- 3.1.7 論理和 (∨)

example22 : (P Q : Set) → P ⊎ Q → Q ⊎ P
example22 P Q (inj₁ p) = inj₂ p
example22 P Q (inj₂ q) = inj₁ q

example23 : (P Q : Set) → (¬ P ⊎ Q) → (P → Q)
example23 P Q (inj₁ hnp) hp = ⊥-elim (hnp hp)
example23 P Q (inj₂ hq) _hp = hq

example24 : (P Q : Set) → (¬ (P ⊎ Q)) ⇔ (¬ P × ¬ Q)
example24 P Q = mk⇔ to from
  where
    to : ¬ (P ⊎ Q) → (¬ P × ¬ Q)
    to h = (h ∘ inj₁ , h ∘ inj₂)

    from : ¬ P × ¬ Q → ¬ (P ⊎ Q)
    from (hnp , _hnq) (inj₁ hp) = hnp hp
    from (_hnp , hnq) (inj₂ hq) = hnq hq
