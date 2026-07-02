-- 6.7 順序関係を決定可能にする
module LeanBook.NatOrder.DecidableOrd where

open import Data.Bool using (Bool; true; false)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import LeanBook.NatOrder.PartialOrder public

module _ where private
  example1 : 0 ≤ 1
  example1 = ≤-step ≤-refl

  example2 : 0 ≤ 3
  example2 = ≤-step (≤-step (≤-step ≤-refl))

-- 6.7.1 Decidable 型クラス

-- 6.7.2 例：等号を決定可能にする

infix 4 _≟_
_≟_ : DecidableEquality MyNat
zero ≟ zero = yes refl
succ x ≟ zero = no (λ ())
zero ≟ succ y = no (λ ())
succ x ≟ succ y with x ≟ y
... | yes x≡y = yes (cong succ x≡y)
... | no x≢y = no (λ x+1≡y+1 → x≢y (succ-cancel x+1≡y+1))

module _ where private
  example : 32 + 13 ≢ 46
  example with 32 + 13 ≟ 46
  ... | no p = p

-- C-c C-n 1 ≟ 2

-- 6.7.3 順序関係を計算する

infix 4 _≤ᵇ_

_≤ᵇ_ : MyNat → MyNat → Bool
zero ≤ᵇ _ = true
succ x ≤ᵇ zero = false
succ x ≤ᵇ succ y = _≤ᵇ_ x y

-- C-c C-n 0 ≤ᵇ 1

-- C-c C-n 4 ≤ᵇ 3

-- C-c C-n 3 ≤ᵇ 12
