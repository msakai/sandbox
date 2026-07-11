-- 第7章 同値関係で割って整数を作る
module LeanBook.Int.Setoid where

open import Agda.Builtin.FromNat public
open import Agda.Builtin.FromNeg public
open import Data.Unit.Base using (⊤; tt)
open import Data.Integer
import Data.Integer.Literals as Int
open import Level using (0ℓ)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

-- 7.1 同値関係

-- 7.1.1 Lean の構造体

record Point : Set where
  field
    x : ℤ
    y : ℤ

instance
  int-number = Int.number
  int-negative = Int.negative

-- C-c C-d record { x = 1; y = 2 }

-- C-c C-d Point.x

-- C-c C-d Point.y

-- C-c C-n let p = record { x = 1; y = 2 } in Point.x p

-- 7.1.2 Equivalence

module _ where private
  example : (α : Set) → (_≈_ : Rel α 0ℓ) → IsEquivalence _≈_ → ∀ x → x ≈ x
  example α _≈_ h x = IsEquivalence.refl h

module _ where private
  example : (a : Set) → IsEquivalence (λ (x y : a) → x ≡ y)
  example a = record
    { refl = refl
    ; sym = sym
    ; trans = trans
    }

-- 7.1.3 Setoid

-- 7.1.4 練習問題（回答は205 ページ）

module _ where private
  example : (α : Set) → IsEquivalence (λ (x y : α) → ⊤)
  example α = record
    { refl = tt
    ; sym = λ x≈y → tt
    ; trans = λ x≈y y≈z → tt
    }
