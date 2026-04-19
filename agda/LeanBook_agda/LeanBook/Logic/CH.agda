-- 3.6 カリー・ハワード同型対応
module LeanBook.Logic.CH where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

one_add_one_eq_two : 1 + 1 ≡ 2
one_add_one_eq_two = refl

example : (P Q : Set) → (P → Q) → P → Q
example P Q h hp = h hp

idOnNat : ℕ → ℕ
idOnNat n = n

-- C-c C-n idOnNat 42
