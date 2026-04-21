module LeanBook.NatCommMonoid.TypeClass where

open import Data.Unit
import Data.Nat as Nat
open import Relation.Binary.PropositionalEquality

open import LeanBook.FirstProof.NaturalNumber public

fromNat : Nat.ℕ → MyNat
fromNat Nat.zero = zero
fromNat (Nat.suc n) = succ (fromNat n)

{-# BUILTIN FROMNAT fromNat #-}

module _ where
  private
    example1 : MyNat
    example1 = 0
    
    example2 : MyNat
    example2 = 1

_+_ : MyNat → MyNat → MyNat
_+_ = add

infixl 6 _+_

module _ where
  private
    example1 : MyNat
    example1 = 1 + 1

    example2 : MyNat
    example2 = zero + one

    -- FIXME: "C-c C-n 1 + 1" だと、数値リテラルが MyNat ではなく Nat.ℕ に解釈されてしまう
    -- private な定義にしてると、 "C-c C-n example3" とすることも出来ない。
    example3 : MyNat
    example3 = 0 + 0

    -- ditto
    example4 : MyNat
    example4 = 1 + 2

module _ where
  private
    example1 : MyNat
    example1 = 0 + 0

    example2 : MyNat
    example2 = 1 + 1

module _ where
  private
    example : (n : MyNat) → n + 0 ≡ n
    example n = refl
