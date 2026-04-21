module TestFromNat where

open import Data.Unit
import Data.Fin as Fin
import Data.Fin.Literals as Fin
import Data.Nat as Nat
import Data.Nat.Literals as Nat
open import Agda.Builtin.FromNat

data MyNat : Set where
  zero : MyNat
  succ : MyNat → MyNat

fromNat' : Nat.ℕ → MyNat
fromNat' Nat.zero = zero
fromNat' (Nat.suc n) = succ (fromNat' n)

instance
  my-nat-number : Number MyNat
  my-nat-number = record
    { Constraint = λ _ → ⊤
    ; fromNat    = λ n → fromNat' n
    }

  nat-number = Nat.number

  fin-number : ∀ {n} → Number (Fin.Fin n)
  fin-number {n} = Fin.number n

test-MyNat : MyNat
test-MyNat = 2

test-ℕ : Nat.ℕ
test-ℕ = 2

test-Fin : Fin.Fin 1
test-Fin = 0
