-- 3.7 依存型
module LeanBook.Logic.Dependent where

open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

add_zero : (n : ℕ) → n + 0 ≡ n
add_zero = +-identityʳ

-- C-c C-d add_zero

-- C-c C-d add_zero 0

-- C-c C-d add_zero 42

example1 : (∀ n → n + 0 ≡ n) ≡ ((n : ℕ) → n + 0 ≡ n)
example1 = refl

{-
data List (α : Set) : Set where
  [] : List α
  _∷_ : α → List α → List α
-}

example2 : List ℕ
example2 = 0 ∷ 1 ∷ 2 ∷ 3 ∷  []

example3 : List ℕ
example3 = 0 ∷ 1 ∷ []

data Vect (α : Set) : ℕ → Set where
  nil : Vect α 0
  cons : ∀ {n} → α → Vect α n → Vect α (n + 1)

example4 : Vect ℕ 0
example4 = nil

example5 : Vect ℕ 1
example5 = cons 42 nil

example6 : Σ[ α ∈ Set ] α
example6 = ( ℕ , 1 )

example7 : Σ[ α ∈ Set ] α
example7 = ( Bool , true )

example8 : Σ[ α ∈ Set1 ] α
example8 = ( Set , ⊤ )

1ℓ : Level
1ℓ = Level.suc 0ℓ

example9 : List (Σ[ α ∈ Set1 ] α)
example9 = ( Lift 1ℓ ℕ , lift 1 ) ∷ ( Lift 1ℓ Bool , lift true ) ∷ ( Set , ⊤ ) ∷ []

example10 : List (Σ[ α ∈ Set1 ] α)
example10 = ( Lift 1ℓ ℕ , lift 42 ) ∷ ( Lift 1ℓ Bool , lift false ) ∷ []

example11 : ∀ {α : Set} {n : ℕ} (a : α) → Vect α n → Vect α (n + 1)
example11 = cons
