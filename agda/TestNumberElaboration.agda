-- Tested with Agda-2.8.0 (optimise-heavily) and agda-stdlib-2.3
module TestNumberElaboration where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties using (+-*-commutativeSemiring)
open import Data.Unit
open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-commutativeSemiring

example : (a : ℕ) → a ≡ a
example = solve 1 (λ a → a := a) refl

open import Agda.Builtin.FromNat
import Data.Nat.Literals

instance
  number : Number ℕ
  number = Data.Nat.Literals.number

-- We can refine the ng-* goals below, but they fail to type-check after reloading Agda.

-- Same source as `example` above, but fromNat and Number ℕ are now in scope:
ng-1 : (a : ℕ) → a ≡ a
ng-1 = solve 1 (λ a → a := a) {!refl!}

ok-1 : (a : ℕ) → a ≡ a
ok-1 = solve (suc zero) (λ a → a := a) refl

-- Same as ng-1, but the third arg uses an explicit hidden lambda:
ok-lambda : (a : ℕ) → a ≡ a
ok-lambda = solve 1 (λ a → a := a) λ {_} → refl

ng-2 : (a : ℕ) → a ≡ a
ng-2 = solve (fromNat (suc zero)) (λ a → a := a) {!refl!}

ok-2 : (a : ℕ) → a ≡ a
ok-2 = solve (fromNat {{number}} (suc zero)) (λ a → a := a) refl
