-- 第5章 分配法則を証明し、マクロで再利用可能にする
module LeanBook.NatSemiring.Distrib where

open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open import LeanBook.NatSemiring.Mult

open import Algebra.Bundles
open import Algebra.Structures {A = MyNat} _≡_
open import Algebra.Definitions {A = MyNat} _≡_

+-*-isSemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _+_ _*_ 0 1
+-*-isSemiringWithoutAnnihilatingZero =
  record
  { +-isCommutativeMonoid = +-0-isCommutativeMonoid
  ; *-cong = cong₂ _*_
  ; *-assoc = mul-assoc
  ; *-identity = (one-mul , mul-one)
  ; distrib = (mul-add , (λ x y z → add-mul y z x))
  }

+-*-isSemiring : IsSemiring _+_ _*_ 0 1
+-*-isSemiring =
  record
  { isSemiringWithoutAnnihilatingZero = +-*-isSemiringWithoutAnnihilatingZero
  ; zero = (zero-mul , mul-zero)
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0 1
+-*-isCommutativeSemiring =
  record
  { isSemiring = +-*-isSemiring
  ; *-comm = mul-comm
  }

+-*-SemiringWithoutAnnihilatingZero : SemiringWithoutAnnihilatingZero 0ℓ 0ℓ
+-*-SemiringWithoutAnnihilatingZero =
  record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  ; isSemiringWithoutAnnihilatingZero = +-*-isSemiringWithoutAnnihilatingZero
  }

+-*-Semiring : Semiring 0ℓ 0ℓ
+-*-Semiring =
  record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  ; isSemiring = +-*-isSemiring
  }

+-*-CommutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-CommutativeSemiring =
  record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  ; isCommutativeSemiring = +-*-isCommutativeSemiring
  }

module _ where private
  open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-CommutativeSemiring

  example : (a : MyNat) → a ≡ a
  example = solve 1 (λ a → a := a) {!refl!}
{-
We can refine the above goal, but it fails to type check after reloading Agda.

Environment
- Agda-2.8.0 (optimise-heavily)
- agda-stdlib-2.3
-}
