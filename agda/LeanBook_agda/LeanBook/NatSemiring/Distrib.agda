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
  { isSemiringWithoutAnnihilatingZero =   record
    { +-isCommutativeMonoid = +-0-isCommutativeMonoid
    ; *-cong = cong₂ _*_
    ; *-assoc = mul-assoc
    ; *-identity = (one-mul , mul-one)
    ; distrib = (mul-add , (λ x y z → add-mul y z x))
    }
  ; zero = (zero-mul , mul-zero)
  }

+-*-isCommutativeSemiring : IsCommutativeSemiring _+_ _*_ 0 1
+-*-isCommutativeSemiring =
  record
  { isSemiring = +-*-isSemiring
  ; *-comm = mul-comm
  }

+-*-semiring : Semiring 0ℓ 0ℓ
+-*-semiring =
  record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  ; isSemiring = +-*-isSemiring
  }

+-*-commutativeSemiring : CommutativeSemiring 0ℓ 0ℓ
+-*-commutativeSemiring =
  record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; 0# = 0
  ; 1# = 1
  ; isCommutativeSemiring = +-*-isCommutativeSemiring
  }

-- 5.2.1 ステップ1：rw ではなくsimp を使う

-- 5.2.2 ステップ2：マクロでタクティクを作る

module _ where private
  open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-commutativeSemiring
  open ≡-Reasoning
  import Data.Nat as Nat

  -- Some values of ℕ are written using suc and zero below.
  -- This is because of https://github.com/agda/agda/issues/8540

  -- 5.2.3 ステップ3：マクロ内で複数タクティクを実行する
  example1 : (m n : MyNat) → m * (n + 1) + (2 + n) * n ≡ m * n + m + 2 * n + n * n
  example1 = solve (Nat.suc (Nat.suc Nat.zero))
    (λ m n → m :* (n :+ con 1) :+ (con 2 :+ n) :* n := m :* n :+ m :+ con 2 :* n :+ n :* n) refl

  -- 5.2.4 ステップ4：n + n = 2 * n といったルールを扱わせる
  example2 : (m n : MyNat) → m * (n + 1) + (2 + m) * m ≡ m * n + 3 * m + m * m
  example2  = solve (Nat.suc (Nat.suc Nat.zero))
    (λ m n → m :* (n :+ con 1) :+ (con 2 :+ m) :* m := m :* n :+ con 3 :* m :+ m :* m) refl

  -- 5.2.5 ステップ5：大きな数にも対応できるようにする
  example3 : (m n : MyNat) → (m + 4) * n + n ≡ m * n + 5 * n
  example3 = solve (Nat.suc (Nat.suc Nat.zero))
    (λ m n → (m :+ con 4) :* n :+ n := m :* n :+ con 5 :* n) refl

  -- 5.2.6 ステップ6：try を使う
  example4 : (m n : MyNat) → m * n + n * n ≡ (m + n) * n
  example4 = solve (Nat.suc (Nat.suc Nat.zero))
           (λ m n → m :* n :+ n :* n := (m :+ n) :* n) refl

  -- 5.2.7 練習問題 （回答は203 ページ）
  example5 : (n : MyNat) → ∃[ s ] ∃[ t ] s * t ≡ n * n + 8 * n + 16
  example5 n =
    ( n + 4
    , n + 4
    , solve (Nat.suc (Nat.zero))
        (λ n → (n :+ con 4) :* (n :+ con 4) := n :* n :+ con 8 :* n :+ con 16) refl n
    )
