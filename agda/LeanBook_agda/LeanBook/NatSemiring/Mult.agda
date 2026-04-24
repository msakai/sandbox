-- 5.1 掛け算を定義して交換法則、結合法則、分配法則を示す
module LeanBook.NatSemiring.Mult where

open import Relation.Binary.PropositionalEquality
import Data.Fin.Base as Fin
import Data.Fin.Literals as Fin
open import Level using (0ℓ)
open import Data.Product
open import Data.Vec.Base using ([]; _∷_)

open import LeanBook.NatCommMonoid.BetterInduction

open ≡-Reasoning

instance
  fin-number : ∀ {n} → Number (Fin.Fin n)
  fin-number {n} = Fin.number n

mul : MyNat → MyNat → MyNat
mul m zero = zero
mul m (succ n) = mul m n + m

_*_ : MyNat → MyNat → MyNat
_*_ = mul

infixl 7 _*_

-- C-c C-n 2 * 3

-- C-c C-n 3 * 5

mul-add-one : (m n : MyNat) → m * (n + 1) ≡ m * n + m
mul-add-one m n = refl

add-one-mul : (m n : MyNat) → (m + 1) * n ≡ m * n + n
add-one-mul m zero = refl
add-one-mul m (succ n) = begin
  (m + 1) * (n + 1)      ≡⟨ mul-add-one (m + 1) n ⟩
  (m + 1) * n + (m + 1)  ≡⟨ cong (λ x → x + (m + 1)) (add-one-mul m n) ⟩
  m * n + n + (m + 1)    ≡⟨ add-assoc (m * n) n (m + 1) ⟩
  m * n + (n + (m + 1))  ≡⟨ cong (λ x -> m * n + succ x) (add-comm n m) ⟩
  m * n + (m + (n + 1))  ≡⟨ sym (add-assoc (m * n) m (n + 1)) ⟩
  m * n + m + (n + 1)    ≡⟨ cong (λ x → x + (n + 1)) (sym (mul-add-one m n)) ⟩
  m * (n + 1) + (n + 1)
  ∎

mul-zero : (m : MyNat) → m * 0 ≡ 0
mul-zero m = refl

zero-mul : (n : MyNat) → 0 * n ≡ 0
zero-mul zero = refl
zero-mul (succ n) = begin
  zero * succ n    ≡⟨ mul-add-one zero n ⟩
  zero * n + zero  ≡⟨ cong (λ x → x + zero) (zero-mul n) ⟩
  zero
  ∎

mul-one : (n : MyNat) → n * 1 ≡ n
mul-one n = begin
  n * 1      ≡⟨ mul-add-one n zero ⟩
  n * 0 + n  ≡⟨ cong (λ x → x + n) (mul-zero n) ⟩
  0 + n      ≡⟨ zero-add n ⟩
  n
  ∎

one-mul : (n : MyNat) → 1 * n ≡ n
one-mul n = begin
  1 * n      ≡⟨ add-one-mul zero n ⟩
  0 * n + n  ≡⟨ cong (λ x → x + n) (zero-mul n) ⟩
  0 + n      ≡⟨ zero-add n ⟩
  n
  ∎

mul-comm : (m n : MyNat) → m * n ≡ n * m
mul-comm m zero = trans (mul-zero m) (sym (zero-mul m))
mul-comm m (succ n) = begin
  m * succ n  ≡⟨ mul-add-one m n ⟩
  m * n + m   ≡⟨ cong (λ x → x + m) (mul-comm m n) ⟩
  n * m + m   ≡⟨ sym (add-one-mul n m) ⟩
  succ n * m
  ∎

add-mul : (l m n : MyNat) → (l + m) * n ≡ l * n + m * n
add-mul l m zero = refl
add-mul l m (succ n) = begin
  (l + m) * succ n           ≡⟨ refl ⟩
  (l + m) * n + (l + m)      ≡⟨ cong (λ x → x + (l + m)) (add-mul l m n) ⟩
  (l * n + m * n) + (l + m)  ≡⟨ prove 4 ((x ⊕ y) ⊕ (z ⊕ w)) ((x ⊕ z) ⊕ (y ⊕ w)) (l * n ∷ m * n ∷ l ∷ m ∷ []) ⟩
  (l * n + l) + (m * n + m)  ≡⟨ refl ⟩
  l * succ n + m * succ n
  ∎
  where
    open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid
    x = var 0
    y = var 1
    z = var 2
    w = var 3

mul-add : (l m n : MyNat) → l * (m + n) ≡ l * m + l * n
mul-add l m n = begin
  l * (m + n)    ≡⟨ mul-comm l (m + n) ⟩
  (m + n) * l    ≡⟨ add-mul m n l ⟩
  m * l + n * l  ≡⟨ cong₂ _+_ (mul-comm m l) (mul-comm n l) ⟩
  l * m + l * n
  ∎

mul-assoc : (l m n : MyNat) → (l * m) * n ≡ l * (m * n)
mul-assoc l m zero = refl
mul-assoc l m (succ n) = begin
  (l * m) * (n + 1)          ≡⟨ mul-add (l * m) n 1 ⟩
  (l * m) * n + (l * m) * 1  ≡⟨ cong (λ x → l * m * n + x) (mul-one (l * m)) ⟩
  (l * m) * n + (l * m)      ≡⟨ cong (λ x → x + l * m) (mul-assoc l m n) ⟩
  l * (m * n) + (l * m)      ≡⟨ sym (mul-add l (m * n) m) ⟩
  l * (m * n + m)            ≡⟨ refl ⟩
  l * (m * (n + 1))
  ∎

open import Algebra.Bundles
open import Algebra.Structures {A = MyNat} _≡_
open import Algebra.Definitions {A = MyNat} _≡_

*-identity : Identity 1 _*_
*-identity = (one-mul , mul-one)

*-isMagma : IsMagma _*_
*-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _*_
  }

*-isSemigroup : IsSemigroup _*_
*-isSemigroup = record
  { isMagma = *-isMagma
  ; assoc   = mul-assoc
  }

*-1-isMonoid : IsMonoid _*_ 1
*-1-isMonoid = record
  { isSemigroup = *-isSemigroup
  ; identity    = *-identity
  }

*-1-isCommutativeMonoid : IsCommutativeMonoid _*_ 1
*-1-isCommutativeMonoid = record
  { isMonoid = *-1-isMonoid
  ; comm     = mul-comm
  }

*-1-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
*-1-commutativeMonoid = record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _∙_ = _*_
  ; ε = 1
  ; isCommutativeMonoid = *-1-isCommutativeMonoid
  }

module _ where private
  example1 : (m n : MyNat) → m * n * n * m ≡ m * m * n * n
  example1 m n = prove 2 (((x ⊕ y) ⊕ y) ⊕ x) (((x ⊕ x) ⊕ y) ⊕ y) (m ∷ n ∷ [])
    where
      open import Algebra.Solver.CommutativeMonoid *-1-commutativeMonoid
      x = var 0
      y = var 1

  example2 : (m n : MyNat) → (m + n) * (m + n) ≡ m * m + 2 * m * n + n * n
  example2 m n = begin
    (m + n) * (m + n)                  ≡⟨ mul-add (m + n) m n ⟩
    (m + n) * m + (m + n) * n          ≡⟨ cong₂ _+_ (add-mul m n m) (add-mul m n n) ⟩
    (m * m + n * m) + (m * n + n * n)  ≡⟨ cong (λ x → (m * m + x) + (m * n + n * n)) (mul-comm n m)  ⟩
    (m * m + m * n) + (m * n + n * n)  ≡⟨ prove 3 ((mm ⊕ mn) ⊕ (mn ⊕ nn)) ((mm ⊕ (mn ⊕ mn)) ⊕ nn) (m * m ∷ m * n ∷ n * n ∷ []) ⟩
    m * m + (m * n + m * n) + n * n    ≡⟨ cong (λ x → m * m + x + n * n) (sym lemma) ⟩
    m * m + 2 * m * n + n * n
    ∎
    where
      open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

      mm = var 0
      mn = var 1
      nn = var 2

      lemma : 2 * m * n ≡ m * n + m * n
      lemma = begin
        2 * m * n                    ≡⟨ mul-assoc 2 m n ⟩
        2 * (m * n)                  ≡⟨ add-mul 1 1 (m * n) ⟩
        (1 * (m * n) + 1 * (m * n))  ≡⟨ cong₂ _+_ (one-mul (m * n)) (one-mul (m * n)) ⟩
        (m * n + m * n)
        ∎
