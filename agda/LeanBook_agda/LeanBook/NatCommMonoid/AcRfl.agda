-- 4.4 足し算の交換法則と結合法則を解放する
module LeanBook.NatCommMonoid.AcRfl where

open import Data.Product
open import Level
open import Relation.Binary.PropositionalEquality

open import LeanBook.NatCommMonoid.Simp public

add-comm : (m n : MyNat) → m + n ≡ n + m
add-comm m zero = sym (zero-add m)
add-comm m (succ n) = begin
  m + succ n   ≡⟨ add-succ m n ⟩
  succ (m + n) ≡⟨ cong succ (add-comm m n) ⟩
  succ (n + m) ≡⟨ sym (succ-add n m) ⟩
  succ n + m
  ∎
  where open ≡-Reasoning

add-assoc : (l m n : MyNat) → (l + m) + n ≡ l + (m + n)
add-assoc l m zero = refl
add-assoc l m (succ n) = begin
  (l + m) + succ n   ≡⟨ add-succ (l + m) n ⟩
  succ ((l + m) + n) ≡⟨ cong succ (add-assoc l m n) ⟩
  succ (l + (m + n)) ≡⟨ sym (add-succ l (m + n)) ⟩
  l + succ (m + n)   ≡⟨ cong (λ x → l + x) (sym (add-succ m n)) ⟩
  l + (m + succ n)
  ∎
  where open ≡-Reasoning

module _ where private
  example1 : (l m n : MyNat) → l + m + n + 3 ≡ m + (l + n) + 3
  example1 l m n = begin
    l + m + n + 3    ≡⟨ cong (λ x → x + n + 3) (add-comm l m) ⟩
    m + l + n + 3    ≡⟨ cong (λ x → x + 3) (add-assoc m l n) ⟩
    m + (l + n) + 3
    ∎
    where open ≡-Reasoning

open import Algebra.Bundles
open import Algebra.Structures {A = MyNat} _≡_
open import Algebra.Definitions {A = MyNat} _≡_

+-identity : Identity 0 _+_
+-identity = (zero-add , add-zero)

+-isMagma : IsMagma _+_
+-isMagma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

+-isSemigroup : IsSemigroup _+_
+-isSemigroup = record
  { isMagma = +-isMagma
  ; assoc   = add-assoc
  }

+-0-isMonoid : IsMonoid _+_ 0
+-0-isMonoid = record
  { isSemigroup = +-isSemigroup
  ; identity    = +-identity
  }

+-0-isCommutativeMonoid : IsCommutativeMonoid _+_ 0
+-0-isCommutativeMonoid = record
  { isMonoid = +-0-isMonoid
  ; comm     = add-comm
  }

+-0-commutativeMonoid : CommutativeMonoid 0ℓ 0ℓ
+-0-commutativeMonoid = record
  { Carrier = MyNat
  ; _≈_ = _≡_
  ; _∙_ = _+_
  ; ε = 0
  ; isCommutativeMonoid = +-0-isCommutativeMonoid
  }

module _ where private
  import Data.Fin.Base as Fin
  import Data.Fin.Literals as Fin
  open import Data.Vec.Base using ([]; _∷_)
  open import Algebra.Solver.CommutativeMonoid +-0-commutativeMonoid

  instance
    fin-number : ∀ {n} → Number (Fin.Fin n)
    fin-number {n} = Fin.number n

  example1 : (l m n : MyNat) → l + m + n + 3 ≡ m + (l + n) + 3
  example1 l m n =
    prove 4 (((x ⊕ y) ⊕ z) ⊕ w) ((y ⊕ (x ⊕ z)) ⊕ w) (l ∷ m ∷ n ∷ 3 ∷ [])
    where
      x = var 0
      y = var 1
      z = var 2
      w = var 3

  example2 : (l m n : MyNat) → l + (1 + m) + n ≡ m + (l + n) + 1
  example2 l m n =
    prove 4 ((x ⊕ (w ⊕ y)) ⊕ z) ((y ⊕ (x ⊕ z)) ⊕ w) (l ∷ m ∷ n ∷ 1 ∷ [])
    where
      x = var 0
      y = var 1
      z = var 2
      w = var 3
