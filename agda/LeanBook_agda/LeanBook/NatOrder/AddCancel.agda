-- 6.1 a + b = a + c → b = c を証明する
module LeanBook.NatOrder.AddCancel where

open import Data.Product
open import Data.Sum
open import Function
open import Function.Properties.Equivalence using () renaming (trans to ⇔-trans)
open import Relation.Binary.PropositionalEquality
open import LeanBook.NatSemiring.Distrib public

-- 6.1.1 ペアノの公理再び

module _ where private
  example1 : (n : MyNat) → MyNat.succ n ≢ MyNat.zero
  example1 n ()  -- absurd pattern

  example2 : (m n : MyNat) → (succ m ≡ succ n) → m ≡ n
  example2 m n refl = refl

  example3 : (m n : MyNat) → (m + 1 ≡ n + 1) → m ≡ n
  example3 m n refl = refl

-- 6.1.2 足し算のキャンセル可能性の証明

succ-cancel : {x y : MyNat} → succ x ≡ succ y → x ≡ y
succ-cancel {x} {y} refl = refl

add-right-cancel : (l m n : MyNat) → (l + m ≡ n + m) → l ≡ n
add-right-cancel l zero n h = h
add-right-cancel l (succ m) n h = add-right-cancel l m n (succ-cancel h)

add-left-cancel : (l m n : MyNat) → (l + m ≡ l + n) → m ≡ n
add-left-cancel l m n h = add-right-cancel m l n lem
  where
    open ≡-Reasoning

    lem : m + l ≡ n + l
    lem = begin
      m + l ≡⟨ add-comm m l ⟩
      l + m ≡⟨ h ⟩
      l + n ≡⟨ add-comm l n ⟩
      n + l
      ∎

-- 6.1.3 simp タクティクで利用できるようにする

add-right-cancel-iff : (l m n : MyNat) → (l + m ≡ n + m) ⇔ l ≡ n
add-right-cancel-iff l m n = mk⇔ (add-right-cancel l m n) (cong (λ x → x + m))

add-left-cancel-iff : (l m n : MyNat) → (l + m ≡ l + n) ⇔ m ≡ n
add-left-cancel-iff l m n = mk⇔ (add-left-cancel l m n) (cong (λ x → l + x))

add-right-eq-self : (m n : MyNat) → m + n ≡ m ⇔ n ≡ 0
add-right-eq-self m n = add-left-cancel-iff m n 0

add-left-eq-self : (m n : MyNat) → n + m ≡ m ⇔ n ≡ 0
add-left-eq-self m n = subst (λ x → x ≡ m ⇔ n ≡ 0) (add-comm m n) (add-right-eq-self m n)

self-eq-add-right : (m n : MyNat) → m ≡ m + n ⇔ n ≡ 0
self-eq-add-right m n = ⇔-trans lem (add-left-eq-self m n)
  where
    lem : m ≡ m + n ⇔ n + m ≡ m
    lem = mk⇔ (λ x → trans (add-comm n m) (sym x)) (λ x → trans (sym x) (add-comm n m))

-- 6.1.4 応用： a * b = 0 ↔ a = 0 ∨ b = 0

eq-zero-of-add-eq-zero : (m n : MyNat) → m + n ≡ 0 → m ≡ 0 × n ≡ 0
eq-zero-of-add-eq-zero m zero refl = (refl , refl)
eq-zero-of-add-eq-zero m (succ n) ()

add-eq-zero-of-eq-zero : (m n : MyNat) → m ≡ 0 × n ≡ 0 → m + n ≡ 0
add-eq-zero-of-eq-zero m n (refl , refl) = refl

add-eq-zero-iff-eq-zero : (m n : MyNat) → (m + n ≡ 0) ⇔ ((m ≡ 0) × (n ≡ 0))
add-eq-zero-iff-eq-zero m n = mk⇔ (eq-zero-of-add-eq-zero m n) (add-eq-zero-of-eq-zero m n)

mul-eq-zero : (m n : MyNat) → (m * n ≡ 0) ⇔ (m ≡ 0 ⊎ n ≡ 0)
mul-eq-zero m n = mk⇔ (to m n) from
  where
    to : (m n : MyNat) → (m * n ≡ 0) → (m ≡ 0 ⊎ n ≡ 0)
    to m zero refl = inj₂ refl
    to m (succ n) h = inj₁ (proj₂ (eq-zero-of-add-eq-zero (m * n) m h))

    from : (m ≡ 0 ⊎ n ≡ 0) → (m * n ≡ 0)
    from (inj₁ refl) = zero-mul n
    from (inj₂ refl) = mul-zero m

-- 6.1.5 練習問題（回答は203 ページ）

module _ where private
  example : (n m : MyNat) → n + (1 + m) ≡ n + 2 → m ≡ 1
  example n m h = add-left-cancel 1 m 1 lem
    where
      lem : 1 + m ≡ 1 + 1
      lem = add-left-cancel n (1 + m) 2 h
