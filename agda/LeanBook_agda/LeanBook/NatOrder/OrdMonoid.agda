-- 6.5 足し算が順序を保つことを示す
module LeanBook.NatOrder.OrdMonoid where

open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import LeanBook.NatOrder.NotationSimp public

import Relation.Binary.Reasoning.Preorder (≤-preorder) as ≤-Reasoning

-- 6.5.1 足し算は順序を保つ

private variable
  a b m n : MyNat

add-le-add-left : (n ≤ m) → (l : MyNat) → l + n ≤ l + m
add-le-add-left {n = n} {m = m} h l with ≤-dest h
... | (k , h) = ≤-intro {k = k} $ begin
  l + n + k   ≡⟨ add-assoc l n k ⟩
  l + (n + k) ≡⟨ cong (λ x → l + x) h ⟩
  l + m
  ∎
  where open ≡-Reasoning

add-le-add-right : (m ≤ n) → (l : MyNat) → m + l ≤ n + l
add-le-add-right {m = m} {n = n} h l = begin
  m + l ≈⟨ add-comm m l ⟩
  l + m ≲⟨ add-le-add-left h l ⟩
  l + n ≈⟨ add-comm l n ⟩
  n + l
  ∎
  where open ≤-Reasoning

add-le-add : m ≤ n → a ≤ b → m + a ≤ n + b
add-le-add {m = m} {n = n} {a = a} {b = b} h1 h2 = begin
  m + a ≲⟨ add-le-add-left h2 m ⟩
  m + b ≲⟨ add-le-add-right h1 b ⟩
  n + b
  ∎
  where open ≤-Reasoning

-- 6.5.2 足し算が順序を保つことを再利用可能にする

-- 6.5.3 足し算は狭義順序を保つ

add-lt-add-left : {m n : MyNat} → (m < n) → (k : MyNat) → k + m < k + n
add-lt-add-left {m} {n} h k = subst (λ x → x ≤ k + n) lem1 lem2
  where
    lem1 : k + (m + 1) ≡ (k + m) + 1
    lem1 = sym (add-assoc k m 1)

    lem2 : k + (m + 1) ≤ k + n
    lem2 = add-le-add-left h k

-- 6.5.4 順序についても足し算はキャンセル可能

private variable
  k : MyNat

le-of-add-le-add-left : k + m ≤ k + n → m ≤ n
le-of-add-le-add-left {k = k} {m = m} {n = n} h with ≤-dest h
... | (d , h2) = ≤-intro lem
  where
    open ≡-Reasoning

    lem : m + d ≡ n
    lem = add-left-cancel k (m + d) n $ begin
      k + (m + d) ≡⟨ sym (add-assoc k m d) ⟩
      (k + m) + d ≡⟨ h2 ⟩
      k + n
      ∎

le-of-add-le-add-right : m + k ≤ n + k → m ≤ n
le-of-add-le-add-right {m = m} {k = k} {n = n} h = le-of-add-le-add-left lem
  where
    open ≤-Reasoning

    lem : k + m ≤ k + n
    lem = begin
      k + m ≈⟨ add-comm k m ⟩
      m + k ≲⟨ h ⟩
      n + k ≈⟨ add-comm n k ⟩
      k + n
      ∎

le-of-add-le-iff-left : k + m ≤ k + n ⇔ m ≤ n
le-of-add-le-iff-left {k = k} = mk⇔ le-of-add-le-add-left (λ h → add-le-add-left h k)

le-of-add-le-iff-right : m + k ≤ n + k ⇔ m ≤ n
le-of-add-le-iff-right {k = k} = mk⇔ le-of-add-le-add-right (λ h → add-le-add-right h k)

-- 6.5.5 練習問題 （回答は204ページ）

module _ where private
  example : (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat) → m₁ ≤ m₂ → n₁ ≤ n₂ → l₁ ≤ l₂ → l₁ + m₁ + n₁ ≤ l₂ + n₂ + m₂
  example m₁ m₂ n₁ n₂ l₁ l₂ h1 h2 h3 = begin
    l₁ + m₁ + n₁ ≲⟨ add-le-add-left h2 (l₁ + m₁) ⟩
    l₁ + m₁ + n₂ ≲⟨ add-le-add-right (add-le-add-left h1 l₁) n₂ ⟩
    l₁ + m₂ + n₂ ≲⟨ add-le-add-right (add-le-add-right h3 m₂) n₂ ⟩
    l₂ + m₂ + n₂ ≈⟨ add-assoc l₂ m₂ n₂ ⟩
    l₂ + (m₂ + n₂) ≈⟨ cong (λ x → l₂ + x) (add-comm m₂ n₂) ⟩
    l₂ + (n₂ + m₂) ≈⟨ sym (add-assoc l₂ n₂ m₂) ⟩
    l₂ + n₂ + m₂
    ∎
    where
      open ≤-Reasoning
