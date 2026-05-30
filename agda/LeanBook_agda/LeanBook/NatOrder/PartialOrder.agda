-- 6.6 a ≤ b → b ≤ a → a = b を示す
module LeanBook.NatOrder.PartialOrder where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Level using (0ℓ)
open import Relation.Binary using (IsPartialOrder; Poset)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation
open import LeanBook.NatOrder.OrdMonoid

import Relation.Binary.Reasoning.Preorder (≤-preorder) as ≤-Reasoning

-- 6.6.1 狭義順序と広義順序の推移律

private variable
  n m k : MyNat

<-trans : n < m → m < k → n < k
<-trans {n = n} {m = m} {k = k} h₁ h₂ = begin
  n + 1 ≲⟨ h₁ ⟩
  m     ≲⟨ ≤-add-one-right m ⟩
  m + 1 ≲⟨ h₂ ⟩
  k
  ∎
  where open ≤-Reasoning

≤-<-trans : n ≤ m → m < k → n < k
≤-<-trans {n = n} {m = m} {k = k} h₁ h₂ = begin
  n + 1 ≲⟨ add-le-add-right h₁ 1 ⟩
  m + 1 ≲⟨ h₂ ⟩
  k
  ∎
  where open ≤-Reasoning

<-≤-trans : n < m → m ≤ k → n < k
<-≤-trans {n = n} {m = m} {k = k} h₁ h₂ = begin
  n + 1 ≲⟨ h₁ ⟩
  m ≲⟨ h₂ ⟩
  k
  ∎
  where open ≤-Reasoning

-- 6.6.2 狭義順序の非反射律
<-irrefl : (n : MyNat) → ¬ n < n
<-irrefl n n<n with ≤-dest n<n
... | (k , n+1+k≡n) with add-left-cancel n (succ k) zero lem
  where
    lem : n + succ k ≡ n
    lem = begin
      n + succ k   ≡⟨ refl ⟩
      n + k + 1    ≡⟨ add-assoc n k 1 ⟩
      n + (k + 1)  ≡⟨ cong (λ x → n + x) (add-comm k 1) ⟩
      n + (1 + k)  ≡⟨ sym (add-assoc n 1 k) ⟩
      n + 1 + k    ≡⟨ n+1+k≡n ⟩
      n
      ∎
      where open ≡-Reasoning
... | ()

-- 6.6.3 反対称律

≤-antisym : n ≤ m →  m ≤ n → n ≡ m
≤-antisym ≤-refl h₂ = refl
≤-antisym {n = n} {m = .succ m₁} (≤-step {m₁} n≤m₁) h₂ with not-le-of-lt lem ≤-refl
  where
    lem : n < n
    lem = begin
      n + 1   ≲⟨ add-le-add-right n≤m₁ 1 ⟩
      m₁ + 1  ≲⟨ h₂ ⟩
      n
      ∎
      where open ≤-Reasoning
... | ()

≤-isPartialOrder : IsPartialOrder _≡_ _≤_
≤-isPartialOrder = record
  { isPreorder = ≤-isPreorder
  ; antisym    = ≤-antisym
  }

≤-poset : Poset 0ℓ 0ℓ 0ℓ
≤-poset = record
  { isPartialOrder = ≤-isPartialOrder
  }

-- 6.6.4 練習問題 （回答は204 ページ）

module _ where private
  example : (a b : MyNat) → (a < b ⊎ a ≡ b) → a ≤ b
  example a b (inj₁ a<b) = ≤-trans (≤-step ≤-refl) a<b
  example a b (inj₂ refl) = ≤-refl
