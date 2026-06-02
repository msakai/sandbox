-- 6.2 順序を定義する
{-# OPTIONS --allow-unsolved-metas #-}
module LeanBook.NatOrder.OrderDef where

open import Function
open import Data.Product
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality.Properties
open import Relation.Binary using (_⇒_)
open import Relation.Binary.Bundles
open import Relation.Nullary

open import LeanBook.NatOrder.AddCancel public

-- 6.2.1 順序関係を帰納的に定義する

infix 4 _≤_ _≰_ _≥_ _≱_

data _≤_ (n : MyNat) : MyNat → Set where
  ≤-refl : n ≤ n
  ≤-step : {m : MyNat} → n ≤ m → n ≤ (m + 1)

_≥_ : MyNat → MyNat → Set
a ≥ b = b ≤ a

_≰_ : MyNat → MyNat → Set
a ≰ b = ¬ a ≤ b

_≱_ : MyNat → MyNat → Set
a ≱ b = b ≰ a

-- 6.2.2 帰納型では帰納法が使える

module _ where private
  example : (m n : MyNat) → (P : MyNat → MyNat → Set) → (h : m ≤ n) → P m n
  example m n P ≤-refl = {!!}
  example m .(n + 1) P (≤-step {n} h) = {!!}
    where
      ih : P m n
      ih = example m n P h

≤-rec : {n b : MyNat} {motive : (a : MyNat) → n ≤ a → Set}
  (refl : motive n ≤-refl)
  (step : ∀ {m : MyNat} (a : n ≤ m) → motive m a → motive (m + 1) (≤-step a))
  (t : n ≤ b) → motive b t
≤-rec refl step ≤-refl = refl
≤-rec refl step (≤-step h) = step h (≤-rec refl step h)

-- 6.2.3 反射律と推移律を示す

≤-reflexive : _≡_ ⇒ _≤_
≤-reflexive {m} {.m} Eq.refl = ≤-refl

≤-trans : {m n k : MyNat} → m ≤ n → n ≤ k → m ≤ k
≤-trans m≤n ≤-refl = m≤n
≤-trans m≤n (≤-step {k} n≤k) = ≤-step (≤-trans m≤n n≤k)

≤-add-one-right : (n : MyNat) → n ≤ n + 1
≤-add-one-right n = ≤-step ≤-refl

≤-add-one-left : (n : MyNat) → n ≤ 1 + n
≤-add-one-left n = Eq.subst (λ x → n ≤ x) (add-comm n 1) (≤-add-one-right n)

open import Relation.Binary.Structures {A = MyNat} _≡_

≤-isPreorder : IsPreorder _≤_
≤-isPreorder = record
  { isEquivalence = Relation.Binary.PropositionalEquality.Properties.isEquivalence
  ; reflexive = ≤-reflexive
  ; trans = ≤-trans
  }

≤-preorder : Preorder 0ℓ 0ℓ 0ℓ
≤-preorder = record
  { isPreorder = ≤-isPreorder
  }

-- 6.2.4 順序関係を和の等式に書き換える

≤-dest : {m n : MyNat} → m ≤ n → ∃[ k ] m + k ≡ n
≤-dest ≤-refl = (0 , Eq.refl)
≤-dest (≤-step m≤n) with ≤-dest m≤n
... | (k , m+k≡n) = (k + 1 , Eq.cong succ m+k≡n)

≤-add-right : (m n : MyNat) → m ≤ m + n
≤-add-right m zero = ≤-refl
≤-add-right m (succ n) = ≤-step (≤-add-right m n)

≤-intro : {m n k : MyNat} → m + k ≡ n → m ≤ n
≤-intro {m} {n} {k} h = Eq.subst (λ x → m ≤ x) h (≤-add-right m k)

≤-iff-add : {m n : MyNat} → m ≤ n ⇔ (∃[ k ] m + k ≡ n)
≤-iff-add = mk⇔ ≤-dest (λ (k , m+k≡n) → ≤-intro m+k≡n)

-- 6.2.5 練習問題（回答は203 ページ）

module _ where private
  example : 1 ≤ 4
  example = ≤-add-right 1 3
