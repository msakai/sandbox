-- 6.7 順序関係を決定可能にする
module LeanBook.NatOrder.DecidableOrd where

open import Data.Bool using (Bool; true; false; not; T)
open import Data.Product
open import Function
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Nullary.Reflects
  using (fromEquivalence; Reflects; ofʸ; ofⁿ; invert)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import LeanBook.NatOrder.PartialOrder public

module _ where private
  example1 : 0 ≤ 1
  example1 = ≤-step ≤-refl

  example2 : 0 ≤ 3
  example2 = ≤-step (≤-step (≤-step ≤-refl))

-- 6.7.1 Decidable 型クラス

-- 6.7.2 例：等号を決定可能にする

infix 4 _≟_
_≟_ : DecidableEquality MyNat
zero ≟ zero = yes refl
succ x ≟ zero = no (λ ())
zero ≟ succ y = no (λ ())
succ x ≟ succ y with x ≟ y
... | yes x≡y = yes (cong succ x≡y)
... | no x≢y = no (λ x+1≡y+1 → x≢y (succ-cancel x+1≡y+1))

module _ where private
  example : 32 + 13 ≢ 46
  example = from-no (32 + 13 ≟ 46)

-- C-c C-n 1 ≟ 2

-- 6.7.3 順序関係を計算する

infix 4 _≤ᵇ_

_≤ᵇ_ : MyNat → MyNat → Bool
zero ≤ᵇ _ = true
succ x ≤ᵇ zero = false
succ x ≤ᵇ succ y = _≤ᵇ_ x y

-- C-c C-n 0 ≤ᵇ 1

-- C-c C-n 4 ≤ᵇ 3

-- C-c C-n 3 ≤ᵇ 12

-- 6.7.4 functional induction

≤ᵇ-induct
  : (motive : MyNat → MyNat → Set)
  → (∀ b → motive zero b)
  → (∀ a → motive (succ a) zero)
  → (∀ a b → motive a b → motive (succ a) (succ b))
  → (a b : MyNat)
  → motive a b
≤ᵇ-induct motive case1 case2 case3 zero y = case1 y
≤ᵇ-induct motive case1 case2 case3 (succ x) zero = case2 x
≤ᵇ-induct motive case1 case2 case3 (succ x) (succ y) = case3 x y (≤ᵇ-induct motive case1 case2 case3 x y)

≤ᵇ-zero-left : ∀ n → T (0 ≤ᵇ n)
≤ᵇ-zero-left _ = tt

≤ᵇ-zero-right : ∀ n → T (not (succ n ≤ᵇ 0))
≤ᵇ-zero-right _ = tt

≤ᵇ-succ : ∀ m n → (succ m ≤ᵇ succ n) ≡ (m ≤ᵇ n)
≤ᵇ-succ _ _ = refl

≤ᵇ-reflects-≤ : ∀ m n → Reflects (m ≤ n) (m ≤ᵇ n)
≤ᵇ-reflects-≤ = ≤ᵇ-induct motive case1 case2 case3
  where
    motive = (λ m n → Reflects (m ≤ n) (m ≤ᵇ n))

    case1 : (n : MyNat) → Reflects (zero ≤ n) (zero ≤ᵇ n)
    case1 n = ofʸ 0≤n

    case2 : (m : MyNat) → Reflects (succ m ≤ zero) (succ m ≤ᵇ zero)
    case2 m = ofⁿ (λ ())

    lem : (m n : MyNat) → (b : Bool) → Reflects (m ≤ n) b → Reflects (succ m ≤ succ n) b
    lem m n .true (ofʸ m≤n) = ofʸ (+-monoˡ-≤ m≤n 1)
    lem m n .false (ofⁿ m≰n) = ofⁿ (λ m+1≤n+1 → m≰n (+-cancelʳ-≤ m+1≤n+1))

    case3 : (m n : MyNat) → Reflects (m ≤ n) (m ≤ᵇ n) → Reflects (succ m ≤ succ n) (succ m ≤ᵇ succ n)
    case3 m n h = lem m n (m ≤ᵇ n) h

≤ᵇ⇒≤ : ∀ m n → T (m ≤ᵇ n) → m ≤ n
≤ᵇ⇒≤ zero n h = 0≤n
≤ᵇ⇒≤ (succ m) zero ()
≤ᵇ⇒≤ (succ m) (succ n) h = +-monoˡ-≤ (≤ᵇ⇒≤ m n h) 1

≤⇒≤ᵇ : ∀ m n → m ≤ n → T (m ≤ᵇ n)
≤⇒≤ᵇ zero _ _ = tt
≤⇒≤ᵇ (succ m) zero ()
≤⇒≤ᵇ (succ m) (succ n) ≤-refl = ≤⇒≤ᵇ m m ≤-refl
≤⇒≤ᵇ (succ m) (succ n) (≤-step m+1≤n) = ≤⇒≤ᵇ m n (≤-trans (≤-add-one-right m) m+1≤n)

≤ᵇ-reflects-≤′ : ∀ m n → Reflects (m ≤ n) (m ≤ᵇ n)
≤ᵇ-reflects-≤′ m n = fromEquivalence (≤ᵇ⇒≤ m n) (≤⇒≤ᵇ m n)

-- 6.7.5 順序関係を決定可能にする

infix 4 _≤?_ _≥?_

_≤?_ : Decidable _≤_
m ≤? n = map′ (≤ᵇ⇒≤ m n) (≤⇒≤ᵇ m n) (T? (m ≤ᵇ n))

_≥?_ : Decidable _≥_
_≥?_ = flip _≤?_

-- C-c C-n 1 ≤? 3
-- ⇒ map′ (λ h → ≤-step (≤-step ≤-refl)) (≤⇒≤ᵇ (succ zero) (succ (succ (succ zero)))) (yes tt)
-- map′ が copattern 定義なので簡約がここで止まり、パターンマッチ時には no の clause を省略できないので注意。
-- ただし、 from-yes / from-no を用いることはできる。

-- C-c C-n 12 ≤? 13

module _ where private
  example1 : 1 ≤ 9
  example1 = from-yes (1 ≤? 9)

  example2 : 32 ≤ 47
  example2 = from-yes (32 ≤? 47)

  example3 : ¬ (2 ≤ 1)
  example3 = from-no (2 ≤? 1)

infix 4 _<ᵇ_

_<ᵇ_ : MyNat → MyNat → Bool
_<ᵇ_ m n = succ m ≤ᵇ n

<ᵇ⇒< : ∀ m n → T (m <ᵇ n) → m < n
<ᵇ⇒< m n = ≤ᵇ⇒≤ (succ m) n

<⇒<ᵇ : ∀ m n → m < n → T (m <ᵇ n)
<⇒<ᵇ m n = ≤⇒≤ᵇ (succ m) n

_<?_ : Decidable _<_
m <? n = m + 1 ≤? n

_>?_ : Decidable _>_
_>?_ = flip _<?_

module _ where private
  example : 1 < 4
  example = from-yes (1 <? 4)

-- 6.7.6 練習問題

module _ where private
  example : (23 < 32) × (12 ≤ 24)
  example = (from-yes (23 <? 32) , from-yes (12 ≤? 24))
