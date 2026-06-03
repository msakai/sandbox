-- 6.3 狭義順序を定義する
module LeanBook.NatOrder.StrictOrder where

open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Negation

open import LeanBook.NatOrder.OrderDef public


-- 6.3.1 狭義順序の定義

infix 4 _<_ _>_ _≮_ _≯_

_<_ : (m n : MyNat) → Set
m < n = m + 1 ≤ n

_>_ : (m n : MyNat) → Set
m > n = n < m

_≮_ : (m n : MyNat) → Set
m ≮ n = ¬ m < n

_≯_ : (m n : MyNat) → Set
m ≯ n = n ≮ m

module _ where private
  example : (m n : MyNat) → m < n ⇔ (m + 1) ≤ n
  example m n = mk⇔ id id

-- 6.3.2 狭義順序と広義順序、等号の関係

1≢0 : (MyNat ∋ 1) ≢ 0
1≢0 ()

0≢1 : (MyNat ∋ 0) ≢ 1
0≢1 ()

0≤n : {n : MyNat} → 0 ≤ n
0≤n {n} = ≤-intro (zero-add n)

n≤0⇒n≡0 : {n : MyNat} (h : n ≤ 0) → n ≡ 0
n≤0⇒n≡0 ≤-refl = refl

n≤0⇔n≡0 : {n : MyNat} → n ≤ 0 ⇔ n ≡ 0
n≤0⇔n≡0 {n} = mk⇔ n≤0⇒n≡0 from
  where
    from : n ≡ 0 → n ≤ 0
    from refl = ≤-refl

-- これは書籍にはなかった定理
s≤s : {n m : MyNat} → n ≤ m → succ n ≤ succ m
s≤s ≤-refl = ≤-refl
s≤s (≤-step h) = ≤-step (s≤s h)

n≡0∨0<n : (n : MyNat) → n ≡ 0 ⊎ 0 < n
n≡0∨0<n zero = inj₁ refl
n≡0∨0<n (succ n) = inj₂ (s≤s 0≤n)

m≤n⇒m≡n∨m<n : {m n : MyNat} → m ≤ n → m ≡ n ⊎ m < n
m≤n⇒m≡n∨m<n ≤-refl = inj₁ refl
m≤n⇒m≡n∨m<n (≤-step h) = inj₂ (s≤s h)

<⇒≤ : {a b : MyNat} → a < b → a ≤ b
<⇒≤ {a} a<b = ≤-trans (≤-add-one-right a) a<b

m≡n∨m<n⇒m≤n : {m n : MyNat} → (m ≡ n ⊎ m < n) → m ≤ n
m≡n∨m<n⇒m≤n (inj₁ refl) = ≤-refl
m≡n∨m<n⇒m≤n (inj₂ m<n) = <⇒≤ m<n

m≤n⇔m≡n∨m<n : {m n : MyNat} → (m ≤ n) ⇔ (m ≡ n ⊎ m < n)
m≤n⇔m≡n∨m<n = mk⇔ m≤n⇒m≡n∨m<n m≡n∨m<n⇒m≤n

m<n∨m≥n : (a b : MyNat) → a < b ⊎ a ≥ b
m<n∨m≥n a zero = inj₂ 0≤n
m<n∨m≥n a (succ b) with m<n∨m≥n a b
... | inj₁ a<b = inj₁ (s≤s (<⇒≤ a<b))
... | inj₂ b≤a with m≤n⇒m≡n∨m<n b≤a
...   | inj₁ refl = inj₁ ≤-refl
...   | inj₂ b<a  = inj₂ b<a

≰⇒> : {a b : MyNat} → a ≰ b → a > b
≰⇒> {a} {b} a≰b with m<n∨m≥n b a
... | inj₁ b<a = b<a
... | inj₂ b≥a = ⊥-elim (a≰b b≥a)

<⇒≱ : {a b : MyNat} → a < b → a ≱ b
<⇒≱ {a} {b} a<b b≤a with ≤-dest a<b | ≤-dest b≤a
... | (k , a+1+k≡b) | (l , b+l≡a) with lem3
  where
    open ≡-Reasoning

    lem1 : (b + l) + 1 + k ≡ b
    lem1 = subst (λ x → x + 1 + k ≡ b) (sym b+l≡a) a+1+k≡b

    lem2 : b + (l + k + 1) ≡ (b + l) + 1 + k
    lem2 = begin
      b + (l + k + 1)    ≡⟨ add-assoc b (l + k) 1 ⟩
      (b + (l + k)) + 1  ≡⟨ cong (λ x → x + 1) (sym (add-assoc b l k)) ⟩
      b + l + k + 1      ≡⟨ add-assoc (b + l) k 1 ⟩
      (b + l) + (k + 1)  ≡⟨ cong (λ x → (b + l) + x) (add-comm k 1) ⟩
      (b + l) + (1 + k)  ≡⟨ sym (add-assoc (b + l) 1 k) ⟩
      (b + l) + 1 + k
      ∎

    lem3 : l + k + 1 ≡ 0
    lem3 = add-left-cancel b (l + k + 1) 0 (trans lem2 lem1)
... | ()

m≤n∨m≥n : (a b : MyNat) → a ≤ b ⊎ a ≥ b
m≤n∨m≥n a b with m<n∨m≥n a b
... | inj₁ a<b = inj₁ (<⇒≤ a<b)
... | inj₂ b≤a = inj₂ b≤a

-- 6.3.3 練習問題（回答は203 ページ）

module _ where private
  example1 : (a : MyNat) → a ≢ a + 1
  example1 a ()

  example2 : (n : MyNat) → n ≮ n
  example2 n n<n = <⇒≱ n<n ≤-refl
