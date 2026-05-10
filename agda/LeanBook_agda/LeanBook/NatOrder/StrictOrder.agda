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

infix 4 _<_

_<_ : (m n : MyNat) → Set
m < n = m + 1 ≤ n

module _ where private
  example : (m n : MyNat) → m < n ⇔ (m + 1) ≤ n
  example m n = mk⇔ id id

-- 6.3.2 狭義順序と広義順序、等号の関係

one-neq-zero : (MyNat ∋ 1) ≢ 0
one-neq-zero ()

zero-neq-one : (MyNat ∋ 0) ≢ 1
zero-neq-one ()

zero-le : (n : MyNat) → 0 ≤ n
zero-le n = ≤-intro (zero-add n)

zero-of-le-zero : {n : MyNat} (h : n ≤ 0) → n ≡ 0
zero-of-le-zero ≤-refl = refl

le-zero : {n : MyNat} → n ≤ 0 ⇔ n ≡ 0
le-zero {n} = mk⇔ zero-of-le-zero from
  where
    from : n ≡ 0 → n ≤ 0
    from refl = ≤-refl

-- これは書籍にはなかった定理
le-succ-monotone : {n m : MyNat} → n ≤ m → succ n ≤ succ m
le-succ-monotone ≤-refl = ≤-refl
le-succ-monotone (≤-step h) = ≤-step (le-succ-monotone h)

eq-zero-or-pos : (n : MyNat) → n ≡ 0 ⊎ 0 < n
eq-zero-or-pos zero = inj₁ refl
eq-zero-or-pos (succ n) = inj₂ (le-succ-monotone (zero-le n))

eq-or-lt-of-le : {m n : MyNat} → n ≤ m → n ≡ m ⊎ n < m
eq-or-lt-of-le ≤-refl = inj₁ refl
eq-or-lt-of-le (≤-step h) = inj₂ (le-succ-monotone h)

le-of-lt : {a b : MyNat} → a < b → a ≤ b
le-of-lt {a} a<b = ≤-trans (≤-add-one-right a) a<b

le-of-eq-or-lt : {m n : MyNat} → (n ≡ m ⊎ n < m) → n ≤ m
le-of-eq-or-lt (inj₁ refl) = ≤-refl
le-of-eq-or-lt (inj₂ n<m) = le-of-lt n<m

le-iff-eq-or-lt : {m n : MyNat} → (n ≤ m) ⇔ (n ≡ m ⊎ n < m)
le-iff-eq-or-lt = mk⇔ eq-or-lt-of-le le-of-eq-or-lt

lt-or-ge : (a b : MyNat) → a < b ⊎ b ≤ a
lt-or-ge a zero = inj₂ (zero-le a)
lt-or-ge a (succ b) with lt-or-ge a b
... | inj₁ a<b = inj₁ (le-succ-monotone (le-of-lt a<b))
... | inj₂ b≤a with eq-or-lt-of-le b≤a
...   | inj₁ refl = inj₁ ≤-refl
...   | inj₂ b<a  = inj₂ b<a

lt-of-not-le : {a b : MyNat} → (¬ a ≤ b) → b < a
lt-of-not-le {a} {b} a≰b with lt-or-ge b a
... | inj₁ b<a = b<a
... | inj₂ a≤b = ⊥-elim (a≰b a≤b)

not-le-of-lt : {a b : MyNat} → a < b → ¬ b ≤ a
not-le-of-lt {a} {b} a<b b≤a with ≤-dest a<b | ≤-dest b≤a
... | (k , a+1+k≡b) | (l , b+l≡a) = ⊥-elim lem4
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

    lem4 : ⊥
    lem4 with lem3
    ... | ()

le-total : (a b : MyNat) → a ≤ b ⊎ b ≤ a
le-total a b with lt-or-ge a b
... | inj₁ a<b = inj₁ (le-of-lt a<b)
... | inj₂ b≤a = inj₂ b≤a

-- 6.3.3 練習問題（回答は203 ページ）

module _ where private
  example1 : (a : MyNat) → ¬ (a ≡ a + 1)
  example1 a ()

  example2 : (n : MyNat) → ¬ n + 1 ≤ n
  example2 n n+1≤n = not-le-of-lt n+1≤n ≤-refl
