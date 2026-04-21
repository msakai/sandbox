-- 4.2 帰納法で0 + n = n を証明する
module LeanBook.NatCommMonoid.Induction where

open import Function
open import Relation.Binary.PropositionalEquality

open import LeanBook.NatCommMonoid.TypeClass public

-- example1 : (n : MyNat) → 0 + n ≡ n
-- example1 = refl

-- C-c C-n λ n → n + 0

-- C-c C-n λ n → 0 + n

add-zero : (n : MyNat) → n + 0 ≡ n
add-zero n = refl

module _ where private
  -- Lean の rw [MyNat.add_zero] を翻訳するとこんな感じ?
  example1 : (m n : MyNat) → (n + 0) + m ≡ n + m
  example1 m n = subst (λ x → x + m ≡ n + m) (sym (add-zero n)) (n + m ≡ n + m ∋ refl)

  -- Agda だとこう書くと思うけど
  example1' : (m n : MyNat) → (n + 0) + m ≡ n + m
  example1' m n = cong (λ x → x + m) (add-zero n)

add-zero-rev : (n : MyNat) → n ≡ n + 0
add-zero-rev n = refl

module _ where private
  -- Lean の rw [<- MyNat.add_zero_rev] を翻訳するとこんな感じ?
  example1 : (m n : MyNat) → (n + 0) + m ≡ n + m
  example1 m n = subst (λ x → x + m ≡ n + m) (add-zero-rev n) refl

  -- Lean の rw [MyNat.add_zero] at h; rw [h] を翻訳するとこんな感じ?
  example2 : (m n : MyNat) → (m + 0 ≡ n) → n + m ≡ m + n
  example2 m n h = subst (λ x → n + x ≡ x + n) (sym h') refl
    where
      h' : m ≡ n
      h' = subst (λ x → x ≡ n) (add-zero m) h

  -- Agda だとこう書くと思うけど
  example2' : (m n : MyNat) → (m + 0 ≡ n) → n + m ≡ m + n
  example2' m n h = cong₂ _+_ (sym h') h'
    where
      h' : m ≡ n
      h' = trans (add-zero-rev m) h

add-succ : (m n : MyNat) → m + succ n ≡ succ (m + n)
add-succ m n = refl

zero-add : (n : MyNat) → 0 + n ≡ n
zero-add zero = (0 + zero ≡ zero) ∋ refl
zero-add (succ n') = goal
  where
    ih : 0 + n' ≡ n'
    ih = zero-add n'

    goal' : succ (0 + n') ≡ succ n'
    goal' = cong succ ih

    goal : 0 + succ n' ≡ succ n'
    goal = subst (λ x → x ≡ succ n') (sym (add-succ 0 n')) goal'

module _ where private
  example : (n : MyNat) → 1 + n ≡ succ n
  example zero = refl
  example (succ n) = (1 + succ n) ≡ succ (succ n) ∋ trans h1 h2
    where
      ih : 1 + n ≡ succ n
      ih = example n

      h1 : (1 + succ n) ≡ succ (1 + n)
      h1 = add-succ 1 n

      h2 : succ (1 + n) ≡ succ (succ n)
      h2 = cong succ ih
