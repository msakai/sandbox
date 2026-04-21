-- 4.3 等式変形による単純化を自動化する
module LeanBook.NatCommMonoid.Simp where

open import Relation.Binary.PropositionalEquality

open import LeanBook.NatCommMonoid.Induction

module _ where private
  example : (n : MyNat) → 0 + (n + 0) ≡ n
  example n = trans h1 h2
    where
      h1 : 0 + (n + 0) ≡ n + 0
      h1 = zero-add (n + 0)
      h2 : n + 0 ≡ n
      h2 = add-zero n

ctor-eq-zero : zero ≡ 0
ctor-eq-zero = refl

module _ where private
  example1 : (m n : MyNat) → (m + n + 0 ≡ n + m) → m + n ≡ n + m
  example1 m n h = h'
    where
      h' : m + n ≡ n + m
      h' = subst (λ x → x + 0 ≡ n + m) (add-zero (m + n)) h

  example2 : (m n : MyNat) → (m + 0 ≡ n) → (m + 0) + 0 ≡ n
  example2 m n h = subst (λ x → x ≡ n) (sym (add-zero m)) goal'
    where
      h' : m ≡ n
      h' = subst (λ x → x ≡ n) (add-zero m) h

      goal' : (m + 0) ≡ n
      goal' = subst (λ x → x ≡ n) (sym (add-zero m)) goal''
        where
          goal'' : m ≡ n
          goal'' = h'

succ-add : (m n : MyNat) → succ m + n ≡ succ (m + n)
succ-add m zero = refl
succ-add m (succ n) = goal
  where
    ih : succ m + n ≡ succ (m + n)
    ih = succ-add m n

    goal : succ m + succ n ≡ succ (m + succ n)
    goal = subst (λ x → succ (succ m + n) ≡ succ x) (sym (add-succ m n)) goal'
      where
        goal' : succ (succ m + n) ≡ succ (succ (m + n))
        goal' = cong succ ih

module _ where private
  open ≡-Reasoning

  example1 : (m n : MyNat) → succ m + n ≡ succ (m + n)
  example1 m zero = refl
  example1 m (succ n) = begin
    succ m + (succ n)   ≡⟨ add-succ (succ m) n ⟩
    succ (succ m + n)   ≡⟨ cong succ ih ⟩
    succ (succ (m + n)) ≡⟨ cong succ (sym (add-succ m n)) ⟩
    succ (m + succ n)
    ∎
    where
      ih : succ m + n ≡ succ (m + n)
      ih = succ-add m n

  example2 : (n : MyNat) → 1 + n ≡ n + 1
  example2 n = begin
    1 + n        ≡⟨ refl ⟩
    succ 0 + n   ≡⟨ succ-add 0 n ⟩
    succ (0 + n) ≡⟨ cong succ (zero-add n) ⟩
    succ n       ≡⟨ refl ⟩
    n + 1
    ∎

  example3 : (n : MyNat) → 2 + n ≡ n + 2
  example3 n = begin
    2 + n                   ≡⟨ succ-add 1 n ⟩
    succ (1 + n)            ≡⟨ cong succ (succ-add 0 n) ⟩
    succ (succ (zero + n))  ≡⟨ cong (λ x → succ (succ x)) (zero-add n) ⟩
    succ (succ n)           ≡⟨ refl ⟩
    n + 2
    ∎
