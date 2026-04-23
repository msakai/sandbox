-- 4.5 帰納法を改善する
module LeanBook.NatCommMonoid.BetterInduction where

open import Level using (Level)
import Level
open import Relation.Binary.PropositionalEquality
open import LeanBook.NatCommMonoid.AcRfl public

module _ where private
  example : (m n : MyNat) → m + n ≡ n + m
  example m zero = sym (zero-add m)
  example m (succ n) = begin
    m + succ n   ≡⟨ add-succ m n ⟩
    succ (m + n) ≡⟨ cong succ ih ⟩
    succ (n + m) ≡⟨ sym (succ-add n m) ⟩
    succ n + m
    ∎
    where
      open ≡-Reasoning
      ih : m + n ≡ n + m
      ih = add-comm m n

MyNat-rec : {ℓ : Level} {motive : MyNat → Set ℓ}
  → (zero : motive zero)
  → (succ : (n : MyNat) → motive n → motive (succ n))
  → (t : MyNat) → motive t
MyNat-rec z s zero = z
MyNat-rec z s (succ n) = s n (MyNat-rec z s n)

module _ where private
  example : (m n : MyNat) → m + n ≡ n + m
  example m n = MyNat-rec {motive = motive} z s n
    where
      open ≡-Reasoning

      motive : MyNat → Set
      motive n = m + n ≡ n + m

      z : m + zero ≡ zero + m
      z = (sym (zero-add m))

      s : (n : MyNat) → m + n ≡ n + m → m + succ n ≡ succ n + m
      s n ih = add-comm m (succ n)

MyNat-rec-aux : {ℓ : Level} {motive : MyNat → Set ℓ}
  → (zero : motive 0)
  → (succ : (n : MyNat) → motive n → motive (n + 1))
  → (t : MyNat) → motive t
MyNat-rec-aux z s zero = z
MyNat-rec-aux z s (succ n) = s n (MyNat-rec-aux z s n)

module _ where private
  example : (m n : MyNat) → m + n ≡ n + m
  example m n = MyNat-rec-aux {motive = motive} z s n
    where
      open ≡-Reasoning

      motive : MyNat → Set
      motive n = m + n ≡ n + m

      z : m + 0 ≡ 0 + m
      z = (sym (zero-add m))

      s : (n : MyNat) → m + n ≡ n + m → m + (n + 1) ≡ (n + 1) + m
      s n ih = add-comm m (n + 1)

module _ where private
  pred : MyNat → MyNat
  pred zero = 0
  pred (succ n) = n

  example : (n : MyNat) → pred (pred n + 1) ≡ pred n
  example zero = refl
  example (succ n) = refl
