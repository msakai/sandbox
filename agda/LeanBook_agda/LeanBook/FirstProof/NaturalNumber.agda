module LeanBook.FirstProof.NaturalNumber where

open import Relation.Binary.PropositionalEquality

data MyNat : Set where
  zero : MyNat
  succ : (n : MyNat) -> MyNat

-- C-c C-d zero

-- C-c C-d succ

-- C-c C-d succ zero

one : MyNat
one = succ zero

two : MyNat
two = succ one

add : MyNat -> MyNat -> MyNat
add m zero = m
add m (succ n) = succ (add m n)

-- C-c C-d add one one ≡ two

-- C-c C-n add one one

-- C-c C-n two

module _ where
  private
    example1 : add one one ≡ two
    example1 = refl

    example2 : (n : MyNat) -> add n zero ≡ n
    example2 n = refl
