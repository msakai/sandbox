{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

import Prelude.Linear

data Normal a where
  Normal :: a %1 -> (a %1 -> ()) -> (a %1 -> (a, a)) -> Normal a

data Linear a where
  Linear :: a %1 -> Linear a

data Affine a where
  Affine :: a %1 -> (a %1 -> ()) -> Affine a

data Relevant a where
  Relevant :: a %1 -> (a %1 -> (a, a)) -> Relevant a

test_normal_0use :: Normal Int %1 -> Int
test_normal_0use (Normal x consume dup) = consume x `lseq` 0

test_normal_1use :: Normal Int %1 -> Int
test_normal_1use (Normal x consume dup) = x

test_normal_2use :: Normal Int %1 -> Int
test_normal_2use (Normal x consume dup) =
  case dup x of
    (x1, x2) -> x1 + x2

-- test_linear_0use :: Linear Int %1 -> Int
-- test_linear_0use (Linear x) = 0

test_linear_1use :: Linear Int %1 -> Int
test_linear_1use (Linear x) = x

-- test_linear_2use :: Linear Int %1 -> Int
-- test_linear_2use x = x + x

test_affine_0use :: Affine Int %1 -> Int
test_affine_0use (Affine x consume) = consume x `lseq` 0

test_affine_1use :: Affine Int %1 -> Int
test_affine_1use (Affine x consume) = x

-- test_affine_2use :: Affine Int %1 -> Int
-- test_affine_2use (Affine x consume) = x + x

-- test_relevant_0use :: Relevant Int %1 -> Int
-- test_relevant_0use (Relevant x dup) = 0

test_relevant_1use :: Relevant Int %1 -> Int
test_relevant_1use (Relevant x dup) = x

test_relevant_2use :: Relevant Int %1 -> Int
test_relevant_2use (Relevant x dup) =
  case dup x of
    (x1, x2) -> x1 + x2
