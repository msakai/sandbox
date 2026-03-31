{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module LinearLogic where

import Prelude.Linear
import Data.Void

infix 4 :≅
infixl 6 :⊕
infixl 7 :⊗, :&

type a :≅ b = (a %1 -> b, b %1 -> a)

-- -------------------------------------------------------------------
-- ⊗ (tensor) and 1 (one)
-- -------------------------------------------------------------------

type a :⊗ b = (a, b)

type One = ()

tensor_left_identity :: One :⊗ a :≅ a
tensor_left_identity = (\((), a) -> a, \a -> ((), a))

tensor_commutative :: a :⊗ b -> b :⊗ a
tensor_commutative (a,b) = (b,a)

tensor_associative :: (a :⊗ b) :⊗ c :≅ a :⊗ (b :⊗ c)
tensor_associative = (\((a,b),c) -> (a,(b,c)), \(a,(b,c)) -> ((a,b),c))

-- -------------------------------------------------------------------
-- ⊕ (plus) and 0 (zero)
-- -------------------------------------------------------------------

type a :⊕ b = Either a b

type Zero = Void

absurd' :: Zero %1 -> a
absurd' = \case {}

plus_left_identity :: Zero :⊕ a :≅ a
plus_left_identity = (either absurd' id, Right)

plus_commutative :: a :⊕ b %1 -> b :⊕ a
plus_commutative = either Right Left

plus_associative :: (a :⊕ b) :⊕ c :≅ a :⊕ (b :⊕ c)
plus_associative = (f, g)
  where
    f = either (either Left (Right . Left)) (Right . Right)
    g = either (Left . Left) (either (Left . Right) Right)

-- -------------------------------------------------------------------
-- & (with) and ⊤ (top)
-- -------------------------------------------------------------------

data a :& b where
  With :: (forall r. (a %1 -> r) :⊕ (b %1 -> r) %1 -> r) %1 -> a :& b

fst' :: a :& b %1 -> a
fst' (With k) = k (Left id)

snd' :: a :& b %1 -> b
snd' (With k) = k (Right id)

pair :: (c %1 -> a) -> (c %1 -> b) -> (c %1 -> a :& b)
pair f g c = With (\case { Left k -> k (f c); Right k -> k (g c) })

data Top where
  Top :: (forall r. Zero %1 -> r) %1 -> Top

sink :: a %1 -> Top
sink a = Top (\void -> absurd' void a)

data Top' where
  Top' :: a %1 -> Top'

sink' :: a %1 -> Top'
sink' = Top'

with_left_identity :: Top :& a :≅ a
with_left_identity = (snd', pair sink id)

with_commutative :: a :& b %1 -> b :& a
with_commutative = pair snd' fst'

with_associative :: (a :& b) :& c :≅ a :& (b :& c)
with_associative = (f, g)
  where
    f = pair (fst' . fst') (pair (snd' . fst') snd')
    g = pair (pair fst' (fst' . snd')) (snd' . snd')

-- -------------------------------------------------------------------
-- TODO: ⅋ (par) and ⊥ (bottom)
-- -------------------------------------------------------------------

-- -------------------------------------------------------------------
-- ! (of course)
-- -------------------------------------------------------------------

-- !
type OfCourse a = Ur a

-- -------------------------------------------------------------------
-- TODO: ? (why not)
-- -------------------------------------------------------------------
