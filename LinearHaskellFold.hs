{-# LANGUAGE LinearTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Prelude hiding (foldr)

foldr :: (a %1 -> b %1 -> b) -> b %1 -> [a] %1 -> b
foldr k z [] = z
foldr k z (x : xs) = k x (foldr k z xs)

append_foldr :: [a] %1 -> [a] %1 -> [a]
append_foldr xs ys = foldr (:) ys xs

fold :: (Maybe (a, b) %1 -> b) -> [a] %1 -> b
fold f [] = f Nothing
fold f (x : xs) = f (Just (x, fold f xs))

append_fold_ng :: forall a. [a] %1 -> [a] %1 -> [a]
append_fold_ng xs ys = fold f xs
  where
    f :: Maybe (a, [a]) %1 -> [a]
    f Nothing = ys
    f (Just (x, zs)) = x : zs

append_fold_ok :: [a] %1 -> [a] %1 -> [a]
append_fold_ok = fold f
  where
    f :: Maybe (a, [a] %1 -> [a]) %1 -> ([a] %1 -> [a])
    f Nothing = \xs -> xs
    f (Just (x, g)) = \xs -> x : g xs
