module Data.List.Utils where

import Data.List
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe

-- | Break up a list into chunks of size @n@, or @< n@ if
-- there are @< n@ elements (remaining) in the list
--
-- @
--  λ> chunks 1 [1..10]
--  [[1],[2],[3],[4],[5],[6],[7],[8],[9],[10],[]]
--
--  λ> chunks 2 [1..10]
--  [[1,2],[3,4],[5,6],[7,8],[9,10],[]]
--
--  λ> chunks 3 [1..10]
--  [[1,2,3],[4,5,6],[7,8,9],[10]]
-- @
--
chunks :: Int -> [a] -> [[a]]
chunks n = loop n []
  where
    loop 0 xs ys = reverse xs : loop n [] ys
    loop _ xs [] = [reverse xs]
    loop n xs (y:ys) = loop (n - 1) (y : xs) ys

-- | Negate all numbers at odd indices
--
-- For example:
--
-- @
--  λ> alternate [0..10]
--  [0,-1,2,-3,4,-5,6,-7,8,-9,10]
-- @
--
alternate :: Num a => [a] -> [a]
alternate [] = []
alternate [x] = [x]
alternate ~(x:y:zs) = x : negate y : alternate zs

-- | `alternate` if `signum`s of the first two elements differ
--
-- For example:
--
-- It adds alternation to @[0..10]@ because
-- @(signum 0 == 0) /= (signum 1 == 1)@:
--
-- @
--  λ> autoAlternate [0..10]
--  [0,-1,2,-3,4,-5,6,-7,8,-9,10]
-- @
--
-- And removes alternation from an already alternating list:
--
-- @
--  λ> autoAlternate $ alternate [0..10]
--  [0,1,2,3,4,5,6,7,8,9,10]
-- @
--
autoAlternate :: (Num a, Ord a) => [a] -> [a]
autoAlternate [] = []
autoAlternate [x] = [x]
autoAlternate ~(x:y:zs)
  | signum x /= signum y = alternate (x : y : zs)
  | otherwise = x : y : zs


-- | First (forward) differences:
--
-- @
--  λ> diff [1..10]
--  [1,1,1,1,1,1,1,1,1]
-- @
--
-- @
--  λ> diff [1,3..10]
--  [2,2,2,2]
-- @
--
diff :: Num a => [a] -> [a]
diff = zipWith (-) =<< drop 1

-- | Automatically alternate the first differences
--
-- @
--   `autoAlternate` . `diff`
-- @
--
autoDiff :: (Ord a, Num a) => [a] -> [a]
autoDiff = autoAlternate . diff

-- | Take exactly the given number of elements or return `Nothing`
takeExactly :: Int -> [a] -> Maybe [a]
takeExactly 0 [] = Just []
takeExactly 0 _ = Just []
takeExactly _ [] = Nothing
takeExactly n ~(x:xs) = (x :) <$> takeExactly (n - 1) xs

-- | Find a subsequence @ys@ of @xs@ such that:
--
-- @
--  and $ zipWith (==) xs (cycle ys)
-- @
--
findCycle :: Eq a => [a] -> Maybe [a]
findCycle [] = Nothing
findCycle [x] = Just [x]
findCycle xs =
  listToMaybe $ boolMaybe (`isCycle` xs) `mapMaybe` init (tail (inits xs))

-- | Is the second argument equal to:
--
-- @
--  take n $ cycle xs
-- @
--
-- for some @n@?
--
-- @
--  λ> all (\n -> isCycle [1,2] (take n $ cycle [1, 2])) [2..2^12]
--  True
--  (0.53 secs, 1,884,383,408 bytes)
--
--  λ> any (\n -> isCycle [1,2] (take n $ 2 : cycle [1, 2])) [2..2^12]
--  False
--  (0.01 secs, 4,943,968 bytes)
-- @
--
isCycle :: Eq a => [a] -> [a] -> Bool
isCycle xs = and . zipWith (==) (cycle xs)

-- | `Just` if the predicate returns `True`
--
-- For example, use with `mapMaybe` to filter a list:
--
-- @
--  λ> mapMaybe (boolMaybe odd) [1..10]
--  [1,3,5,7,9]
-- @
--
-- Should be equivalent to:
--
-- @
--  \\p -> liftM2 (>>) ((\`unless\` Nothing) . p) return
-- @
--
boolMaybe :: (a -> Bool) -> a -> Maybe a
boolMaybe p x =
  if p x
    then Just x
    else Nothing

