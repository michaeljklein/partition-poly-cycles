{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Lib where

import Control.Applicative
import Control.Monad
import Control.Monad.Free
import Control.Monad.Free.TH
import Data.Function.Memoize
import Data.Functor.Classes
import Data.List
import Data.List.Utils
import Data.Maybe
import Data.Poly
import Data.Time.Clock
import Data.Tuple
import System.Environment
import Test.QuickCheck
import Text.ParserCombinators.ReadP
import Text.ParserCombinators.ReadPrec

-- | @`parts` k n@ is the number of partitions of @n@ elements
-- mutually disjoint subsets of at most @k@ elements
parts :: (Num a, Ord a, Num p) => a -> a -> p
parts 0 0 = 1
parts k n
  | n <= 0 || k <= 0 = 0
parts k n = parts k (n - k) + parts (k - 1) (n - 1)

-- | `parts` decreasing inputs
prop_partsDecInputs :: Integer -> Integer -> Property
prop_partsDecInputs =
    (\x y -> ((x :: Integer) > y) ==> (parts x y == (0 :: Integer)))

-- | `parts` with specific handling for more cases
parts1 :: (Num a, Ord a, Num p) => a -> a -> p
parts1 0 0 = 1
parts1 k n
  | n <= 0 || k <= 0 || n < k = 0
parts1 k n = parts1 k (n - k) + parts1 (k - 1) (n - 1)

-- | `parts1` to `parts2`
prop_parts1ToParts2 :: Integer -> Integer -> Bool
prop_parts1ToParts2 =
  (\n ->
       (\x y ->
          let [z, w] = map (`mod` n) [x, y]
           in parts1 z w == parts2 z w))
    (60 :: Integer)

-- | `parts` for equal positive inputs equal to @1@
--
-- @
--  (\x -> (1 <= x) ==> (parts x x == 1))
-- @
--
prop_partsOnLine1 :: Integer -> Property
prop_partsOnLine1 =
    (\x -> ((1 :: Integer) <= x) ==> (parts x x == (1 :: Integer)))

-- | `parts` version 2
parts2 :: (Num a, Ord a, Num p) => a -> a -> p
parts2 0 0 = 1
parts2 k n
  | n <= 0 || k <= 0 || n < k = 0
parts2 k n
  | n == k = 1
parts2 k n = parts2 k (n - k) + parts2 (k - 1) (n - 1)

-- | `parts1` to `parts2` with a modulus
prop_parts1ToParts2Mod :: Integer -> Integer -> Bool
prop_parts1ToParts2Mod =
  (\n ->
       (\x y ->
          let [z, w] = map (`mod` n) [x, y]
           in parts1 z w == parts2 z w))
    (60 :: Integer)


-- | `parts` version 3
parts3 :: (Integral a, Ord a) => a -> a -> a
parts3 0 0 = 1
parts3 1 _ = 1
parts3 2 n = (2 * n - 1 + (-1) ^ n) `div` 4
parts3 k n
  | n <= 0 || k <= 0 || n < k = 0
parts3 k n
  | n == k = 1
parts3 k n = parts3 k (n - k) + parts3 (k - 1) (n - 1)

-- | `parts2` to `parts3`
prop_parts2ToParts3 :: Integer -> Integer -> Bool
prop_parts2ToParts3 =
  (\n ->
       (\x y ->
          let [z, w] = map (`mod` n) [x, y]
           in parts2 z w == parts3 z w))
    (60 :: Integer)

-- | `parts` version 4
--
-- @
--  p 3 n = p 3 (n - 3) + p 2 (n - 1)
--    p 3 (n - 3) = p 3 (n - 6) + p 2 (n - 4) = p 3 (n - 6) + (2 * (n - 4) - 1 + (- 1) ^ (4 * n)) `div` 4 = p 3 (n - 6) + (2 * n - 8) `div` 4 = p 3 (n - 6) + (n - 4) `div` 2
--    p 2 (n - 1) = p 2 (n - 3) + p 1 (n - 2) = p 2 (n - 3) + 1 = (2 * (n - 3) - 1 + (- 1) ^ (n - 3)) `div` 4 = (2 * n - 6 - (- 1) ^ n) `div` 4
--  p 3 n = p 3 (n - 6) + (n - 4) `div` 2 + (2 * n - 6 - (- 1) ^ n) `div` 4
--  p 3 n = p 3 (n - 6) + (2 * n - 8 + 2 * n - 6 - (- 1) ^ n) `div` 4
--  p 3 n = p 3 (n - 6) + (4 * n - 14 - (- 1) ^ n) `div` 4
-- @
--
parts4 :: (Integral a, Ord a) => a -> a -> a
parts4 0 0 = 1
parts4 1 _ = 1
parts4 2 n = (2 * n - 1 + (-1) ^ n) `div` 4
parts4 k n
  | n <= 0 || k <= 0 || n < k = 0
parts4 k n
  | n == k = 1
parts4 3 n = parts4 3 (n - 6) + n - 3
parts4 k n = parts4 k (n - k) + parts4 (k - 1) (n - 1)

-- | Relation for multiples of arguments
--
-- @
--  (\x y -> (x > y && 0 < y) ==> (parts4 x (x + y) == parts4 y (2 * y)))
-- @
--
prop_parts4PlusTimes :: Integer -> Integer -> Property
prop_parts4PlusTimes =
    (\x y ->
       (x > y && (0 :: Integer) < y) ==> (parts4 x (x + y) == parts4 y (2 * y)))


-- | `parts` version 5
{-# SPECIALIZE parts5 :: Integer -> Integer -> Integer #-}
parts5 :: (Integral a, Ord a) => a -> a -> a
parts5 0 0 = 1
parts5 1 _ = 1
parts5 2 n = (2 * n - 1 + (-1) ^ n) `div` 4
parts5 k n
  | n <= 0 || k <= 0 || n < k = 0
parts5 k n
  | n == k = 1
parts5 3 n = parts5 3 (n - 6) + n - 3
parts5 k n
  | 2 * k > n =
    let nk = n - k
     in parts5 nk (2 * nk)
parts5 k n = parts5 k (n - k) + parts5 (k - 1) (n - 1)

-- | `parts` version 5
--
-- Alternate implementation of `part5`
parts6 :: Integer -> Integer -> Integer
parts6 = memoFix2 parts6'
  where
    parts6' _ 0 0 = 1
    parts6' _ 1 _ = 1
    parts6' _ 2 n = (2 * n - 1 + (-1) ^ n) `div` 4
    parts6' _ k n
      | n <= 0 || k <= 0 || n < k = 0
    parts6' _ k n
      | n == k = 1
    parts6' f 3 n = f 3 (n - 6) + n - 3
    parts6' f k n
      | 2 * k > n =
        let nk = n - k
         in f nk (2 * nk)
    parts6' f k n = f k (n - k) + f (k - 1) (n - 1)

-- | `part4` to `part5`
prop_parts4ToParts5 :: Integer -> Integer -> Bool
prop_parts4ToParts5 =
  (\n ->
       (\x y ->
          let [z, w] = map (`mod` n) [x, y]
           in parts4 z w == parts5 z w))
    (60 :: Integer)

-- | Example cyclic series
--
-- @
--  scanl(+) c (cycle [a1, a2, .., an])
-- @
--
cyclicSeriesEx :: Num a => [a]
cyclicSeriesEx = scanl (+) 1 (scanl (+) 1 (cycle [0, 0, 0, 1, -1, 1]))


-- | `part5` to `cyclicSeriesEx`
prop_part5ToCyclicSeriesEx :: Bool
prop_part5ToCyclicSeriesEx =
  (\x -> and . take x $ zipWith (==) (parts5 3 <$> [4 ..]) cyclicSeriesEx) 1000

-- | `ff` to `cyclicSeriesEx`
prop_ffToCyclicSeriesEx :: Bool
prop_ffToCyclicSeriesEx =
  (\x -> and . take x $ zipWith (==) (ff <$> [0 ..]) cyclicSeriesEx) 1000


-- | See `prop_ffToCyclicSeriesEx`
ff :: Integral a => a -> a
ff x =
  case divMod x 6 of
    (y, 0) ->
      let n = y + 1
       in n * (3 * n - 2)
    (y, 1) ->
      let n = y + 1
       in n * (3 * n - 1)
    (y, 2) ->
      let n = y + 1
       in n * (3 * n - 0)
    (y, 3) ->
      let n = y + 1
       in n * (3 * n + 1)
    (y, 4) ->
      let n = y + 1
       in n * (3 * n + 2)
    (y, 5) ->
      let n = y + 1
       in 3 * n ^ 2 + 3 * n + 1


-- | Find a "poly cycle", i.e. a cycle that results from taking `alternate`'s
-- and `diff`'s of the original series.
--
-- Such a cycle can always be reconstituted into a piecewise polynomial,
-- with cases for each residue modulo the period of the cycle.
{-# SPECIALIZE findPolyCycle :: Integer -> Maybe ([Integer], Int) #-}
findPolyCycle :: Integral a => a -> Maybe ([a], Int)
findPolyCycle x =
  listToMaybe .
  mapMaybe
    (\(ys, len) ->
       if fromMaybe False $
          all ((== len) . snd) <$>
          mapM (findPolyCycleN x) [2 * len .. 3 * len - div len 2]
         then Just (ys, len)
         else Nothing) $
  mapMaybe ((>>= boolMaybe ((/= 1) . snd)) . findPolyCycleN x) [fromEnum x ..]

-- | `findPolyCycle` with a given period, applied to `parts5`
findPolyCycleN :: Integral a => a -> Int -> Maybe ([a], Int)
findPolyCycleN x y =
  fmap (fmap length . join (,)) .
  findCycle .
  until (isJust . findCycle) (autoAlternate . diff) . take y . fmap (parts5 x) $
  [x + 2 ..]

-- | `findCycle` and print, from `autoAlternate`ing `parts5`
exampleFindCycle :: (Show a, Integral a) => a -> Int -> IO ()
exampleFindCycle x y =
  print . fmap (fmap length . join (,)) . findCycle $
  until
    (isJust . findCycle)
    (autoAlternate . diff)
    (take y $ parts5 x <$> [x ..])


-- | Nest a function @n@ times on the input
nest :: Int -> (a -> a) -> a -> a
nest 0 _ x = x
nest 1 f x = f x
nest n f x = nest (n - 1) f (f x)

-- | `Integral` log base @2@
log2 :: Integral a => a -> a
log2 0 = 0
log2 1 = 0
log2 n = 1 + log2 (div n 2)

-- | `mapM_` with timing information printed
mapMTimed_ :: (a -> IO ()) -> [a] -> IO ()
mapMTimed_ _ [] = putStrLn "(done)"
mapMTimed_ f ~(x:xs) = do
  seconds <-
    (/ 1000000000000.0) . fromInteger . toEnum . fromEnum <$> timed (f x)
  putStrLn $ unwords ["Took", show (seconds :: Double), "s"]
  mapMTimed_ f xs

-- | Run and get duration using `getCurrentTime`
timed :: IO () -> IO NominalDiffTime
timed action = do
  timeBefore <- getCurrentTime
  action
  timeAfter <- getCurrentTime
  return $ timeAfter `diffUTCTime` timeBefore

-- | @`findPolyCycleN` 6 <$> [1..]@
runMain :: IO ()
runMain = do
  mapMTimed_ (print . fmap (`findPolyCycleN` 6) . join (,)) [1..]
  -- mapMTimed_ (print . fmap (fmap swap . findPolyCycle) . join (,)) [2..]
  -- [x, y] <- fmap read <$> getArgs
  -- print.fmap(fmap length.join(,)).findCycle$until(isJust.findCycle)(autoAlternate.diff)(take y$parts5 x<$>[x..])

return []
runTests :: IO Bool
runTests = $quickCheckAll

