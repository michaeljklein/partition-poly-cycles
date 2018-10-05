{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Data.Poly where

import Data.PolyF
import Control.Applicative
import Data.Maybe
import Control.Monad.Free
import Data.Functor.Classes
import Data.List
import Data.List.Utils


-- | Univariate polynomials
newtype Poly a = Poly
  { unPoly :: Free PolyF a
  } deriving (Eq, Show, Read, Functor, Applicative, Monad)

instance MonadFree PolyF Poly where
  wrap = Poly . wrap . fmap unPoly

-- Warning: `abs` and `signum` are unsupported on all but literals
instance Num a => Num (Poly a) where
  (+) = wrap2 (:+)
  (-) = wrap2 (:-)
  (*) = wrap2 (:*)

  abs (Poly (Pure x)) = Poly (Pure (abs x))
  abs _ = error "abs unsupported on all but literals"

  signum (Poly (Pure x)) = Poly (Pure (signum x))
  signum _ = error "signum unsupported on all but literals"

  fromInteger = return . fromInteger

instance Fractional a => Fractional (Poly a) where
  (/) = wrap2 (:/)
  fromRational = return . fromRational


-- | `Poly` variable
var :: Poly a
var = Poly $ Free Var

-- | Convert a list to a `Poly` if possible
toPoly :: (Eq a, Fractional a) => [a] -> Maybe (Poly a)
toPoly = listToMaybe . toPolys

-- | Convert a list to a list of `Poly`s
toPolys :: (Eq a, Fractional a) => [a] -> [Poly a]
toPolys xs = catMaybes $ zipWith toPolyN [0 .. length xs] (repeat xs)

-- | Convert to `Poly` if possible using the given number of elements
toPolyN :: (Eq a, Fractional a) => Int -> [a] -> Maybe (Poly a)
toPolyN n xs =
  if all (\x -> runPoly poly x == x) xs
    then Just poly
    else Nothing
  where
    ys = takeExactly n xs
    poly = interpolate xs

-- | Interpolate a list of `Fractional` values into a `Poly`
--
-- Currently buggy:
--
-- @
--  λ> runPoly (interpolate [1,2,3]) <$> [0..3]
--  [1.0,1.0,1.0,1.0]
--  (0.01 secs, 485,672 bytes)
-- @
--
interpolate :: Fractional a => [a] -> Poly a
interpolate xs =
  simplify $
  sum
    [ product
      [ (var - return (xs !! j)) / return (xs !! i - xs !! j)
      | j <- [0 .. n]
      , j /= i
      ]
    | i <- [0 .. n]
    ]
  where
    n = length xs - 1

-- | Simplify combinations of constants and @x + x@
simplify :: Fractional a => Poly a -> Poly a
simplify xss@(Poly (Free xs)) =
  case xs of
    (Free Var :+ Free Var) -> 2 * var
    (Pure x :+ Pure y) -> return $ x + y
    (Pure x :- Pure y) -> return $ x - y
    (Pure x :* Pure y) -> return $ x * y
    (Pure x :/ Pure y) -> return $ x / y
    _ -> xss
simplify x = x

-- | Apply a transformation on a `Free` `Monad` on all levels,
-- repeating until equivalence using `fixEq`
freeLevels :: (Functor f, Eq1 f, Eq a) => (Free f a -> Free f a) -> Free f a -> Free f a
freeLevels _ (Pure x) = Pure x
freeLevels f x =
  case fixEq f x of
    y@(Pure _) -> y
    ~(Free y) -> fixEq f . Free $ freeLevels f <$> y

-- | Apply the function until it reaches a fixed point
fixEq :: Eq a => (a -> a) -> a -> a
fixEq f x = loop x (f x)
  where
    loop y z = if y == z
                  then z
                  else loop z (f z)

-- | Examples:
--
-- @
--  λ> simplifyAll (1 + 2 + 3 :: Poly Double)
--  Poly {unPoly = Pure 6.0}
--
--  λ> simplifyAll (1 + 2 + 3 + var :: Poly Double)
--  Poly {unPoly = Free (:+ (Pure 6.0) (Free Var))}
--
--  λ> simplifyAll (1 + 2 + 3 * (var + var) :: Poly Double)
--  Poly {unPoly = Free (:+ (Pure 3.0) (Free (:* (Pure 3.0) (Free (:* (Pure 2.0) (Free Var))))))}
-- @
--
simplifyAll :: (Fractional a, Eq a) => Poly a -> Poly a
simplifyAll = Poly . freeLevels (unPoly . simplify . Poly) . unPoly

-- | `wrap` after applying a binary function
wrap2 :: MonadFree m f => (a -> b -> m (f c)) -> a -> b -> f c
wrap2 f x = wrap . f x

-- | Evaluate a univariate polynomial on the given input
runPoly :: Fractional a => Poly a -> a -> a
runPoly (Poly poly) x = iter (`runPolyF` x) poly

