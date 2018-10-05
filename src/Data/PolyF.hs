{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GADTs #-}

module Data.PolyF where

import Data.Functor.Classes
import Control.Applicative
import Text.ParserCombinators.ReadPrec
import Text.ParserCombinators.ReadP

-- | Base `Functor` of polynomials with variables and division
data PolyF a where
  Var :: PolyF a
  (:+) :: a -> a -> PolyF a
  (:-) :: a -> a -> PolyF a
  (:*) :: a -> a -> PolyF a
  (:/) :: a -> a -> PolyF a
  deriving (Eq, Ord, Show, Read, Functor)

-- | Literal equality: @Var :+ Var /= 2 :* Var@
instance Eq1 PolyF where
  liftEq _ Var Var = True
  liftEq _ _ Var = False
  liftEq _ Var _ = False
  liftEq eq (x :+ y) (z :+ w) = eq x z && eq y w
  liftEq _ _ (_ :+ _) = False
  liftEq _ (_ :+ _) _ = False
  liftEq eq (x :- y) (z :- w) = eq x z && eq y w
  liftEq _ _ (_ :- _) = False
  liftEq _ (_ :- _) _ = False
  liftEq eq (x :* y) (z :* w) = eq x z && eq y w
  liftEq _ _ (_ :* _) = False
  liftEq _ (_ :* _) _ = False
  liftEq eq (x :/ y) (z :/ w) = eq x z && eq y w

instance Show1 PolyF where
  liftShowsPrec _ _ _ Var = ("Var" ++)
  liftShowsPrec sp sl n (x :+ y) = showsBinaryWith sp sp ":+" n x y
  liftShowsPrec sp sl n (x :- y) = showsBinaryWith sp sp ":-" n x y
  liftShowsPrec sp sl n (x :* y) = showsBinaryWith sp sp ":*" n x y
  liftShowsPrec sp sl n (x :/ y) = showsBinaryWith sp sp ":/" n x y

instance Read1 PolyF where
  liftReadPrec rp rs =
    (readP_to_Prec (const $ Var <$ string "Var")) <|>
    readBinaryWith rp rp ":+" (:+) <|>
    readBinaryWith rp rp ":-" (:-) <|>
    readBinaryWith rp rp ":*" (:*) <|>
    readBinaryWith rp rp ":/" (:/)

-- | Run a single vase `Functor` layer of a `Poly`
runPolyF :: Fractional a => PolyF a -> a -> a
runPolyF Var x = x
runPolyF (x :+ y) _ = x + y
runPolyF (x :- y) _ = x - y
runPolyF (x :* y) _ = x * y
runPolyF (x :/ y) _ = x / y

