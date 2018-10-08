# partition-poly-cycles

Several implementations calculating the number of partitions of `n` elements
into disjoint sets with at most `k` elements and analysis of the resulting series.


## Polynomial representation

We consider bivariate polynomials `p(x, y) :: (Integer, Integer) -> Integer`
and set `y := x modulo m` for some positive modulus `m`.

For brevity and lack of a better term, we call these "cyclic polynomials",
not to be confused with
[polynomial functions that are invariant under cyclic permutation of the arguments.](https://brilliant.org/wiki/cyclic-polynomials/).

These are exactly the piecewise functions with `m` polynomial pieces where
the piece is chosen by the remainder modulo `m`.


### Recognition

The ring of these functions is closed under:

- First differences
- Alternation (negate indices in a cyclic pattern)
- Integer multiplication
- Exact integer division
  + By "exact integer division", we mean `exactDiv` below:

```haskell
exactDiv :: Integral a => a -> a -> Maybe a
exactDiv x y =
  case divMod x y of
    (div', 0) -> Just div'
    _         -> Nothing
```

So we may take any combination of these operations on an input series
and preserve whether the series is representable by a cyclic polynomial.

If a series is a cycle, it's trivially representable by a cyclic polynomial:

```haskell
baseCycle :: Integer

mySeries :: [Integer]
mySeries = cycle baseCycle

-- | Interpolating polynomial:
--     [0..length baseCycle] -> baseCycle
interpBaseCycle :: Integer -> Integer

myCyclicPoly :: Integer -> Integer
myCyclicPoly x = interpBaseCycle (x `mod` length baseCycle)
```

Thus we can recognize some cyclic polynomials by transforming the series
using first differences and isolation to isolate an underlying cycle.


### Note

While the above method for recognizing cyclic polynomials could be generalized
to more dimensions, I expect the 1D version to be the most applicable.


## Analysis

We use the above methods to analyze and optimize calculating the
number of partitions for subsets of a given size along different axes.


# Docs

Haddock generated documentation may be found [here](https://michaeljklein.github.io/partition-poly-cycles/)

