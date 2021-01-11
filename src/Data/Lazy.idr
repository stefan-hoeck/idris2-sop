module Data.Lazy

public export
Eq a => Eq (Lazy a) where
  x == y = x == y

public export
Ord a => Ord (Lazy a) where
  compare x y = compare x y

public export
Semigroup a => Semigroup (Lazy a) where
  x <+> y = x <+> y

public export
Monoid a => Monoid (Lazy a) where
  neutral = neutral

public export
Show a => Show (Lazy a) where
  showPrec p a = showPrec p a

public export
Num a => Num (Lazy a) where
  a + b = a + b
  a * b = a * b
  fromInteger n = fromInteger n

public export
Neg a => Neg (Lazy a) where
  negate a = negate a
  a - b = a - b

public export
Abs a => Abs (Lazy a) where
  abs a = abs a

public export
Fractional a => Fractional (Lazy a) where
  a / b = a / b
  recip a = recip a

public export
Integral a => Integral (Lazy a) where
  a `mod` b = a `mod` b
  a `div` b = a `div` b
