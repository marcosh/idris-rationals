module Rationals

import NonZeroInt

-- contrib
import Control.Algebra

%access export
%default total

private
record FreeRational where
  constructor MkFreeRational
  num : Int
  den : NonZeroInt
  
Rational : Type
Rational = FreeRational

rational : Int -> NonZeroInt -> Rational
rational = MkFreeRational

intAsRational : Int -> Rational
intAsRational n = rational n (MkNonZeroInt 1 oneNotZero)
  where
    distinguish : Int -> Type
    distinguish 0 = Void
    distinguish _ = ()
    oneNotZero = \oneEqualsZero => replace {P=distinguish} oneEqualsZero ()

postulate
rationalQuotient :
     (num1, num2 : Int)
  -> (den1, den2 : NonZeroInt)
  -> (num1 * (num den2) = num2 * (num den1))
  -> rational num1 den1 = rational num2 den2

fold :
     (map : Int -> NonZeroInt -> a)
  -> ( (num1, num2 : Int)
    -> (den1, den2 : NonZeroInt)
    -> (num1 * (num den2) = num2 * (num den1))
    -> map num1 den1 = map num2 den2)
  -> Rational
  -> a
fold map mapCoherence (MkFreeRational num den) = map num den

-- operations on rationals

rationalEq : Rational -> Rational -> Bool
rationalEq (MkFreeRational num1 den1) (MkFreeRational num2 den2) = num1 * (num den2) == num2 * (num den1)

implementation Eq Rational where
  (==) = rationalEq

rationalCompare : Rational -> Rational -> Ordering
rationalCompare (MkFreeRational num1 den1) (MkFreeRational num2 den2) = compare (num1 * (num den2)) (num2 * (num den1))

implementation Ord Rational where
  compare = rationalCompare

rationalAddition : Rational -> Rational -> Rational
rationalAddition (MkFreeRational num1 den1) (MkFreeRational num2 den2) = MkFreeRational
  (num1 * (num den2) + num2 * (num den1)) (productOfNonZeroIsNonZero den1 den2)
  
[additiveRationalSemigroup] Semigroup Rational where
  (<+>) = rationalAddition
  
-- the additive monoid is actually unlawful
-- because, in Rational, 0/m + 0/n = 0/(m * n)
-- so the identity laws do not hold
[additiveRationalMonoid] Monoid Rational using additiveRationalSemigroup where
  neutral = intAsRational 0
  
rationalOpposite : Rational -> Rational
rationalOpposite (MkFreeRational num1 den1) = MkFreeRational (-num1) den1

[additiveRationalGroup] Group Rational using additiveRationalMonoid where
  inverse = rationalOpposite
  
[additiveRationalAbelianGroup] AbelianGroup Rational using additiveRationalGroup where

rationalMultiplication : Rational -> Rational -> Rational
rationalMultiplication (MkFreeRational num1 den1) (MkFreeRational num2 den2) =
  MkFreeRational (num1 * num2) (productOfNonZeroIsNonZero den1 den2)
  
[multiplicativeRationalSemigroup] Semigroup Rational where
  (<+>) = rationalMultiplication
  
[multiplicativeRationalMonoid] Monoid Rational using multiplicativeRationalSemigroup where
  neutral = intAsRational 1
  
[rationalRing] Ring Rational using additiveRationalAbelianGroup where
  (<.>) = rationalMultiplication
  
[rationalRingWithUnity] RingWithUnity Rational using rationalRing where
  unity = intAsRational 1
  
IsNonZero : Rational -> Type
IsNonZero (MkFreeRational 0 den) = Void
IsNonZero a                      = Not (num a = 0)
  
rationalReciprocal : (a : Rational) -> {auto isNonZero : IsNonZero a} -> Rational
rationalReciprocal (MkFreeRational num1 den1) {isNonZero} = MkFreeRational (num den1) den
  where
    den = MkNonZeroInt num1 (\num1IsZero => replace {P=\n => IsNonZero (MkFreeRational n den1)} num1IsZero isNonZero)
    
-- the fact that the additive monoid in unlawful forbids us to define a field instance
-- because we have more that one zero