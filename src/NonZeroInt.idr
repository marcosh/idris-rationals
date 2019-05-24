module NonZeroInt

%access public export
%default total
%auto_implicits off

record NonZeroInt where
  constructor MkNonZeroInt
  num : Int
  nonZero : Not (num = 0)

postulate
zeroProductProperty : (a, b : Int) -> a * b = 0 -> Either (a = 0) (b = 0)
  
productOfNonZeroIsNonZero : NonZeroInt -> NonZeroInt -> NonZeroInt
productOfNonZeroIsNonZero (MkNonZeroInt num1 nonZero1) (MkNonZeroInt num2 nonZero2) = MkNonZeroInt (num1 * num2) prf
  where
    prf = \prodIsZero => case zeroProductProperty num1 num2 prodIsZero of
      Left  aIsZero => nonZero1 aIsZero
      Right bIsZero => nonZero2 bIsZero
