module OddOddEven where

mutual
  data Even : Set where
    zeroE : Even
    succE : Odd -> Even
  data Odd : Set where
    succO : Even -> Odd

_odd+_ : Odd -> Odd -> Even
succO zeroE     odd+ n               = succE n
n               odd+ succO zeroE     = succE n
succO (succE n) odd+ succO (succE m) = succE (succO (succE (succO (n odd+ m))))
