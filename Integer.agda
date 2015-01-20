open import Prelude

module Integer where

  data Int : Set where
    +_     : Nat → Int
    -[1+_] : Nat → Int

  -_ : Nat → Int
  - zero  = + zero
  - suc x = -[1+ x ]

  pattern +5 = + 5
  pattern +4 = + 4
  pattern +3 = + 3
  pattern +2 = + 2
  pattern +1 = + 1
  pattern +0 = + 0
  pattern -1 = -[1+ 0 ]
  pattern -2 = -[1+ 1 ]
  pattern -3 = -[1+ 2 ]
  pattern -4 = -[1+ 3 ]
  pattern -5 = -[1+ 4 ]

  _+I_ : Int → Int → Int
  (  + zero  ) +I          y   = y
  (  + suc x ) +I (  +     y ) = + (suc x + y)
  (  + suc x ) +I -[1+ zero  ] = + x
  (  + suc x ) +I -[1+ suc y ] = + x +I -[1+ y ]
  -[1+     x ] +I (  + zero  ) = -[1+ x ]
  -[1+ zero  ] +I (  + suc y ) = + y
  -[1+ suc x ] +I (  + suc y ) = -[1+ x ] +I + y
  -[1+     x ] +I -[1+     y ] = -[1+ suc x + y ]
