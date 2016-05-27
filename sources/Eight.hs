{-# LANGUAGE OverloadedLabels, DataKinds, UndecidableInstances, PolyKinds #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fprint-explicit-kinds -fprint-potential-instances #-}
{-|

see <https://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/OverloadedLabels
OverloadedLabels>

-}
module Eight where
import Data.Vinyl
import Data.Proxy
import GHC.Exts
import GHC.TypeLits
import Data.Kind
import GHC.OverloadedLabels (IsLabel(..))

{-

stack build && stack exec -- eight-example

• Ambiguous type variable ‘a1’ arising from the overloaded label ‘#y’
   prevents the constraint ‘(RElem
                               '("y", a1)
                               '['("y", Int)]
                               (Data.Vinyl.TypeLevel.RIndex
                                  '("y", a1) '['("y", Int)]))’ from being solved.

must pick first field whose key matches the label, without specifying the value


-}
main = do
  print "Eight"
  print $ point
  print $ #x point
  -- print $ #y point

x = Proxy :: Proxy ("x" ::: Int)
y = Proxy :: Proxy ("y" ::: Int)

nil :: forall (f :: k -> *). Rec f '[]
nil = RNil

-- proxy s?
(-:)
 :: forall (s::Symbol) (a::Type) proxy. (KnownSymbol s)
 => proxy '(s,a) -> a -> ElField '(s,a)
_ -: a = Field a

infix 8 -: -- more tightly than :&

type P = Proxy
-- type (s ::: a) = ElField '(s,a)
type (s ::: a) = '(s,a)

type Point2D =
  [ '("x",Int)
  , '("y",Int)
  ]

point
  = x-: 1
 :& y-: 2
 :& nil
 :: Record Point2D

type Record = Rec ElField

instance ('(s,a) ∈ fields) => IsLabel s (Record fields -> a) where -- UndecidableInstances
 fromLabel _ = getField . rget (Proxy :: Proxy '(s,a))
