{-# LANGUAGE OverloadedLabels, DataKinds, UndecidableInstances, PolyKinds, TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
{-# OPTIONS_GHC -fprint-explicit-kinds -fprint-potential-instances #-}
{-|

see <https://ghc.haskell.org/trac/ghc/wiki/Records/OverloadedRecordFields/OverloadedLabels
OverloadedLabels>

-}
module Eight where
import Data.Vinyl
import Data.Vinyl.TypeLevel
import Data.Proxy
import GHC.Exts
import GHC.TypeLits hiding (Nat)
import Data.Kind
import GHC.OverloadedLabels (IsLabel(..))

{-

stack build && stack exec -- eight-example


1.

• Ambiguous type variable ‘a1’ arising from the overloaded label ‘#y’
   prevents the constraint ‘(RElem
                               '("y", a1)
                               '['("y", Int)]
                               (Data.Vinyl.TypeLevel.RIndex
                                  '("y", a1) '['("y", Int)]))’ from being solved.

i.e. 'a' must depend only on 's'. a functional dependency {{ s, field -> a }}
e.g. {{ Int ~ RFind "x" [ ("x",Int), ("y",Int) ] }}
pick first field whose key matches the label, without specifying the value
type-level {{ Map.lookup }}



2.

• Could not deduce (RElem
                       '(s, a) fields (Data.Vinyl.TypeLevel.RIndex '(s, a) fields))
     arising from a use of ‘rget’

relate RFind to RElem

{{ a ~ RFind s fields }}  ==>  {{ RElem '(s,a) fields (RIndex '(s, a) fields }}



3.


-}
main = do
  print "Eight"
  print $ point
  print $ #x point
  print $ #y point
  --
  -- print $ p2
  -- print $ #a p2

  print $ p3
  -- print $ (#a p3 :: Record ['("a",String), '("b",Char)])
  print $ #a p3

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

type F = ElField

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

-- p2
--   = #a "a"
--  :& #b 'b'
--  :& nil

p3
   = field @"a" "a"
  :& Field @"b" 'b'
  :& nil


-- type family RFind (s :: Symbol) (fields :: [(Symbol,Type)]) :: Type where
--   RFind s ('(s,a) ': fields) = a
--   RFind s ('(_,a) ': fields) = RFind s fields

-- type family RFind (s :: Symbol) (fields :: [(Symbol,Type)]) :: (Type,Nat) where
--   RFind s ('(s,a) ': fields) i = '(a,i)
--   RFind s ('(_,a) ': fields) i = RFind s fields (S i)

type family RFind (s :: Symbol) (fields :: [(Symbol,Type)]) :: (Type,Nat) where
  RFind s ('(s,a) ': fields) = '(a,Z)
  RFind s ('(_,a) ': fields) = Second S (RFind s fields)

type family Second (f :: (b -> c)) (pair :: (a,b)) :: (a,c) where
  Second f '(a,b) = '(a, f b)

-- instance ('(s,a) ∈ fields) => IsLabel s (Record fields -> a) where -- UndecidableInstances
--  fromLabel _ = getField . rget (Proxy :: Proxy '(s,a))
--
-- instance (a ~ RFind s fields) => IsLabel s (Record fields -> a) where -- UndecidableInstances
--  fromLabel _ = getField . rget (Proxy :: Proxy '(s,a))

instance -- UndecidableInstances
 ( '(a,i) ~ RFind s fields
 , RElem '(s,a) fields i
 ) =>

 IsLabel s (Record fields -> a)
 where

 fromLabel _ = getField . rget (Proxy :: Proxy '(s,a))

-- field :: proxy '(s,a) -> Field '(s,a)
-- field _ = Field
--
-- field
--  :: forall s a proxy. (KnownSymbol s)
--  => proxy s -> a -> ElField '(s,a)
-- field _ = Field

field
 :: forall s a proxy. (KnownSymbol s)
 => a
 -> ElField '(s,a)
field = Field

{- |

@
#x 1
@

is a cleaner

@
'Field' @"x" 1
@

or

@
'field' (Proxy :: Proxy "x") 1
@

-}
-- instance (KnownSymbol s) => IsLabel s (a -> ElField '(s,a)) where
--
--  fromLabel _ = Field
