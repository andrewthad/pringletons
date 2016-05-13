 {-# LANGUAGE TemplateHaskell #-}
 {-# LANGUAGE KindSignatures #-}
 {-# LANGUAGE ScopedTypeVariables #-}
 {-# LANGUAGE DataKinds #-}
 {-# LANGUAGE TypeFamilies #-}
 {-# LANGUAGE GADTs #-}
 {-# LANGUAGE FlexibleContexts #-}
import Data.Singletons
import Data.Singletons.TH
import Data.Case.Enumerate

data MyType = MyInt | MyBool | MyChar

$(genSingletons [''MyType])

type family Interpret m where
  Interpret 'MyInt  = Int
  Interpret 'MyChar = Char
  Interpret 'MyBool = Bool

newtype MyValue x = MyValue { getMyValue :: Interpret x }

-- This is how you could define the function by
-- hand. This is no fun because every time you universe
-- changes, you must rewrite this pattern match.
myEq1 :: Sing a -> MyValue a -> MyValue a -> Bool
myEq1 s (MyValue a) (MyValue b) = 
  case s of
    SMyInt  -> a == b
    SMyChar -> a == b
    SMyBool -> a == b

-- This is an alternative that requires FlexibleContexts. I
-- do not like this either. FlexibleContexts is an extension
-- that is almost always avoidable, and it makes using this
-- function inside other function more difficult, since 
-- the constraint gets propogated. In addition, there's the
-- issue that the constrant is obvious. In other words, in 
-- non valid haskell syntax, we know that:
--
--   (forall (a :: MyType). Eq (Interpret a))
--
-- Ed Kmett's `constraints` package has a `Forall` module
-- that captures this notion, but I do not like it.
myEq2 :: (Eq (Interpret a)) => MyValue a -> MyValue a -> Bool
myEq2 (MyValue a) (MyValue b) = a == b

-- Finally, a TH solution that generates something equivalent
-- to `myEq1`. This is ideal (except for using metaprogramming,
-- but whatevs):
myEq3 :: Sing a -> MyValue a -> MyValue a -> Bool
myEq3 x (MyValue a) (MyValue b) = $(enumerateConstructors 'x ''MyType =<< [|a == b|])

main :: IO ()
main = putStrLn "Hey"

