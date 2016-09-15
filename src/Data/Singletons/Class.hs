{-# LANGUAGE FlexibleContexts #-}

module Data.Singletons.Class
  (
  -- * Singleton Classes
  -- $singletonClasses
    EqSing1(..)
  , EqSing2(..)
  , OrdSing1(..)
  , OrdSing2(..)
  , ShowSing2(..)
  , ReadSing2(..)
  , HashableSing1(..)
  , HashableSing2(..)
  , ToJSONSing1(..)
  , ToJSONSing2(..)
  , FromJSONSing1(..)
  , FromJSONSing2(..)
  -- * Kind classes
  -- $kindClasses
  , ShowKind(..)
  , ReadKind(..)
  , HashableKind(..)
  , ToJSONKind(..)
  , FromJSONKind(..)
  , ToJSONKeyKind(..)
  , FromJSONKeyKind(..)
  -- * Data types
  , Applied1(..)
  , Applied2(..)
  , Applied3(..)
  , SomeSingWith1(..)
  , SomeSingWith1'
  , SomeSingWith2(..)
  , SomeSingWith2'
  , SingWith1(..)
  , ClassySomeSing(..)
  -- * Classes for Applied
  -- $appliedClasses
  , EqApplied1(..)
  , HashableApplied1(..)
  , ToJSONApplied1(..)
  , FromJSONApplied1(..)
  -- * Functions
  , showKind
  , readMaybeKind
  , eqSome
  , compareSome
  ) where

import Data.Hashable
import Data.Maybe
import Data.Singletons
import Data.Singletons.Prelude
import Data.Singletons.Decide
import Data.Text (Text)
import Data.Functor.Identity
import Text.Read.Lex (Lexeme(Ident))
import Text.Read (readMaybe,readPrec,ReadPrec,lexP,parens)
import Text.ParserCombinators.ReadPrec (readPrec_to_S, prec, step)
import Text.Show (showChar, showString, showParen)
import qualified Data.Text as Text
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.Types as Aeson
import Data.Type.Equality
import Data.Aeson (FromJSON(..),ToJSON(..))
import Data.Proxy
import Control.Arrow (first)
import qualified Data.Vector as Vector
import Data.Function ((&))

{- $singletonClasses

 These are singleton variants of the commonly used classes from @base@,
 @hashable@, and @aeson@. These variants work on higher-kinded types instead
 of on ground types. For example, if you wrote the following:

 > data MyType = MyInt | MyBool | MyChar
 > $(genSingletons [''MyType])
 > type family Interpret m where
 >   Interpret 'MyInt  = Int
 >   Interpret 'MyChar = Char
 >   Interpret 'MyBool = Bool
 > newtype MyValue x = MyValue { getMyValue :: Interpret x }

 You could then write @MyValue@ instances for all of the classes that in this
 module that end in @Sing1@. For example:

 > instance EqSing1 MyValue where
 >   eqSing1 x a b = case x of
 >     SMyInt  -> a == b
 >     SMyChar -> a == b
 >     SMyBool -> a == b

 For our example @MyValue@ type, the @EqSing1@ instance is trivial. We simply
 pattern match on the singleton and then do the same thing in each case. This
 kind of pattern matching ends up happening any time our universe
 interpreter maps to types that all have @Eq@ instances. Since writing this
 out is tedious, we can instead use a template haskell function provided in
 the @Data.Case.Enumerate@ module:

 > instance EqSing1 MyValue where
 >   eqSing1 x a b $(enumerateConstructors 'x ''MyValue =<< [|a == b|])

 Instances for the other classes here can be written similarly.

-}

class EqSing1 f where
  eqSing1 :: Sing a -> f a -> f a -> Bool

class EqSing2 f where
  eqSing2 :: Sing a -> Sing b -> f a b -> f a b -> Bool

class EqSing1 f => OrdSing1 f where
  compareSing1 :: Sing a -> f a -> f a -> Ordering

class EqSing2 f => OrdSing2 f where
  compareSing2 :: Sing a -> Sing b -> f a b -> f a b -> Ordering

class ShowSing2 f where
  showsPrecSing2 :: Int -> Sing a -> Sing b -> f a b -> ShowS

class ReadSing2 f where
  readPrecSing2 :: Sing a -> Sing b -> ReadPrec (f a b)

class HashableSing1 f where
  hashWithSaltSing1 :: Sing a -> Int -> f a -> Int

class HashableSing2 f where
  hashWithSaltSing2 :: Sing a -> Sing b -> Int -> f a b -> Int

class ToJSONSing1 f where
  toJSONSing1 :: Sing a -> f a -> Aeson.Value

class ToJSONSing2 f where
  toJSONSing2 :: Sing a -> Sing b -> f a b -> Aeson.Value

class FromJSONSing1 f where
  parseJSONSing1 :: Sing a -> Aeson.Value -> Aeson.Parser (f a)

class FromJSONSing2 f where
  parseJSONSing2 :: Sing a -> Sing b -> Aeson.Value -> Aeson.Parser (f a b)

{- $kindClasses

 These are kind classes. They express that something is true for all
 singletons of a particular kind. Note that these are different from the
 kind classes provided in the @singletons@ library itself. The methods
 in those classes ('SOrd','SEnum',etc.) work entirely on singletons. Here,
 the methods also work with normal data types.

 Notice that classes like @EqKind@ and @OrdKind@ have been omitted from
 this library. The reason is that that functions that would be provided by
 these can be trivially recovered by demoting the results of methods in 'SEq'
 and 'SOrd'.

 These methods in these classes all have defaults that involve demoting the
 singleton and using the corresponding method from the normal typeclass.
-}

class (kproxy ~ 'KProxy) => ShowKind (kproxy :: KProxy a) where
  showsPrecKind :: Int -> Sing (x :: a) -> ShowS
  default showsPrecKind :: (SingKind kproxy, Show (DemoteRep kproxy)) => Int -> Sing (x :: a) -> ShowS
  showsPrecKind i s xs = showsPrec i (fromSing s) xs

class (kproxy ~ 'KProxy) => ReadKind (kproxy :: KProxy a) where
  readPrecKind :: ReadPrec (SomeSing kproxy)
  default readPrecKind :: (SingKind kproxy, Read (DemoteRep kproxy)) => ReadPrec (SomeSing kproxy)
  readPrecKind = fmap toSing readPrec
  -- readsPrecKind :: Int -> ReadS (SomeSing kproxy)
  -- default readsPrecKind :: (SingKind kproxy, Read (DemoteRep kproxy)) => Int -> ReadS (SomeSing kproxy)
  -- readsPrecKind i s = map (first toSing) (readsPrec i s)

class (kproxy ~ 'KProxy) => HashableKind (kproxy :: KProxy a) where
  hashWithSaltKind :: Int -> Sing (x :: a) -> Int
  default hashWithSaltKind :: (SingKind kproxy, Hashable (DemoteRep kproxy)) => Int -> Sing (x :: a) -> Int
  hashWithSaltKind i s = hashWithSalt i (fromSing s)

class (kproxy ~ 'KProxy) => ToJSONKind (kproxy :: KProxy a) where
  toJSONKind :: Sing (x :: a) -> Aeson.Value
  default toJSONKind :: ShowKind kproxy => Sing (x :: a) -> Aeson.Value
  toJSONKind s = Aeson.String (Text.pack (showKind s))

class (kproxy ~ 'KProxy) => FromJSONKind (kproxy :: KProxy a) where
  parseJSONKind :: Aeson.Value -> Aeson.Parser (SomeSing kproxy)
  default parseJSONKind :: ReadKind kproxy => Aeson.Value -> Aeson.Parser (SomeSing kproxy)
  parseJSONKind (Aeson.String t) = let s = Text.unpack t in
    case readMaybeKind s of
      Nothing -> fail ("Could not parse singleton from: " ++ s)
      Just a -> return a

class (kproxy ~ 'KProxy) => ToJSONKeyKind (kproxy :: KProxy a) where
  toJSONKeyKind :: Sing (x :: a) -> Text
  default toJSONKeyKind :: ShowKind kproxy => Sing (x :: a) -> Text
  toJSONKeyKind s = Text.pack (showKind s)

class (kproxy ~ 'KProxy) => FromJSONKeyKind (kproxy :: KProxy a) where
  parseJSONKeyKind :: Text -> Aeson.Parser (SomeSing kproxy)
  default parseJSONKeyKind :: ReadKind kproxy => Text -> Aeson.Parser (SomeSing kproxy)
  parseJSONKeyKind t = let s = Text.unpack t in
    case readMaybeKind s of
      Nothing -> fail ("Could not parse key: " ++ s)
      Just a -> return a

------------------------
-- Data Types
------------------------
newtype Applied1 (f :: TyFun k * -> *) (a :: k) =
  Applied1 { getApplied1 :: Apply f a }
  deriving (Eq,Ord,Read,Show,Hashable,ToJSON,FromJSON)

newtype Applied2 (f :: TyFun k (TyFun j * -> *) -> *) (a :: k) (b :: j) =
  Applied2 { getApplied2 :: Apply (Apply f a) b }

newtype Applied3 (f :: TyFun k (TyFun j (TyFun l * -> *) -> *) -> *) (a :: k) (b :: j) (c :: l) =
  Applied3 { getApplied3 :: Apply (Apply (Apply f a) b) c }

data SingWith1 (kproxy :: KProxy k) (f :: k -> *) (a :: k) where
  SingWith1 :: Sing a -> f a -> SingWith1 'KProxy f a

data SomeSingWith1 (kproxy :: KProxy k) (f :: k -> *) where
  SomeSingWith1 :: Sing a -> f a -> SomeSingWith1 'KProxy f

type SomeSingWith1' = SomeSingWith1 'KProxy

data SomeSingWith2 (kproxy1 :: KProxy k) (kproxy2 :: KProxy j) (f :: k -> j -> *) where
  SomeSingWith2 :: Sing a -> Sing b -> f a b -> SomeSingWith2 'KProxy 'KProxy f

type SomeSingWith2' = SomeSingWith2 'KProxy 'KProxy

{- $appliedClasses

 These are additional classes used to provide instances for 'Applied1'.
 If you have a defunctionalized typeclass that provides produces types
 in the category hask, you can use this. Instances will often look like
 this:

 > data Thing = ...
 > type family ToType (x :: Thing) :: * where ...
 > instance EqApplied1 ToTypeSym0 where
 >   eqApplied1 _ x (Applied a) (Applied b) = $(enumerateConstructors 'x ''Thing =<< [|a == b|])

-}
class EqApplied1 (f :: TyFun k * -> *) where
  eqApplied1 :: proxy f -> Sing a -> Apply f a -> Apply f a -> Bool

class HashableApplied1 (f :: TyFun k * -> *) where
  hashWithSaltApplied1 :: proxy f -> Sing a -> Int -> Apply f a -> Int

class ToJSONApplied1 (f :: TyFun k * -> *) where
  toJSONApplied1 :: proxy f -> Sing a -> Apply f a -> Aeson.Value

class FromJSONApplied1 (f :: TyFun k * -> *) where
  parseJSONApplied1 :: proxy f -> Sing a -> Aeson.Value -> Aeson.Parser (Apply f a)


------------------------
-- A bunch of instances
------------------------

instance EqApplied1 f => EqSing1 (Applied1 f) where
  eqSing1 s (Applied1 a) (Applied1 b) = eqApplied1 (Proxy :: Proxy f) s a b

instance ToJSONApplied1 f => ToJSONSing1 (Applied1 f) where
  toJSONSing1 s (Applied1 a) = toJSONApplied1 (Proxy :: Proxy f) s a

instance FromJSONApplied1 f => FromJSONSing1 (Applied1 f) where
  parseJSONSing1 s v = fmap Applied1 (parseJSONApplied1 (Proxy :: Proxy f) s v)

instance HashableApplied1 f => HashableSing1 (Applied1 f) where
  hashWithSaltSing1 s i (Applied1 a) = hashWithSaltApplied1 (Proxy :: Proxy f) s i a

instance (EqSing1 f, SDecide kproxy) => Eq (SomeSingWith1 kproxy f) where
  SomeSingWith1 s1 v1 == SomeSingWith1 s2 v2 =
    case testEquality s1 s2 of
      Nothing -> False
      Just Refl -> eqSing1 s1 v1 v2

instance (ShowKind kproxy1, ShowKind kproxy2, ShowSing2 f) => Show (SomeSingWith2 kproxy1 kproxy2 f) where
  showsPrec i (SomeSingWith2 s1 s2 f) =
    showString "SomeSingWith2 " . showParen True
      ( showsPrecKind 11 s1
      . showChar ' '
      . showsPrecKind 11 s2
      . showChar ' '
      . showsPrecSing2 11 s1 s2 f
      )

instance (ReadKind kproxy1, ReadKind kproxy2, ReadSing2 f) => Read (SomeSingWith2 kproxy1 kproxy2 f) where
  readPrec = parens $ prec 10 $ do
    Ident "SomeSingWith2" <- lexP
    SomeSing s1 <- step readPrecKind
    SomeSing s2 <- step readPrecKind
    f <- step (readPrecSing2 s1 s2)
    return (SomeSingWith2 s1 s2 f)


instance (SDecide kproxy1, SDecide kproxy2, EqSing2 f) => Eq (SomeSingWith2 kproxy1 kproxy2 f) where
  SomeSingWith2 s1 s2 a == SomeSingWith2 t1 t2 b = fromMaybe False $ do
    Refl <- testEquality s1 t1
    Refl <- testEquality s2 t2
    return $ eqSing2 s1 s2 a b

instance (ToJSONKind kproxy1, ToJSONKind kproxy2, ToJSONSing2 f) => ToJSON (SomeSingWith2 kproxy1 kproxy2 f) where
  toJSON (SomeSingWith2 s1 s2 v) =
    toJSON [toJSONKind s1, toJSONKind s2, toJSONSing2 s1 s2 v]

instance (FromJSONKind kproxy1, FromJSONKind kproxy2, FromJSONSing2 f) => FromJSON (SomeSingWith2 kproxy1 kproxy2 f) where
  parseJSON (Aeson.Array xs) = case Vector.toList xs of
    [v1,v2,v] -> do
      SomeSing s1 <- parseJSONKind v1
      SomeSing s2 <- parseJSONKind v2
      a <- parseJSONSing2 s1 s2 v
      return (SomeSingWith2 s1 s2 a)
    _ -> fail "SomeSingWith2: expected Array of three elements"
  parseJSON _ = mempty

instance (HashableKind kproxy1, HashableSing1 f) => Hashable (SomeSingWith1 kproxy1 f) where
  hashWithSalt i (SomeSingWith1 s v) = i
    & flip hashWithSaltKind s
    & flip (hashWithSaltSing1 s) v

showKind :: forall (kproxy :: KProxy k) (a :: k). ShowKind kproxy => Sing a -> String
showKind x = showsPrecKind 0 x ""

readsPrecKind :: ReadKind kproxy => Int -> ReadS (SomeSing kproxy)
readsPrecKind = readPrec_to_S readPrecKind

readMaybeKind :: ReadKind kproxy => String -> Maybe (SomeSing kproxy)
readMaybeKind s = listToMaybe
  $ mapMaybe (\(a,x) -> if null x then Just a else Nothing)
  $ readsPrecKind 0 s

-- | Helper function to demote an equality check. It would be nice if
--   this could be added as an 'Eq' instance for 'SomeSing', but it
--   would required collapsing a lot of the modules in 'singletons'
--   to prevent cyclic imports. Or it could be provided as an orphan
--   instance.
eqSome :: SEq kproxy => SomeSing kproxy -> SomeSing kproxy -> Bool
eqSome (SomeSing a) (SomeSing b) = fromSing (a %:== b)

-- | Helper function to demote a comparison
compareSome :: SOrd kproxy => SomeSing kproxy -> SomeSing kproxy -> Ordering
compareSome (SomeSing a) (SomeSing b) = fromSing (sCompare a b)

-- | This is a wrapper for 'SomeSing' that provides common typeclass instances
--   for it. This can be helpful when you want to use @Data.Set@ with 'SomeSing'.
newtype ClassySomeSing kproxy = ClassySomeSing { getClassySomeSing :: SomeSing kproxy }

instance SEq kproxy => Eq (ClassySomeSing kproxy) where
  ClassySomeSing a == ClassySomeSing b = eqSome a b

instance SOrd kproxy => Ord (ClassySomeSing kproxy) where
  compare (ClassySomeSing a) (ClassySomeSing b) = compareSome a b



