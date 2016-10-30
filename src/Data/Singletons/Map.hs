{-# LANGUAGE TypeInType #-}

{-| This is a dependent version of the @Data.Map@ module from @containers@.

    This module was largely copied from the @dependent-map@ package.
-}
module Data.Singletons.Map where

import Data.Singletons
import Data.Singletons.Decide
import Data.Singletons.Prelude
import Data.Type.Equality
import Data.Typeable
import Data.Singletons.Class
import Data.Maybe
import Prelude hiding (null, lookup)
import qualified Data.HashMap.Strict as HashMap
import Data.Aeson
import Data.Aeson.Types (Parser)
import Data.Text (Text)
import Data.Hashable
import Data.Vinyl.Core (Rec(..))
import Data.Kind (Type)

data SingMap (k :: Type) (f :: k -> Type) where
    Tip :: SingMap k f
    Bin :: {- sz    -} !Int
        -> {- key   -} !(Sing v)
        -> {- value -} !(f v)
        -> {- left  -} !(SingMap k f)
        -> {- right -} !(SingMap k f)
        -> SingMap k f

type family SingMap' (f :: k -> Type) :: Type where
  SingMap' (f :: k -> Type) = SingMap k f


instance (SEq k, SDecide k, EqSing1 f) => Eq (SingMap k f) where
  t1 == t2 = (size t1 == size t2) && (toAscList t1 == toAscList t2)

instance (HashableKind k, HashableSing1 f) => Hashable (SingMap k f) where
  hashWithSalt i m = hashWithSalt i (toAscList m)

instance (ToJSONKeyKind k, ToJSONSing1 f) => ToJSON (SingMap k f) where
  toJSON = Object . foldrWithKey (\s f -> HashMap.insert (toJSONKeyKind s) (toJSONSing1 s f)) HashMap.empty

instance (SOrd k, SDecide k, FromJSONKeyKind k, FromJSONSing1 f) => FromJSON (SingMap k f) where
  parseJSON = withObject "SingMap k a" $ fmap fromList . mapM parseSingWith . HashMap.toList
    where
    parseSingWith :: (Text,Value) -> Parser (SomeSingWith1 k f)
    parseSingWith (t,v) = do
      SomeSing s :: SomeSing k  <- parseJSONKeyKind t
      pv <- parseJSONSing1 s v
      return (SomeSingWith1 s pv)



{--------------------------------------------------------------------
  Construction
--------------------------------------------------------------------}

-- | /O(1)/. The empty map.
--
-- > empty      == fromList []
-- > size empty == 0
empty :: SingMap k f
empty = Tip

-- | /O(1)/. A map with a single element.
--
-- > singleton 1 'a'        == fromList [(1, 'a')]
-- > size (singleton 1 'a') == 1
singleton :: Sing v -> f v -> SingMap k f
singleton k x = Bin 1 k x Tip Tip

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(1)/. Is the map empty?
null :: SingMap k f -> Bool
null Tip    = True
null Bin{}  = False

-- | /O(1)/. The number of elements in the map.
size :: SingMap k f -> Int
size Tip                = 0
size (Bin n _ _ _ _)    = n

-- | /O(log n)/. Lookup the value at a key in the map.
--
-- The function will return the corresponding value as @('Just' value)@,
-- or 'Nothing' if the key isn't in the map.
lookup :: forall k f v. (SOrd k, SDecide k) => Sing v -> SingMap k f -> Maybe (f v)
lookup k = k `seq` go
  where
  go :: SingMap k f -> Maybe (f v)
  go Tip = Nothing
  go (Bin _ kx x l r) =
    case sCompare k kx of
      SLT -> go l
      SGT -> go r
      SEQ -> case testEquality k kx of
        Nothing -> error "lookup: inconsistent SOrd and SDecide instances"
        Just Refl -> Just x

lookupAssoc :: forall k f v. (SOrd k, SDecide k) => SomeSing k -> SingMap k f -> Maybe (SomeSingWith1 k f)
lookupAssoc (SomeSing k) = k `seq` go
  where
  go :: SingMap k f -> Maybe (SomeSingWith1 k f)
  go Tip = Nothing
  go (Bin _ kx x l r) =
    case sCompare k kx of
      SLT -> go l
      SGT -> go r
      SEQ -> case testEquality k kx of
        Nothing -> error "lookupAssoc: inconsistent SOrd and SDecide instances"
        Just Refl -> Just (SomeSingWith1 kx x)
{--------------------------------------------------------------------
  Utility functions that maintain the balance properties of the tree.
  All constructors assume that all values in [l] < [k] and all values
  in [r] > [k], and that [l] and [r] are valid trees.

  In order of sophistication:
    [Bin sz k x l r]  The type constructor.
    [bin k x l r]     Maintains the correct size, assumes that both [l]
                      and [r] are balanced with respect to each other.
    [balance k x l r] Restores the balance and size.
                      Assumes that the original tree was balanced and
                      that [l] or [r] has changed by at most one element.
    [combine k x l r] Restores balance and size.

  Furthermore, we can construct a new tree from two trees. Both operations
  assume that all values in [l] < all values in [r] and that [l] and [r]
  are valid:
    [glue l r]        Glues [l] and [r] together. Assumes that [l] and
                      [r] are already balanced with respect to each other.
    [merge l r]       Merges two trees and restores balance.

  Note: in contrast to Adam's paper, we use (<=) comparisons instead
  of (<) comparisons in [combine], [merge] and [balance].
  Quickcheck (on [difference]) showed that this was necessary in order
  to maintain the invariants. It is quite unsatisfactory that I haven't
  been able to find out why this is actually the case! Fortunately, it
  doesn't hurt to be a bit more conservative.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  Combine
--------------------------------------------------------------------}
combine :: (SOrd k, SDecide k) => Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
combine kx x Tip r  = insertMin kx x r
combine kx x l Tip  = insertMax kx x l
combine kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL <= sizeR  = balance kz z (combine kx x l lz) rz
  | delta*sizeR <= sizeL  = balance ky y ly (combine kx x ry r)
  | otherwise             = bin kx x l r


-- insertMin and insertMax don't perform potentially expensive comparisons.
insertMax,insertMin :: Sing v -> f v -> SingMap k f -> SingMap k f
insertMax kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y l (insertMax kx x r)

insertMin kx x t
  = case t of
      Tip -> singleton kx x
      Bin _ ky y l r
          -> balance ky y (insertMin kx x l) r

{--------------------------------------------------------------------
  [merge l r]: merges two trees.
--------------------------------------------------------------------}
merge :: SOrd k => SingMap k f -> SingMap k f -> SingMap k f
merge Tip r   = r
merge l Tip   = l
merge l@(Bin sizeL kx x lx rx) r@(Bin sizeR ky y ly ry)
  | delta*sizeL <= sizeR = balance ky y (merge l ly) ry
  | delta*sizeR <= sizeL = balance kx x lx (merge rx r)
  | otherwise            = glue l r

{--------------------------------------------------------------------
  [glue l r]: glues two trees together.
  Assumes that [l] and [r] are already balanced with respect to each other.
--------------------------------------------------------------------}
glue ::  SingMap k f -> SingMap k f -> SingMap k f
glue Tip r = r
glue l Tip = l
glue l r
  | size l > size r = case deleteFindMax l of (SomeSingWith1 km m,l') -> balance km m l' r
  | otherwise       = case deleteFindMin r of (SomeSingWith1 km m,r') -> balance km m l r'

-- | /O(log n)/. Delete and find the minimal element.
--
-- > deleteFindMin (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((3,"b"), fromList[(5,"a"), (10,"c")])
-- > deleteFindMin                                            Error: can not return the minimal element of an empty map

deleteFindMin ::  SingMap k f -> (SomeSingWith1 k f, SingMap k f)
deleteFindMin t
  = case t of
      Bin _ k x Tip r -> (SomeSingWith1 k x ,r)
      Bin _ k x l r   -> let (km,l') = deleteFindMin l in (km,balance k x l' r)
      Tip             -> (error "Map.deleteFindMin: can not return the minimal element of an empty map", Tip)

-- | /O(log n)/. Delete and find the maximal element.
--
-- > deleteFindMax (fromList [(5,"a"), (3,"b"), (10,"c")]) == ((10,"c"), fromList [(3,"b"), (5,"a")])
-- > deleteFindMax empty                                      Error: can not return the maximal element of an empty map

deleteFindMax ::  SingMap k f -> (SomeSingWith1 k f, SingMap k f)
deleteFindMax t
  = case t of
      Bin _ k x l Tip -> (SomeSingWith1 k x,l)
      Bin _ k x l r   -> let (km,r') = deleteFindMax r in (km,balance k x l r')
      Tip             -> (error "Map.deleteFindMax: can not return the maximal element of an empty map", Tip)


{--------------------------------------------------------------------
  [balance l x r] balances two trees with value x.
  The sizes of the trees should balance after decreasing the
  size of one of them. (a rotation).

  [delta] is the maximal relative difference between the sizes of
          two trees, it corresponds with the [w] in Adams' paper.
  [ratio] is the ratio between an outer and inner sibling of the
          heavier subtree in an unbalanced setting. It determines
          whether a double or single rotation should be performed
          to restore balance. It is correspondes with the inverse
          of $\alpha$ in Adam's article.

  Note that:
  - [delta] should be larger than 4.646 with a [ratio] of 2.
  - [delta] should be larger than 3.745 with a [ratio] of 1.534.

  - A lower [delta] leads to a more 'perfectly' balanced tree.
  - A higher [delta] performs less rebalancing.

  - Balancing is automatic for random data and a balancing
    scheme is only necessary to avoid pathological worst cases.
    Almost any choice will do, and in practice, a rather large
    [delta] may perform better than smaller one.

  Note: in contrast to Adam's paper, we use a ratio of (at least) [2]
  to decide whether a single or double rotation is needed. Allthough
  he actually proves that this ratio is needed to maintain the
  invariants, his implementation uses an invalid ratio of [1].
--------------------------------------------------------------------}
delta,ratio :: Int
delta = 4
ratio = 2

balance :: Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
balance k x l r
  | sizeL + sizeR <= 1    = Bin sizeX k x l r
  | sizeR >= delta*sizeL  = rotateL k x l r
  | sizeL >= delta*sizeR  = rotateR k x l r
  | otherwise             = Bin sizeX k x l r
  where
    sizeL = size l
    sizeR = size r
    sizeX = sizeL + sizeR + 1

-- rotate
rotateL :: Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
rotateL k x l r@(Bin _ _ _ ly ry)
  | size ly < ratio*size ry = singleL k x l r
  | otherwise               = doubleL k x l r
rotateL _ _ _ Tip = error "rotateL Tip"

rotateR :: Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
rotateR k x l@(Bin _ _ _ ly ry) r
  | size ry < ratio*size ly = singleR k x l r
  | otherwise               = doubleR k x l r
rotateR _ _ Tip _ = error "rotateR Tip"

-- basic rotations
singleL, singleR :: Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
singleL k1 x1 t1 (Bin _ k2 x2 t2 t3)  = bin k2 x2 (bin k1 x1 t1 t2) t3
singleL _ _ _ Tip = error "singleL Tip"
singleR k1 x1 (Bin _ k2 x2 t1 t2) t3  = bin k2 x2 t1 (bin k1 x1 t2 t3)
singleR _ _ Tip _ = error "singleR Tip"

doubleL, doubleR :: Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
doubleL k1 x1 t1 (Bin _ k2 x2 (Bin _ k3 x3 t2 t3) t4) = bin k3 x3 (bin k1 x1 t1 t2) (bin k2 x2 t3 t4)
doubleL _ _ _ _ = error "doubleL"
doubleR k1 x1 (Bin _ k2 x2 t1 (Bin _ k3 x3 t2 t3)) t4 = bin k3 x3 (bin k2 x2 t1 t2) (bin k1 x1 t3 t4)
doubleR _ _ _ _ = error "doubleR"

{--------------------------------------------------------------------
  The bin constructor maintains the size of the tree
--------------------------------------------------------------------}
bin :: Sing v -> f v -> SingMap k f -> SingMap k f -> SingMap k f
bin k x l r
  = Bin (size l + size r + 1) k x l r

{--------------------------------------------------------------------
  Utility functions that return sub-ranges of the original
  tree. Some functions take a comparison function as argument to
  allow comparisons against infinite values. A function [cmplo k]
  should be read as [compare lo k].

  [trim cmplo cmphi t]  A tree that is either empty or where [cmplo k == LT]
                        and [cmphi k == GT] for the key [k] of the root.
  [filterGt cmp t]      A tree where for all keys [k]. [cmp k == LT]
  [filterLt cmp t]      A tree where for all keys [k]. [cmp k == GT]

  [split k t]           Returns two trees [l] and [r] where all keys
                        in [l] are <[k] and all keys in [r] are >[k].
  [splitLookup k t]     Just like [split] but also returns whether [k]
                        was found in the tree.
--------------------------------------------------------------------}

{--------------------------------------------------------------------
  [trim lo hi t] trims away all subtrees that surely contain no
  values between the range [lo] to [hi]. The returned tree is either
  empty or the key of the root is between @lo@ and @hi@.
--------------------------------------------------------------------}
trim :: SOrd k => (SomeSing k -> Ordering) -> (SomeSing k -> Ordering) -> SingMap k f -> SingMap k f
trim _     _     Tip = Tip
trim cmplo cmphi t@(Bin _ kx _ l r)
  = case cmplo (SomeSing kx) of
      LT -> case cmphi (SomeSing kx) of
              GT -> t
              _  -> trim cmplo cmphi l
      _  -> trim cmplo cmphi r

trimLookupLo :: (SOrd k, SDecide k) => SomeSing k -> (SomeSing k -> Ordering) -> SingMap k f -> (Maybe (SomeSingWith1 k f), SingMap k f)
trimLookupLo _  _     Tip = (Nothing,Tip)
trimLookupLo lo cmphi t@(Bin _ kx x l r)
  = case compareSome lo (SomeSing kx) of
      LT -> case cmphi (SomeSing kx) of
              GT -> (lookupAssoc lo t, t)
              _  -> trimLookupLo lo cmphi l
      GT -> trimLookupLo lo cmphi r
      EQ -> (Just (SomeSingWith1 kx x),trim (compareSome lo) cmphi r)


{--------------------------------------------------------------------
  [filterGt k t] filter all keys >[k] from tree [t]
  [filterLt k t] filter all keys <[k] from tree [t]
--------------------------------------------------------------------}
filterGt :: (SOrd k, SDecide k) => (SomeSing k -> Ordering) -> SingMap k f -> SingMap k f
filterGt cmp = go
  where
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (SomeSing kx) of
              LT -> combine kx x (go l) r
              GT -> go r
              EQ -> r

filterLt :: (SOrd k, SDecide k) => (SomeSing k -> Ordering) -> SingMap k f -> SingMap k f
filterLt cmp = go
  where
    go Tip              = Tip
    go (Bin _ kx x l r) = case cmp (SomeSing kx) of
          LT -> go l
          GT -> combine kx x l (go r)
          EQ -> l

----------------------------------------------------------------
----------------------------------------------------------------
-- Stuff that is, for some reason, in the non-internal module.
----------------------------------------------------------------
----------------------------------------------------------------

{--------------------------------------------------------------------
  Operators
--------------------------------------------------------------------}
infixl 9 !,\\ --

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
--
-- > fromList [(5,'a'), (3,'b')] ! 1    Error: element not in the map
-- > fromList [(5,'a'), (3,'b')] ! 5 == 'a'

(!) :: (SOrd k, SDecide k) => SingMap k f -> Sing v -> f v
(!) m k    = find k m

-- | Same as 'difference'.
(\\) :: (SOrd k, SDecide k) => SingMap k f -> SingMap k f -> SingMap k f
m1 \\ m2 = difference m1 m2

{--------------------------------------------------------------------
  Query
--------------------------------------------------------------------}

-- | /O(log n)/. Is the key a member of the map? See also 'notMember'.
member :: forall k f (v :: k). (SOrd k, SDecide k) => Sing v -> SingMap k f -> Bool
member k = isJust . lookup k

-- | /O(log n)/. Is the key not a member of the map? See also 'member'.
notMember :: forall k f (v :: k). (SOrd k, SDecide k) => Sing v -> SingMap k f -> Bool
notMember k m = not (member k m)

-- | /O(log n)/. Find the value at a key.
-- Calls 'error' when the element can not be found.
-- Consider using 'lookup' when elements may not be present.
find :: (SOrd k, SDecide k) => Sing v -> SingMap k f -> f v
find k m = case lookup k m of
    Nothing -> error "SingMap.find: element not in the map"
    Just v  -> v

-- | /O(log n)/. The expression @('findWithDefault' def k map)@ returns
-- the value at key @k@ or returns default value @def@
-- when the key is not in the map.
findWithDefault :: (SOrd k, SDecide k) => f v -> Sing v -> SingMap k f -> f v
findWithDefault def k m = case lookup k m of
    Nothing -> def
    Just v  -> v

{--------------------------------------------------------------------
  Insertion
--------------------------------------------------------------------}

-- | /O(log n)/. Insert a new key and value in the map.
-- If the key is already present in the map, the associated value is
-- replaced with the supplied value. 'insert' is equivalent to
-- @'insertWith' 'const'@.
insert :: forall k f v. (SOrd k, SDecide k) => Sing v -> f v -> SingMap k f -> SingMap k f
insert kx x = kx `seq` go
    where
        go :: SingMap k f -> SingMap k f
        go Tip = singleton kx x
        go (Bin sz ky y l r) = case sCompare kx ky of
            SLT -> balance ky y (go l) r
            SGT -> balance ky y l (go r)
            SEQ -> Bin sz kx x l r

-- | /O(log n)/. Insert with a function, combining new value and old value.
-- @'insertWith' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f new_value old_value@.
insertWith :: (SOrd k, SDecide k) => (f v -> f v -> f v) -> Sing v -> f v -> SingMap k f -> SingMap k f
insertWith f = insertWithKey (\_ x' y' -> f x' y')

-- | Same as 'insertWith', but the combining function is applied strictly.
-- This is often the most desirable behavior.
insertWith' :: (SOrd k, SDecide k) => (f v -> f v -> f v) -> Sing v -> f v -> SingMap k f -> SingMap k f
insertWith' f = insertWithKey' (\_ x' y' -> f x' y')

-- | /O(log n)/. Insert with a function, combining key, new value and old value.
-- @'insertWithKey' f key value mp@
-- will insert the entry @key :=> value@ into @mp@ if key does
-- not exist in the map. If the key does exist, the function will
-- insert the entry @key :=> f key new_value old_value@.
-- Note that the key passed to f is the same key passed to 'insertWithKey'.
insertWithKey :: forall k f v. (SOrd k, SDecide k) => (Sing v -> f v -> f v -> f v) -> Sing v -> f v -> SingMap k f -> SingMap k f
insertWithKey f kx x = kx `seq` go
  where
    go :: SingMap k f -> SingMap k f
    go Tip = singleton kx x
    go (Bin sy ky y l r) =
        case sCompare kx ky of
            SLT -> balance ky y (go l) r
            SGT -> balance ky y l (go r)
            SEQ -> unifyOnCompareEQ kx ky (Bin sy kx (f kx x y) l r)

-- | Same as 'insertWithKey', but the combining function is applied strictly.
insertWithKey' :: forall k f v. (SOrd k, SDecide k) => (Sing v -> f v -> f v -> f v) -> Sing v -> f v -> SingMap k f -> SingMap k f
insertWithKey' f kx x = kx `seq` go
  where
    go :: SingMap k f -> SingMap k f
    go Tip = singleton kx $! x
    go (Bin sy ky y l r) =
        case sCompare kx ky of
            SLT -> balance ky y (go l) r
            SGT -> balance ky y l (go r)
            SEQ -> unifyOnCompareEQ kx ky (let x' = f kx x y in seq x' (Bin sy kx x' l r))

-- | /O(log n)/. Combines insert operation with old value retrieval.
-- The expression (@'insertLookupWithKey' f k x map@)
-- is a pair where the first element is equal to (@'lookup' k map@)
-- and the second element equal to (@'insertWithKey' f k x map@).
insertLookupWithKey :: forall k f v. (SOrd k, SDecide k) => (Sing v -> f v -> f v -> f v) -> Sing v -> f v -> SingMap k f
                    -> (Maybe (f v), SingMap k f)
insertLookupWithKey f kx x = kx `seq` go
  where
    go :: SingMap k f -> (Maybe (f v), SingMap k f)
    go Tip = (Nothing, singleton kx x)
    go (Bin sy ky y l r) =
        case sCompare kx ky of
            SLT -> let (found, l') = go l
                  in (found, balance ky y l' r)
            SGT -> let (found, r') = go r
                  in (found, balance ky y l r')
            SEQ -> unifyOnCompareEQ kx ky (Just y, Bin sy kx (f kx x y) l r)

-- | /O(log n)/. A strict version of 'insertLookupWithKey'.
insertLookupWithKey' :: forall k f v. (SOrd k, SDecide k) => (Sing v -> f v -> f v -> f v) -> Sing v -> f v -> SingMap k f
                     -> (Maybe (f v), SingMap k f)
insertLookupWithKey' f kx x = kx `seq` go
  where
    go :: SingMap k f -> (Maybe (f v), SingMap k f)
    go Tip = x `seq` (Nothing, singleton kx x)
    go (Bin sy ky y l r) =
        case sCompare kx ky of
            SLT -> let (found, l') = go l
                  in (found, balance ky y l' r)
            SGT -> let (found, r') = go r
                  in (found, balance ky y l r')
            SEQ -> unifyOnCompareEQ kx ky (let x' = f kx x y in x' `seq` (Just y, Bin sy kx x' l r))

{--------------------------------------------------------------------
  Deletion
  [delete] is the inlined version of [deleteWith (\k x -> Nothing)]
--------------------------------------------------------------------}

-- | /O(log n)/. Delete a key and its value from the map. When the key is not
-- a member of the map, the original map is returned.
delete :: forall k f (v :: k). (SOrd k, SDecide k) => Sing v -> SingMap k f -> SingMap k f
delete k = k `seq` go
  where
    go :: SingMap k f -> SingMap k f
    go Tip = Tip
    go (Bin _ kx x l r) =
        case sCompare k kx of
            SLT -> balance kx x (go l) r
            SGT -> balance kx x l (go r)
            SEQ -> unifyOnCompareEQ k kx (glue l r)

-- | /O(log n)/. Update a value at a specific key with the result of the provided function.
-- When the key is not
-- a member of the map, the original map is returned.
adjust :: (SOrd k, SDecide k) => (f v -> f v) -> Sing v -> SingMap k f -> SingMap k f
adjust f = adjustWithKey (\_ x -> f x)

-- | /O(log n)/. Adjust a value at a specific key. When the key is not
-- a member of the map, the original map is returned.
adjustWithKey :: (SOrd k, SDecide k) => (Sing v -> f v -> f v) -> Sing v -> SingMap k f -> SingMap k f
adjustWithKey f = updateWithKey (\k' x' -> Just (f k' x'))

-- | /O(log n)/. The expression (@'update' f k map@) updates the value @x@
-- at @k@ (if it is in the map). If (@f x@) is 'Nothing', the element is
-- deleted. If it is (@'Just' y@), the key @k@ is bound to the new value @y@.
update :: (SOrd k, SDecide k) => (f v -> Maybe (f v)) -> Sing v -> SingMap k f -> SingMap k f
update f = updateWithKey (\_ x -> f x)

-- | /O(log n)/. The expression (@'updateWithKey' f k map@) updates the
-- value @x@ at @k@ (if it is in the map). If (@f k x@) is 'Nothing',
-- the element is deleted. If it is (@'Just' y@), the key @k@ is bound
-- to the new value @y@.
updateWithKey :: forall k f v. (SOrd k, SDecide k) => (Sing v -> f v -> Maybe (f v)) -> Sing v -> SingMap k f -> SingMap k f
updateWithKey f k = k `seq` go
  where
    go :: SingMap k f -> SingMap k f
    go Tip = Tip
    go (Bin sx kx x l r) =
        case sCompare k kx of
           SLT -> balance kx x (go l) r
           SGT -> balance kx x l (go r)
           SEQ -> unifyOnCompareEQ k kx $ case f kx x of
                   Just x' -> Bin sx kx x' l r
                   Nothing -> glue l r

-- | /O(log n)/. Lookup and update. See also 'updateWithKey'.
-- The function returns changed value, if it is updated.
-- Returns the original key value if the map entry is deleted.
updateLookupWithKey :: forall k f v. (SOrd k, SDecide k) => (Sing v -> f v -> Maybe (f v)) -> Sing v -> SingMap k f -> (Maybe (f v), SingMap k f)
updateLookupWithKey f k = k `seq` go
 where
   go :: SingMap k f -> (Maybe (f v), SingMap k f)
   go Tip = (Nothing,Tip)
   go (Bin sx kx x l r) =
          case sCompare k kx of
               SLT -> let (found,l') = go l in (found,balance kx x l' r)
               SGT -> let (found,r') = go r in (found,balance kx x l r')
               SEQ -> unifyOnCompareEQ k kx $ case f kx x of
                       Just x' -> (Just x',Bin sx kx x' l r)
                       Nothing -> (Just x,glue l r)

-- | /O(log n)/. The expression (@'alter' f k map@) alters the value @x@ at @k@, or absence thereof.
-- 'alter' can be used to insert, delete, or update a value in a 'Map'.
-- In short : @'lookup' k ('alter' f k m) = f ('lookup' k m)@.
alter :: forall k f v. (SOrd k, SDecide k) => (Maybe (f v) -> Maybe (f v)) -> Sing v -> SingMap k f -> SingMap k f
alter f k = k `seq` go
  where
    go :: SingMap k f -> SingMap k f
    go Tip = case f Nothing of
               Nothing -> Tip
               Just x  -> singleton k x

    go (Bin sx kx x l r) = case sCompare k kx of
               SLT -> balance kx x (go l) r
               SGT -> balance kx x l (go r)
               SEQ -> unifyOnCompareEQ k kx $ case f (Just x) of
                       Just x' -> Bin sx kx x' l r
                       Nothing -> glue l r

{--------------------------------------------------------------------
  Indexing
--------------------------------------------------------------------}

-- | /O(log n)/. Return the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map. Calls 'error' when
-- the key is not a 'member' of the map.
findIndex :: forall k f (v :: k). (SOrd k, SDecide k) => Sing v -> SingMap k f -> Int
findIndex k t
  = case lookupIndex k t of
      Nothing  -> error "Map.findIndex: element is not in the map"
      Just idx -> idx

-- | /O(log n)/. Lookup the /index/ of a key. The index is a number from
-- /0/ up to, but not including, the 'size' of the map.
lookupIndex :: forall k f (v :: k). (SOrd k, SDecide k) => Sing v -> SingMap k f -> Maybe Int
lookupIndex k = k `seq` go 0
  where
    go :: Int -> SingMap k f -> Maybe Int
    go !idx Tip  = idx `seq` Nothing
    go !idx (Bin _ kx _ l r)
      = case sCompare k kx of
          SLT -> go idx l
          SGT -> go (idx + size l + 1) r
          SEQ -> Just (idx + size l)

-- | /O(log n)/. Retrieve an element by /index/. Calls 'error' when an
-- invalid index is used.
elemAt ::  Int -> SingMap k f -> SomeSingWith1 k f
elemAt _ Tip = error "Map.elemAt: index out of range"
elemAt i (Bin _ kx x l r)
  = case compare i sizeL of
      LT -> elemAt i l
      GT -> elemAt (i-sizeL-1) r
      EQ -> SomeSingWith1 kx x
  where
    sizeL = size l

-- | /O(log n)/. Update the element at /index/. Calls 'error' when an
-- invalid index is used.
updateAt ::  (forall v. Sing v -> f v -> Maybe (f v)) -> Int -> SingMap k f -> SingMap k f
updateAt f i0 t = i0 `seq` go i0 t
 where
    go _ Tip  = error "Map.updateAt: index out of range"
    go i (Bin sx kx x l r) = case compare i sizeL of
      LT -> balance kx x (go i l) r
      GT -> balance kx x l (go (i-sizeL-1) r)
      EQ -> case f kx x of
              Just x' -> Bin sx kx x' l r
              Nothing -> glue l r
      where
        sizeL = size l

-- | /O(log n)/. Delete the element at /index/.
-- Defined as (@'deleteAt' i map = 'updateAt' (\k x -> 'Nothing') i map@).
deleteAt ::  Int -> SingMap k f -> SingMap k f
deleteAt i m
  = updateAt (\_ _ -> Nothing) i m


{--------------------------------------------------------------------
  Minimal, Maximal
--------------------------------------------------------------------}

-- | /O(log n)/. The minimal key of the map. Calls 'error' is the map is empty.
findMin ::  SingMap k f -> SomeSingWith1 k f
findMin (Bin _ kx x Tip _)  = SomeSingWith1 kx x
findMin (Bin _ _  _ l _)    = findMin l
findMin Tip                 = error "Map.findMin: empty map has no minimal element"

-- | /O(log n)/. The maximal key of the map. Calls 'error' is the map is empty.
findMax ::  SingMap k f -> SomeSingWith1 k f
findMax (Bin _ kx x _ Tip)  = SomeSingWith1 kx x
findMax (Bin _ _  _ _ r)    = findMax r
findMax Tip                 = error "Map.findMax: empty map has no maximal element"

-- | /O(log n)/. Delete the minimal key. Returns an empty map if the map is empty.
deleteMin ::  SingMap k f -> SingMap k f
deleteMin (Bin _ _  _ Tip r)  = r
deleteMin (Bin _ kx x l r)    = balance kx x (deleteMin l) r
deleteMin Tip                 = Tip

-- | /O(log n)/. Delete the maximal key. Returns an empty map if the map is empty.
deleteMax ::  SingMap k f -> SingMap k f
deleteMax (Bin _ _  _ l Tip)  = l
deleteMax (Bin _ kx x l r)    = balance kx x l (deleteMax r)
deleteMax Tip                 = Tip

-- | /O(log n)/. Update the value at the minimal key.
updateMinWithKey :: (forall v. Sing v -> f v -> Maybe (f v)) -> SingMap k f -> SingMap k f
updateMinWithKey f = go
 where
    go (Bin sx kx x Tip r) = case f kx x of
                                  Nothing -> r
                                  Just x' -> Bin sx kx x' Tip r
    go (Bin _ kx x l r)    = balance kx x (go l) r
    go Tip                 = Tip

-- | /O(log n)/. Update the value at the maximal key.
updateMaxWithKey :: (forall v. Sing v -> f v -> Maybe (f v)) -> SingMap k f -> SingMap k f
updateMaxWithKey f = go
 where
    go (Bin sx kx x l Tip) = case f kx x of
                              Nothing -> l
                              Just x' -> Bin sx kx x' l Tip
    go (Bin _ kx x l r)    = balance kx x l (go r)
    go Tip                 = Tip

-- | /O(log n)/. Retrieves the minimal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
minViewWithKey ::  SingMap k f -> Maybe (SomeSingWith1 k f, SingMap k f)
minViewWithKey Tip = Nothing
minViewWithKey x   = Just (deleteFindMin x)

-- | /O(log n)/. Retrieves the maximal (key :=> value) entry of the map, and
-- the map stripped of that element, or 'Nothing' if passed an empty map.
maxViewWithKey ::  SingMap k f -> Maybe (SomeSingWith1 k f, SingMap k f)
maxViewWithKey Tip = Nothing
maxViewWithKey x   = Just (deleteFindMax x)

{--------------------------------------------------------------------
  Union.
--------------------------------------------------------------------}

-- | The union of a list of maps:
--   (@'unions' == 'Prelude.foldl' 'union' 'empty'@).
unions :: (SOrd k, SDecide k) => [SingMap k f] -> SingMap k f
unions ts
  = foldlStrict union empty ts

-- | The union of a list of maps, with a combining operation:
--   (@'unionsWithKey' f == 'Prelude.foldl' ('unionWithKey' f) 'empty'@).
unionsWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> f v -> f v) -> [SingMap k f] -> SingMap k f
unionsWithKey f ts
  = foldlStrict (unionWithKey f) empty ts

-- | /O(n+m)/.
-- The expression (@'union' t1 t2@) takes the left-biased union of @t1@ and @t2@.
-- It prefers @t1@ when duplicate keys are encountered,
-- i.e. (@'union' == 'unionWith' 'const'@).
-- The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
union :: (SOrd k, SDecide k) => SingMap k f -> SingMap k f -> SingMap k f
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnionL (const LT) (const GT) t1 t2

-- left-biased hedge union
hedgeUnionL :: (SOrd k, SDecide k)
            => (SomeSing k -> Ordering) -> (SomeSing k -> Ordering) -> SingMap k f -> SingMap k f
            -> SingMap k f
hedgeUnionL _     _     t1 Tip
  = t1
hedgeUnionL cmplo cmphi Tip (Bin _ kx x l r)
  = combine kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnionL cmplo cmphi (Bin _ kx x l r) t2
  = combine kx x (hedgeUnionL cmplo cmpkx l (trim cmplo cmpkx t2))
              (hedgeUnionL cmpkx cmphi r (trim cmpkx cmphi t2))
  where
    cmpkx k  = compareSome (SomeSing kx) k

{--------------------------------------------------------------------
  Union with a combining function
--------------------------------------------------------------------}

-- | /O(n+m)/.
-- Union with a combining function. The implementation uses the efficient /hedge-union/ algorithm.
-- Hedge-union is more efficient on (bigset \``union`\` smallset).
unionWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> f v -> f v) -> SingMap k f -> SingMap k f -> SingMap k f
unionWithKey _ Tip t2  = t2
unionWithKey _ t1 Tip  = t1
unionWithKey f t1 t2 = hedgeUnionWithKey f (const LT) (const GT) t1 t2

hedgeUnionWithKey :: forall k f. (SOrd k, SDecide k)
                  => (forall v. Sing v -> f v -> f v -> f v)
                  -> (SomeSing k -> Ordering) -> (SomeSing k -> Ordering)
                  -> SingMap k f -> SingMap k f
                  -> SingMap k f
hedgeUnionWithKey _ _     _     t1 Tip
  = t1
hedgeUnionWithKey _ cmplo cmphi Tip (Bin _ kx x l r)
  = combine kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeUnionWithKey f cmplo cmphi (Bin _ (kx :: Sing tx) x l r) t2
  = combine kx newx (hedgeUnionWithKey f cmplo cmpkx l lt)
                 (hedgeUnionWithKey f cmpkx cmphi r gt)
  where
    cmpkx k     = compareSome (SomeSing kx) k
    lt          = trim cmplo cmpkx t2
    (found,gt)  = trimLookupLo (SomeSing kx) cmphi t2
    newx :: f tx
    newx        = case found of
                    Nothing -> x
                    Just (SomeSingWith1 ky y) -> case kx %:== ky of
                        STrue  -> unifyOnEq kx ky (f kx x y)
                        SFalse -> error "SingMap.union: inconsistent SEq instance"

{--------------------------------------------------------------------
  Difference
--------------------------------------------------------------------}

-- | /O(n+m)/. Difference of two maps.
-- Return elements of the first map not existing in the second map.
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
difference :: (SOrd k, SDecide k) => SingMap k f -> SingMap k g -> SingMap k f
difference Tip _   = Tip
difference t1 Tip  = t1
difference t1 t2   = hedgeDiff (const LT) (const GT) t1 t2

hedgeDiff :: (SOrd k, SDecide k)
          => (SomeSing k -> Ordering) -> (SomeSing k -> Ordering) -> SingMap k f -> SingMap k g
          -> SingMap k f
hedgeDiff _     _     Tip _
  = Tip
hedgeDiff cmplo cmphi (Bin _ kx x l r) Tip
  = combine kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeDiff cmplo cmphi t (Bin _ kx _ l r)
  = merge (hedgeDiff cmplo cmpkx (trim cmplo cmpkx t) l)
          (hedgeDiff cmpkx cmphi (trim cmpkx cmphi t) r)
  where
    cmpkx k = compareSome (SomeSing kx) k

-- | /O(n+m)/. Difference with a combining function. When two equal keys are
-- encountered, the combining function is applied to the key and both values.
-- If it returns 'Nothing', the element is discarded (proper set difference). If
-- it returns (@'Just' y@), the element is updated with a new value @y@.
-- The implementation uses an efficient /hedge/ algorithm comparable with /hedge-union/.
differenceWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> g v -> Maybe (f v)) -> SingMap k f -> SingMap k g -> SingMap k f
differenceWithKey _ Tip _   = Tip
differenceWithKey _ t1 Tip  = t1
differenceWithKey f t1 t2   = hedgeDiffWithKey f (const LT) (const GT) t1 t2

hedgeDiffWithKey :: (SOrd k, SDecide k)
                 => (forall v. Sing v -> f v -> g v -> Maybe (f v))
                 -> (SomeSing k -> Ordering) -> (SomeSing k -> Ordering)
                 -> SingMap k f -> SingMap k g
                 -> SingMap k f
hedgeDiffWithKey _ _     _     Tip _
  = Tip
hedgeDiffWithKey _ cmplo cmphi (Bin _ kx x l r) Tip
  = combine kx x (filterGt cmplo l) (filterLt cmphi r)
hedgeDiffWithKey f cmplo cmphi t (Bin _ kx x l r)
  = case found of
      Nothing -> merge tl tr
      Just (SomeSingWith1 ky y) ->
        case kx %:== ky of
          SFalse -> error "SingMap.difference: inconsistent SEq instance"
          STrue -> unifyOnEq kx ky $
            case f ky y x of
              Nothing -> merge tl tr
              Just z  -> combine ky z tl tr
  where
    cmpkx k     = compareSome (SomeSing kx) k
    lt          = trim cmplo cmpkx t
    (found,gt)  = trimLookupLo (SomeSing kx) cmphi t
    tl          = hedgeDiffWithKey f cmplo cmpkx lt l
    tr          = hedgeDiffWithKey f cmpkx cmphi gt r



{--------------------------------------------------------------------
  Intersection
--------------------------------------------------------------------}

-- | /O(n+m)/. Intersection of two maps.
-- Return data in the first map for the keys existing in both maps.
-- (@'intersection' m1 m2 == 'intersectionWith' 'const' m1 m2@).
intersection :: (SOrd k, SDecide k) => SingMap k f -> SingMap k f -> SingMap k f
intersection m1 m2
  = intersectionWithKey (\_ x _ -> x) m1 m2

-- | /O(n+m)/. Intersection with a combining function.
-- Intersection is more efficient on (bigset \``intersection`\` smallset).
intersectionWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> g v -> h v) -> SingMap k f -> SingMap k g -> SingMap k h
intersectionWithKey _ Tip _ = Tip
intersectionWithKey _ _ Tip = Tip
intersectionWithKey f t1@(Bin s1 k1 x1 l1 r1) t2@(Bin s2 k2 x2 l2 r2) =
   if s1 >= s2 then
      let (lt,found,gt) = splitLookupWithKey k2 t1
          tl            = intersectionWithKey f lt l2
          tr            = intersectionWithKey f gt r2
      in case found of
      Just (k,x) -> combine k (f k x x2) tl tr
      Nothing -> merge tl tr
   else let (lt,found,gt) = splitLookup k1 t2
            tl            = intersectionWithKey f l1 lt
            tr            = intersectionWithKey f r1 gt
      in case found of
      Just x -> combine k1 (f k1 x1 x) tl tr
      Nothing -> merge tl tr



-- TODO: Fix submap functions
-- {--------------------------------------------------------------------
--   Submap
-- --------------------------------------------------------------------}
-- -- | /O(n+m)/.
-- -- This function is defined as (@'isSubmapOf' = 'isSubmapOfBy' 'eqTagged')@).
-- isSubmapOf :: ((SOrd k, SDecide k) EqTag k f) => SingMap k f -> SingMap k f -> Bool
-- isSubmapOf m1 m2 = isSubmapOfBy eqTagged m1 m2
--
-- {- | /O(n+m)/.
--  The expression (@'isSubmapOfBy' f t1 t2@) returns 'True' if
--  all keys in @t1@ are in tree @t2@, and when @f@ returns 'True' when
--  applied to their respective keys and values.
-- -}
-- isSubmapOfBy :: (SOrd k, SDecide k) => (forall v. Sing v -> Sing v -> f v -> g v -> Bool) -> SingMap k f -> SingMap k g -> Bool
-- isSubmapOfBy f t1 t2
--   = (size t1 <= size t2) && (submap' f t1 t2)
--
-- submap' :: (SOrd k, SDecide k) => (forall v. Sing v -> Sing v -> f v -> g v -> Bool) -> SingMap k f -> SingMap k g -> Bool
-- submap' _ Tip _ = True
-- submap' _ _ Tip = False
-- submap' f (Bin _ kx x l r) t
--   = case found of
--       Nothing -> False
--       Just (ky, y)  -> f kx ky x y && submap' f l lt && submap' f r gt
--   where
--     (lt,found,gt) = splitLookupWithKey kx t
--
-- -- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
-- -- Defined as (@'isProperSubmapOf' = 'isProperSubmapOfBy' 'eqTagged'@).
-- isProperSubmapOf :: ((SOrd k, SDecide k) EqTag k f) => SingMap k f -> SingMap k f -> Bool
-- isProperSubmapOf m1 m2
--   = isProperSubmapOfBy eqTagged m1 m2
--
-- {- | /O(n+m)/. Is this a proper submap? (ie. a submap but not equal).
--  The expression (@'isProperSubmapOfBy' f m1 m2@) returns 'True' when
--  @m1@ and @m2@ are not equal,
--  all keys in @m1@ are in @m2@, and when @f@ returns 'True' when
--  applied to their respective keys and values.
-- -}
-- isProperSubmapOfBy :: (SOrd k, SDecide k) => (forall v. Sing v -> Sing v -> f v -> g v -> Bool) -> SingMap k f -> SingMap k g -> Bool
-- isProperSubmapOfBy f t1 t2
--   = (size t1 < size t2) && (submap' f t1 t2)

{--------------------------------------------------------------------
  Filter and partition
--------------------------------------------------------------------}

-- | /O(n)/. Filter all keys\/values that satisfy the predicate.
filterWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> Bool) -> SingMap k f -> SingMap k f
filterWithKey p = go
  where
    go Tip = Tip
    go (Bin _ kx x l r)
          | p kx x    = combine kx x (go l) (go r)
          | otherwise = merge (go l) (go r)

-- | /O(n)/. Partition the map according to a predicate. The first
-- map contains all elements that satisfy the predicate, the second all
-- elements that fail the predicate. See also 'split'.
partitionWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> Bool) -> SingMap k f -> (SingMap k f, SingMap k f)
partitionWithKey _ Tip = (Tip,Tip)
partitionWithKey p (Bin _ kx x l r)
  | p kx x    = (combine kx x l1 r1,merge l2 r2)
  | otherwise = (merge l1 r1,combine kx x l2 r2)
  where
    (l1,l2) = partitionWithKey p l
    (r1,r2) = partitionWithKey p r

-- | /O(n)/. Map keys\/values and collect the 'Just' results.
mapMaybeWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> Maybe (g v)) -> SingMap k f -> SingMap k g
mapMaybeWithKey f = go
  where
    go Tip = Tip
    go (Bin _ kx x l r) = case f kx x of
        Just y  -> combine kx y (go l) (go r)
        Nothing -> merge (go l) (go r)

-- | /O(n)/. Map keys\/values and separate the 'Left' and 'Right' results.
mapEitherWithKey :: (SOrd k, SDecide k) =>
  (forall v. Sing v -> f v -> Either (g v) (h v)) -> SingMap k f -> (SingMap k g, SingMap k h)
mapEitherWithKey _ Tip = (Tip, Tip)
mapEitherWithKey f (Bin _ kx x l r) = case f kx x of
  Left y  -> (combine kx y l1 r1, merge l2 r2)
  Right z -> (merge l1 r1, combine kx z l2 r2)
 where
    (l1,l2) = mapEitherWithKey f l
    (r1,r2) = mapEitherWithKey f r

{--------------------------------------------------------------------
  Mapping
--------------------------------------------------------------------}

-- | /O(n)/. Map a function over all values in the map.
mapWithKey :: (forall v. Sing v -> f v -> g v) -> SingMap k f -> SingMap k g
mapWithKey f = go
  where
    go Tip = Tip
    go (Bin sx kx x l r) = Bin sx kx (f kx x) (go l) (go r)

-- | /O(n)/. The function 'mapAccumLWithKey' threads an accumulating
-- argument throught the map in ascending order of keys.
mapAccumLWithKey :: (forall v. a -> Sing v -> f v -> (a, g v)) -> a -> SingMap k f -> (a, SingMap k g)
mapAccumLWithKey f = go
  where
    go a Tip               = (a,Tip)
    go a (Bin sx kx x l r) =
                 let (a1,l') = go a l
                     (a2,x') = f a1 kx x
                     (a3,r') = go a2 r
                 in (a3,Bin sx kx x' l' r')

-- | /O(n)/. The function 'mapAccumRWithKey' threads an accumulating
-- argument through the map in descending order of keys.
mapAccumRWithKey :: (forall v. a -> Sing v -> f v -> (a, g v)) -> a -> SingMap k f -> (a, SingMap k g)
mapAccumRWithKey f = go
  where
    go a Tip = (a,Tip)
    go a (Bin sx kx x l r) =
                 let (a1,r') = go a r
                     (a2,x') = f a1 kx x
                     (a3,l') = go a2 l
                 in (a3,Bin sx kx x' l' r')

-- TODO: Maybe fix mapKeysWith. I don't think this function is
-- actually meaningful with singletons though.
-- | /O(n*log n)/.
-- @'mapKeysWith' c f s@ is the map obtained by applying @f@ to each key of @s@.
--
-- The size of the result may be smaller if @f@ maps two or more distinct
-- keys to the same new key.  In this case the associated values will be
-- combined using @c@.
-- mapKeysWith :: (SOrd k2, SDecide k2) => (forall v. Sing v -> f v -> f v -> f v) -> (forall v. Sing v -> Sing v) -> SingMap k1 f -> SingMap k2 f
-- mapKeysWith c f = fromListWithKey c . map fFirst . toList
--     where fFirst (SomeSingWith1 x y) = (SomeSingWith1 (f x) y)


-- TODO: Maybe fix mapKeysMonotonic. I don't think this function is
-- actually meaningful with singletons though.
--
-- | /O(n)/.
-- @'mapKeysMonotonic' f s == 'mapKeys' f s@, but works only when @f@
-- is strictly monotonic.
-- That is, for any values @x@ and @y@, if @x@ < @y@ then @f x@ < @f y@.
-- /The precondition is not checked./
-- Semi-formally, we have:
--
-- > and [x < y ==> f x < f y | x <- ls, y <- ls]
-- >                     ==> mapKeysMonotonic f s == mapKeys f s
-- >     where ls = keys s
--
-- This means that @f@ maps distinct original keys to distinct resulting keys.
-- This function has better performance than 'mapKeys'.
-- mapKeysMonotonic :: forall (k1 :: KProxy k) k2 f. (forall (v :: k). Sing v -> Sing v) -> SingMap k1 f -> SingMap k2 f
-- mapKeysMonotonic _ Tip = Tip
-- mapKeysMonotonic f (Bin sz k x l r) =
--     Bin sz (f k) x (mapKeysMonotonic f l) (mapKeysMonotonic f r)

{--------------------------------------------------------------------
  Folds
--------------------------------------------------------------------}

-- | /O(n)/. Fold the keys and values in the map, such that
-- @'foldWithKey' f z == 'Prelude.foldr' ('uncurry' f) z . 'toAscList'@.
--
-- This is identical to 'foldrWithKey', and you should use that one instead of
-- this one.  This name is kept for backward compatibility.
foldWithKey :: (forall v. Sing v -> f v -> b -> b) -> b -> SingMap k f -> b
foldWithKey = foldrWithKey
{-# DEPRECATED foldWithKey "Use foldrWithKey instead" #-}

-- | /O(n)/. Post-order fold.  The function will be applied from the lowest
-- value to the highest.
foldrWithKey :: (forall v. Sing v -> f v -> b -> b) -> b -> SingMap k f -> b
foldrWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f kx x (go z r)) l

-- | /O(n)/. Pre-order fold.  The function will be applied from the highest
-- value to the lowest.
foldlWithKey :: (forall v. b -> Sing v -> f v -> b) -> b -> SingMap k f -> b
foldlWithKey f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = go (f (go z l) kx x) r

{-
-- | /O(n)/. A strict version of 'foldlWithKey'.
foldlWithKey' :: (b -> k -> a -> b) -> b -> SingMap k -> b
foldlWithKey' f = go
  where
    go z Tip              = z
    go z (Bin _ kx x l r) = z `seq` go (f (go z l) kx x) r
-}

{--------------------------------------------------------------------
  List variations
--------------------------------------------------------------------}

-- | /O(n)/. Return all keys of the map in ascending order.
--
-- > keys (fromList [(5,"a"), (3,"b")]) == [3,5]
-- > keys empty == []

keys ::  SingMap k f -> [SomeSing k]
keys m
  = [SomeSing k | (SomeSingWith1 k _) <- assocs m]

-- | /O(n)/. Return all key\/value pairs in the map in ascending key order.
assocs ::  SingMap k f -> [SomeSingWith1 k f]
assocs m
  = toList m

{--------------------------------------------------------------------
  Lists
  use [foldlStrict] to reduce demand on the control-stack
--------------------------------------------------------------------}

-- | /O(n*log n)/. Build a map from a list of key\/value pairs. See also 'fromAscList'.
-- If the list contains more than one value for the same key, the last value
-- for the key is retained.
fromList :: (SOrd k, SDecide k) => [SomeSingWith1 k f] -> SingMap k f
fromList xs
  = foldlStrict ins empty xs
  where
    ins :: (SOrd k, SDecide k) => SingMap k f -> SomeSingWith1 k f -> SingMap k f
    ins t (SomeSingWith1 k x) = insert k x t

-- | /O(n*log n)/. Build a map from a list of key\/value pairs with a combining function. See also 'fromAscListWithKey'.
fromListWithKey :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> f v -> f v) -> [SomeSingWith1 k f] -> SingMap k f
fromListWithKey f xs
  = foldlStrict (ins f) empty xs
  where
    ins :: (SOrd k, SDecide k) => (forall v. Sing v -> f v -> f v -> f v) -> SingMap k f -> SomeSingWith1 k f -> SingMap k f
    ins f t (SomeSingWith1 k x) = insertWithKey f k x t

-- | /O(n)/. Convert to a list of key\/value pairs.
toList ::  SingMap k f -> [SomeSingWith1 k f]
toList t      = toAscList t

-- | /O(n)/. Convert to an ascending list.
toAscList ::  SingMap k f -> [SomeSingWith1 k f]
toAscList t   = foldrWithKey (\k x xs -> (SomeSingWith1 k x):xs) [] t

-- | /O(n)/. Convert to a descending list.
toDescList :: SingMap k f -> [SomeSingWith1 k f]
toDescList t  = foldlWithKey (\xs k x -> (SomeSingWith1 k x):xs) [] t

{--------------------------------------------------------------------
  Building trees from ascending/descending lists can be done in linear time.

  Note that if [xs] is ascending that:
    fromAscList xs       == fromList xs
    fromAscListWith f xs == fromListWith f xs
--------------------------------------------------------------------}

-- | /O(n)/. Build a map from an ascending list in linear time.
-- /The precondition (input list is ascending) is not checked./
fromAscList :: (SEq k, SDecide k) => [SomeSingWith1 k f] -> SingMap k f
fromAscList xs
  = fromAscListWithKey (\_ x _ -> x) xs

-- | /O(n)/. Build a map from an ascending list in linear time with a
-- combining function for equal keys.
-- /The precondition (input list is ascending) is not checked./
fromAscListWithKey :: (SEq k, SDecide k) => (forall v. Sing v -> f v -> f v -> f v) -> [SomeSingWith1 k f] -> SingMap k f
fromAscListWithKey f xs
  = fromDistinctAscList (combineEq f xs)
  where
  -- [combineEq f xs] combines equal elements with function [f] in an ordered list [xs]
  combineEq _ xs'
    = case xs' of
        []     -> []
        [x]    -> [x]
        (x:xx) -> combineEq' f x xx

  combineEq' :: (SEq k, SDecide k) => (forall v. Sing v -> f v -> f v -> f v) -> SomeSingWith1 k f -> [SomeSingWith1 k f] -> [SomeSingWith1 k f]
  combineEq' f z [] = [z]
  combineEq' f z@(SomeSingWith1 kz zz) (x@(SomeSingWith1 kx xx):xs') =
    case kx %:== kz of
      STrue  -> unifyOnEq kx kz (let yy = f kx xx zz in combineEq' f (SomeSingWith1 kx yy) xs')
      SFalse -> z : combineEq' f x xs'


-- | /O(n)/. Build a map from an ascending list of distinct elements in linear time.
-- /The precondition is not checked./
fromDistinctAscList :: [SomeSingWith1 k f] -> SingMap k f
fromDistinctAscList xs
  = build const (length xs) xs
  where
    -- 1) use continutations so that we use heap space instead of stack space.
    -- 2) special case for n==5 to build bushier trees.

    build :: (SingMap k f -> [SomeSingWith1 k f] -> b) -> Int -> [SomeSingWith1 k f] -> b
    build c 0 xs'  = c Tip xs'
    build c 5 xs'  = case xs' of
                       ((SomeSingWith1 k1 x1):(SomeSingWith1 k2 x2):(SomeSingWith1 k3 x3):(SomeSingWith1 k4 x4):(SomeSingWith1 k5 x5):xx)
                            -> c (bin k4 x4 (bin k2 x2 (singleton k1 x1) (singleton k3 x3)) (singleton k5 x5)) xx
                       _ -> error "fromDistinctAscList build"
    build c n xs'  = seq nr $ build (buildR nr c) nl xs'
                   where
                     nl = n `div` 2
                     nr = n - nl - 1

    buildR :: Int -> (SingMap k f -> [SomeSingWith1 k f] -> b) -> SingMap k f -> [SomeSingWith1 k f] -> b
    buildR n c l (SomeSingWith1 k x : ys) = build (buildB l k x c) n ys
    buildR _ _ _ []           = error "fromDistinctAscList buildR []"

    buildB :: SingMap k f -> Sing v -> f v -> (SingMap k f -> a -> b) -> SingMap k f -> a -> b
    buildB l k x c r zs       = c (bin k x l r) zs


{--------------------------------------------------------------------
  Split
--------------------------------------------------------------------}

-- | /O(log n)/. The expression (@'split' k map@) is a pair @(map1,map2)@ where
-- the keys in @map1@ are smaller than @k@ and the keys in @map2@ larger than @k@.
-- Any key equal to @k@ is found in neither @map1@ nor @map2@.
split :: forall k f (v :: k). (SOrd k, SDecide k) => Sing v -> SingMap k f -> (SingMap k f, SingMap k f)
split k = go
  where
    go :: SingMap k f -> (SingMap k f, SingMap k f)
    go Tip              = (Tip, Tip)
    go (Bin _ kx x l r) = case sCompare k kx of
      SLT -> let (lt,gt) = go l in (lt,combine kx x gt r)
      SGT -> let (lt,gt) = go r in (combine kx x l lt,gt)
      SEQ -> unifyOnCompareEQ k kx (l,r)

-- | /O(log n)/. The expression (@'splitLookup' k map@) splits a map just
-- like 'split' but also returns @'lookup' k map@.
splitLookup :: forall k f v. (SOrd k, SDecide k) => Sing v -> SingMap k f -> (SingMap k f, Maybe (f v), SingMap k f)
splitLookup k = go
  where
    go :: SingMap k f -> (SingMap k f, Maybe (f v), SingMap k f)
    go Tip              = (Tip,Nothing,Tip)
    go (Bin _ kx x l r) = case sCompare k kx of
      SLT -> let (lt,z,gt) = go l in (lt,z,combine kx x gt r)
      SGT -> let (lt,z,gt) = go r in (combine kx x l lt,z,gt)
      SEQ -> unifyOnCompareEQ k kx (l,Just x,r)

-- | /O(log n)/.
splitLookupWithKey :: forall k f v. (SOrd k, SDecide k) => Sing v -> SingMap k f -> (SingMap k f, Maybe (Sing v, f v), SingMap k f)
splitLookupWithKey k = go
  where
    go :: SingMap k f -> (SingMap k f, Maybe (Sing v, f v), SingMap k f)
    go Tip              = (Tip,Nothing,Tip)
    go (Bin _ kx x l r) = case sCompare k kx of
      SLT -> let (lt,z,gt) = go l in (lt,z,combine kx x gt r)
      SGT -> let (lt,z,gt) = go r in (combine kx x l lt,z,gt)
      SEQ -> unifyOnCompareEQ k kx (l,Just (kx, x),r)

-- TODO: Enable Eq and Ord instances
{--------------------------------------------------------------------
  Eq converts the tree to a list. In a lazy setting, this
  actually seems one of the faster methods to compare two trees
  and it is certainly the simplest :-)
--------------------------------------------------------------------}
-- instance EqSing1 f => Eq (SingMap k f) where
--   t1 == t2  = (size t1 == size t2) && (toAscList t1 == toAscList t2)

{--------------------------------------------------------------------
  Ord
--------------------------------------------------------------------}

-- instance OrdTag k f => Ord (SingMap k f) where
--     compare m1 m2 = compare (toAscList m1) (toAscList m2)

-- TODO: Figure out show to recreate a Read instance
{--------------------------------------------------------------------
  Read
--------------------------------------------------------------------}

-- instance ((SOrd k, SDecide k) ReadTag k f) => Read (SingMap k f) where
--   readPrec = parens $ prec 10 $ do
--     Ident "fromList" <- lexP
--     xs <- readPrec
--     return (fromList xs)
--
--   readListPrec = readListPrecDefault

-- TODO: Figure out show to recreate a Show instance
{--------------------------------------------------------------------
  Show
--------------------------------------------------------------------}
-- instance ShowTag k f => Show (SingMap k f) where
--     showsPrec p m = showParen (p>10)
--         ( showString "fromList "
--         . showsPrec 11 (toList m)
--         )
--
-- -- | /O(n)/. Show the tree that implements the map. The tree is shown
-- -- in a compressed, hanging format. See 'showTreeWith'.
-- showTree :: ShowTag k f => SingMap k f -> String
-- showTree m
--   = showTreeWith showElem True False m
--   where
--     showElem :: ShowTag k f => Sing v -> f v -> String
--     showElem k x  = show (k :=> x)


{- | /O(n)/. The expression (@'showTreeWith' showelem hang wide map@) shows
 the tree that implements the map. Elements are shown using the @showElem@ function. If @hang@ is
 'True', a /hanging/ tree is shown otherwise a rotated tree is shown. If
 @wide@ is 'True', an extra wide version is shown.
-}
showTreeWith :: (forall v. Sing v -> f v -> String) -> Bool -> Bool -> SingMap k f -> String
showTreeWith showelem hang wide t
  | hang      = (showsTreeHang showelem wide [] t) ""
  | otherwise = (showsTree showelem wide [] [] t) ""

showsTree :: (forall v. Sing v -> f v -> String) -> Bool -> [String] -> [String] -> SingMap k f -> ShowS
showsTree showelem wide lbars rbars t
  = case t of
      Tip -> showsBars lbars . showString "|\n"
      Bin _ kx x Tip Tip
          -> showsBars lbars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          -> showsTree showelem wide (withBar rbars) (withEmpty rbars) r .
             showWide wide rbars .
             showsBars lbars . showString (showelem kx x) . showString "\n" .
             showWide wide lbars .
             showsTree showelem wide (withEmpty lbars) (withBar lbars) l

showsTreeHang :: (forall v. Sing v -> f v -> String) -> Bool -> [String] -> SingMap k f -> ShowS
showsTreeHang showelem wide bars t
  = case t of
      Tip -> showsBars bars . showString "|\n"
      Bin _ kx x Tip Tip
          -> showsBars bars . showString (showelem kx x) . showString "\n"
      Bin _ kx x l r
          -> showsBars bars . showString (showelem kx x) . showString "\n" .
             showWide wide bars .
             showsTreeHang showelem wide (withBar bars) l .
             showWide wide bars .
             showsTreeHang showelem wide (withEmpty bars) r

showWide :: Bool -> [String] -> String -> String
showWide wide bars
  | wide      = showString (concat (reverse bars)) . showString "|\n"
  | otherwise = id

showsBars :: [String] -> ShowS
showsBars bars
  = case bars of
      [] -> id
      _  -> showString (concat (reverse (tail bars))) . showString node

node :: String
node           = "+--"

withBar, withEmpty :: [String] -> [String]
withBar bars   = "|  ":bars
withEmpty bars = "   ":bars

{--------------------------------------------------------------------
  Assertions
--------------------------------------------------------------------}

-- | /O(n)/. Test if the internal map structure is valid.
valid :: (SOrd k, SDecide k) => SingMap k f -> Bool
valid t
  = balanced t && ordered t && validsize t

ordered :: (SOrd k, SDecide k) => SingMap k f -> Bool
ordered t
  = bounded (const True) (const True) t
  where
    bounded :: (SOrd k, SDecide k) => (SomeSing k -> Bool) -> (SomeSing k -> Bool) -> SingMap k f -> Bool
    bounded lo hi t'
      = case t' of
          Tip              -> True
          Bin _ kx _ l r  -> (lo (SomeSing kx))
                          && (hi (SomeSing kx))
                          && bounded lo (`ltSome` SomeSing kx) l
                          && bounded (`gtSome` SomeSing kx) hi r

-- | Exported only for "Debug.QuickCheck"
balanced :: SingMap k f -> Bool
balanced t
  = case t of
      Tip            -> True
      Bin _ _ _ l r  -> (size l + size r <= 1 || (size l <= delta*size r && size r <= delta*size l)) &&
                        balanced l && balanced r

validsize :: SingMap k f -> Bool
validsize t
  = (realsize t == Just (size t))
  where
    realsize t'
      = case t' of
          Tip            -> Just 0
          Bin sz _ _ l r -> case (realsize l,realsize r) of
                            (Just n,Just m)  | n+m+1 == sz  -> Just sz
                            _                               -> Nothing
{--------------------------------------------------------------------
  Utilities
--------------------------------------------------------------------}
foldlStrict :: (a -> b -> a) -> a -> [b] -> a
foldlStrict f = go
  where
    go z []     = z
    go z (x:xs) = z `seq` go (f z x) xs


ltSome :: SOrd k => SomeSing k -> SomeSing k -> Bool
ltSome (SomeSing a) (SomeSing b) = fromSing (a %:< b)

gtSome :: SOrd k => SomeSing k -> SomeSing k -> Bool
gtSome (SomeSing a) (SomeSing b) = fromSing (a %:> b)

unifyOnCompareEQ :: forall k (a :: k) (b :: k) x.
  (SDecide k, Compare a b ~ 'EQ)
  => Sing a -> Sing b -> (a ~ b => x) -> x
unifyOnCompareEQ a b x =
  case testEquality a b of
    Nothing -> error "unifyOnCompareEQ: inconsistent SOrd and SDecide instances"
    Just Refl -> x

unifyOnEq :: forall k (a :: k) (b :: k) x.
  (SDecide k, (a :== b) ~ 'True)
  => Sing a -> Sing b -> (a ~ b => x) -> x
unifyOnEq a b x =
  case testEquality a b of
    Nothing -> error "unifyOnEq: inconsistent SEq and SDecide instances"
    Just Refl -> x

---------------------
-- Record Helpers
---------------------
fromRec :: (SOrd k, SDecide k) => Rec (SingWith1 k f) rs -> SingMap k f
fromRec r = insertRec r empty

insertRec :: (SOrd k, SDecide k) => Rec (SingWith1 k f) rs -> SingMap k f -> SingMap k f
insertRec RNil m = m
insertRec (SingWith1 s v :& rs) m = insert s v (insertRec rs m)

