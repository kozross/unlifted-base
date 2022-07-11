{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UnboxedSums #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE UnliftedNewtypes #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Unlifted.Ordering
  ( -- * Types
    Bool (False, True),
    Maybe,

    -- * Type classes
    Eq (..),
    StrictPreOrd (..),

    -- * Functions
    not,
    and,
    or,
  )
where

import GHC.Prim
  ( Int#,
    Int16#,
    Int32#,
    Int8#,
    Word#,
    Word16#,
    Word32#,
    Word8#,
    eqInt16#,
    eqInt32#,
    eqInt8#,
    eqWord#,
    eqWord16#,
    eqWord32#,
    eqWord8#,
    (==#),
  )
import GHC.Types
  ( RuntimeRep (SumRep, TupleRep),
    TYPE,
  )

{-# ANN module "HLint: use if" #-}

-- | Boolean values. This is not only unlifted, but also unboxed, hence its
-- somewhat scary-looking kind.
--
-- @since 1.0.0
type Bool :: TYPE ('SumRep ['TupleRep '[], 'TupleRep '[]])
newtype Bool = Bool (# (# #)| (# #) #)

-- | The canonical false value.
--
-- @since 1.0.0
pattern False :: Bool
pattern False <-
  Bool (# (##) | #)
  where
    False = Bool (# (##) | #)

-- | The canonical true value.
--
-- @since 1.0.0
pattern True :: Bool
pattern True <-
  Bool (# | (##) #)
  where
    True = Bool (# | (##) #)

{-# COMPLETE False, True #-}

-- | A value which might be missing. This is not only unlifted, but also
-- unboxed, hence its somewhat scary-looking kind.
--
-- @since 1.0.0
type Maybe ::
  forall (rep :: RuntimeRep).
  TYPE rep ->
  TYPE ('SumRep ['TupleRep '[], 'TupleRep '[rep]])
newtype Maybe a = Maybe (# (# #)| (# a #) #)

-- | @since 1.0.0
instance (Eq a) => Eq (Maybe a) where
  Maybe xs == Maybe ys = case xs of
    (# (##) | #) -> case ys of
      (# (##) | #) -> True
      _ -> False
    (# | (# x #) #) -> case ys of
      (# | (# y #) #) -> x == y
      _ -> False
  Maybe xs /= Maybe ys = case xs of
    (# (##) | #) -> case ys of
      (# (##) | #) -> False
      _ -> True
    (# | (# x #) #) -> case ys of
      (# | (# y #) #) -> x /= y
      _ -> True

-- | Inverts a boolean value: 'True' becomes 'False' and vice versa.
--
-- @since 1.0.0
not :: Bool -> Bool
not = \case
  False -> True
  True -> False

-- | 'True' if both arguments are true, 'False' otherwise.
--
-- @since 1.0.0
and :: Bool -> Bool -> Bool
and b b' = case b of
  False -> False
  True -> b'

-- | 'True' if one of the arguments is 'True', 'False' otherwise.
--
-- @since 1.0.0
or :: Bool -> Bool -> Bool
or b b' = case b of
  True -> True
  False -> b'

-- TODO: if-then-else, as strict semantics force us to define it specially
--
-- we do have RebindableSyntax for that at least

-- | The ability to compare values for (structural) equality.
--
-- This type class is representationally-polymorphic: instances of it can be
-- defined over a type of any representation.
--
-- = Laws
--
-- * /Reflexivity/: @x '==' x@ @=@ @'True'@
-- * /Symmetry/: @x '==' y@ @=@ @y '==' x@
-- * /Transitivity/: If @x '==' y@ and @y '==' z@, then @x '==' z@
-- * /Substitution/: For any pure function @f@, @x '==' y@ @=@ @f x '==' f y@
--
-- Furthermore, it must be the case that @x '==' y = 'True'@ if and only if
-- @x '/=' y = 'False'@, and that @x '==' y = 'False'@ if and only if @x '/=' y
-- = 'True'@.
--
-- = Note
--
-- IEEE-754 floating point types /cannot/ be instances of this type class, as
-- their equality (as defined by the standard) cannot even be reflexive. While
-- we can't stop you writing such awful instances, please don't do it.
--
-- @since 1.0.0
class Eq (a :: TYPE rep) where
  -- | Compare two values for representational equality. This is 'True' if and
  -- only if the arguments are representationally equal.
  (==) :: a -> a -> Bool

  -- | Compare two values for representational /in/equality. This is 'True' if
  -- and only if the arguments are representationally different.
  (/=) :: a -> a -> Bool

-- | @since 1.0.0
instance Eq Bool where
  {-# INLINE (==) #-}
  False == False = True
  True == True = True
  _ == _ = False
  {-# INLINE (/=) #-}
  False /= True = True
  True /= False = True
  _ /= _ = False

-- | @since 1.0.0
instance Eq Word8# where
  {-# INLINE (==) #-}
  w8 == w8' = case eqWord8# w8 w8' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  w8 /= w8' = case eqWord8# w8 w8' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Word16# where
  {-# INLINE (==) #-}
  w16 == w16' = case eqWord16# w16 w16' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  w16 /= w16' = case eqWord16# w16 w16' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Word32# where
  {-# INLINE (==) #-}
  w32 == w32' = case eqWord32# w32 w32' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  w32 /= w32' = case eqWord32# w32 w32' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Word# where
  {-# INLINE (==) #-}
  w == w' = case eqWord# w w' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  w /= w' = case eqWord# w w' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Int8# where
  {-# INLINE (==) #-}
  i8 == i8' = case eqInt8# i8 i8' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  i8 /= i8' = case eqInt8# i8 i8' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Int16# where
  {-# INLINE (==) #-}
  i16 == i16' = case eqInt16# i16 i16' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  i16 /= i16' = case eqInt16# i16 i16' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Int32# where
  {-# INLINE (==) #-}
  i32 == i32' = case eqInt32# i32 i32' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  i32 /= i32' = case eqInt32# i32 i32' of
    0# -> True
    _ -> False

-- | @since 1.0.0
instance Eq Int# where
  {-# INLINE (==) #-}
  i == i' = case i ==# i' of
    1# -> True
    _ -> False
  {-# INLINE (/=) #-}
  i /= i' = case i ==# i' of
    0# -> True
    _ -> False

-- | A class representing strict preorders.
--
-- = Laws
--
-- * /Asymmetry/: If @x '<?' y@ @=@ @'Just' b@, then @y '<?' x@ @=@ @'Just'
-- ('not' b)@
-- * /Transitivity/: If @x '<?' y@ @=@ @'Just' 'True'@ and @y '<?' z@ @=@
-- @'Just' 'True'@, then @x '<?' z@ @=@ @'Just' 'True'@
--
-- = Note
--
-- This gives us some manner of ability to compare IEEE-754 floating-point
-- values without it being completely lawless.
--
-- @since 1.0.0
class StrictPreOrd (a :: TYPE rep) where
  -- | Performs a partial comparison. Returns 'Just' 'True' if the first
  -- argument is ordered before the second, 'Just' 'False' if the second is
  -- ordered before the first, and 'Nothing' otherwise.
  --
  -- = Note
  --
  -- Since 'StrictPreOrd' is not \'aware\' of equality, a result of 'Nothing'
  -- can indicate both equality and incomparability.
  (<?) :: a -> a -> Maybe Bool

-- | @since 1.0.0
instance StrictPreOrd Bool where
  False <? True = Maybe (# | (# True #) #)
  True <? False = Maybe (# | (# False #) #)
  _ <? _ = Maybe (# (##) | #)
