{-# LANGUAGE ScopedTypeVariables
           , TypeApplications
           , DataKinds
           , ConstraintKinds
           , AllowAmbiguousTypes
           , MultiParamTypeClasses
           , FlexibleInstances
           , FlexibleContexts
           , RankNTypes
           , TypeFamilies
           #-}
-- | Wrappers and common functionality for classyplates
module Data.Generics.ClassyPlate.Common where

import Control.Monad

import Data.Generics.ClassyPlate.Core
import Data.Generics.ClassyPlate.TypePrune

-- | A class for the simple case when the applied function is monomorphic.
class MonoMatch a b where
  -- | Apply a monomorphic function on a polymorphic data structure.
  monoApp :: (a -> a) -> b -> b
  monoAppM :: (a -> m a) -> b -> m b

instance MonoMatch a a where
  monoApp = id
  {-# INLINE monoApp #-}
  monoAppM = id
  {-# INLINE monoAppM #-}

type instance AppSelector (MonoMatch a) b = TypEq a b
  
type family TypEq a b :: Bool where
  TypEq a a = 'True
  TypEq a b = 'False

-- | Go down one level in the data structure and apply the given polymorphic function
descend :: forall c b . ClassyPlate c b => (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
{-# INLINE descend #-}
descend = descend_ (undefined :: ClsToken c)

descendM :: forall c b m . (ClassyPlate c b, Monad m) => (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b
{-# INLINE descendM #-}
descendM = descendM_ (undefined :: ClsToken c)


-- | Traverse the data structure in a top-down fashion with a polymorphic function.
topDown :: forall c b . ClassyPlate c b => (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
{-# INLINE topDown #-}
topDown = topDown_ (undefined :: ClsToken c)

topDownM :: forall c b m . (ClassyPlate c b, Monad m) => (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b
{-# INLINE topDownM #-}
topDownM = topDownM_ (undefined :: ClsToken c)

-- | Traverse the data structure with a polymorphic function.
bottomUp :: forall c b . ClassyPlate c b => (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
{-# INLINE bottomUp #-}
bottomUp = bottomUp_ (undefined :: ClsToken c)

-- | Traverse the data structure with a polymorphic monadic function.
bottomUpM :: forall c b m . (ClassyPlate c b, Monad m) 
                => (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b
{-# INLINE bottomUpM #-}
bottomUpM = bottomUpM_ (undefined :: ClsToken c)

-- | Traverse the data structure selectively with a function specifying if need to go down on the subtrees.
selectiveTraverse :: forall c b . ClassyPlate c b => (forall a . (ClassyPlate c a, c a) => a -> (a, Bool)) -> b -> b
{-# INLINE selectiveTraverse #-}
selectiveTraverse trf = descend @c ((\(e, go) -> if go then selectiveTraverse @c trf e else e) . trf)

-- | Traverse the data structure selectively with a monadic function specifying if need to go down on the subtrees.
selectiveTraverseM :: forall c b m . (Monad m, ClassyPlate c b) => (forall a . (ClassyPlate c a, c a) => a -> m (a, Bool)) -> b -> m b
{-# INLINE selectiveTraverseM #-}
selectiveTraverseM trf = descendM @c ((\(e, go) -> if go then selectiveTraverseM @c trf e else return e) <=< trf)

-- | Traverse only those parts of the data structure that could possibly contain elements that the given function can be applied on
smartTraverse :: forall c b . SmartClassyPlate c b 
              => (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
{-# INLINE smartTraverse #-}
smartTraverse = smartTraverse_ (undefined :: FlagToken (ClassIgnoresSubtree c b)) (undefined :: ClsToken c)

-- | Traverse only those parts of the data structure that could possibly contain elements that the given monadic function can be applied on
smartTraverseM :: forall c b m . (SmartClassyPlate c b, Monad m) 
               => (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b
{-# INLINE smartTraverseM #-}
smartTraverseM = smartTraverseM_ (undefined :: FlagToken (ClassIgnoresSubtree c b)) (undefined :: ClsToken c)