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
           , TemplateHaskell
           , UndecidableInstances
           #-}
-- | Wrappers and common functionality for classyplates
module Data.Generics.ClassyPlate.Common where

import Control.Monad

import Data.Generics.ClassyPlate.TH
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

-- * Commonly used instances

-- The [] instance is optimized, will invoke the app only once on a list
instance (GoodOperationFor c [a], ClassyPlate c a) => ClassyPlate c [a] where
  topDown_ t f ls = map (topDown_ t f) $ app (undefined :: FlagToken (AppSelector c [a])) t f ls
  topDownM_ t f ls = mapM (topDownM_ t f) =<< appM (undefined :: FlagToken (AppSelector c [a])) t f ls

  bottomUp_ t f ls = app (undefined :: FlagToken (AppSelector c [a])) t f $ map (bottomUp_ t f) ls
  bottomUpM_ t f ls = appM (undefined :: FlagToken (AppSelector c [a])) t f =<< mapM (bottomUpM_ t f) ls

  descend_ t f ls = map (appTD (undefined :: FlagToken (AppSelector c a)) t f (descend_ t f)) ls
  descendM_ t f ls = mapM (appTDM (undefined :: FlagToken (AppSelector c a)) t f (descendM_ t f)) ls 

-- we don't need to do addition check here
instance (GoodOperationForAuto c [a], SmartClassyPlate' c flag a) => SmartClassyPlate' c flag [a] where
  smartTraverse_ _ t f ls = map (smartTraverse_ (undefined :: FlagToken flag) t f) $ app (undefined :: FlagToken (AppSelector c [a])) t f ls
  smartTraverseM_ _ t f ls = mapM (smartTraverseM_ (undefined :: FlagToken flag) t f) =<< appM (undefined :: FlagToken (AppSelector c [a])) t f ls

type instance IgnoredFields [a] = '[]


makeClassyPlate [] ''(,)
makeClassyPlate [] ''(,,)
makeClassyPlate [] ''(,,,)
makeClassyPlate [] ''Maybe
makeClassyPlate [] ''Either
makeClassyPlate [] ''Bool