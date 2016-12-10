{-# LANGUAGE Rank2Types
           , ConstraintKinds
           , KindSignatures
           , TypeFamilies
           , ScopedTypeVariables
           , MultiParamTypeClasses
           , AllowAmbiguousTypes
           , FlexibleContexts
           , FlexibleInstances
           , UndecidableInstances
           , DataKinds
           , TypeApplications
           , DeriveGeneric
           , DeriveDataTypeable
           , TypeOperators
           , PolyKinds 
           #-}
module Data.Generics.ClassyPlate.Core
  ( -- public functions and classes
    ClassyPlate, SmartClassyPlate, SmartClassyPlate'
    -- generator functions and datatypes
  , bottomUp_, bottomUpM_, smartTraverse_, smartTraverseM_
  , descend_, descendM_, topDown_, topDownM_

  , app, appM, appTD, appTDM
  , GoodOperationFor, GoodOperationForAuto, FlagToken
  , ClsToken, FlagToken
  ) where

import GHC.Exts
import Data.Maybe
import Control.Monad
import GHC.Generics (Generic)
import Data.Data (Data)

import Data.Generics.ClassyPlate.TypePrune

-- FIXME: when TH supports type application we can remove the token parameters

type GoodOperationFor c e = (App (AppSelector c e) c e)
type GoodOperationForAuto c e = (GoodOperationFor c e, Generic e)

data ClsToken (c :: * -> Constraint)
data FlagToken (c :: Bool)

-- | A class for applying a function if the class of the functions allows the application
class App (flag :: Bool) c b where
  app :: FlagToken flag -> ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
  appM :: Monad m => FlagToken flag -> ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b
  appTD :: FlagToken flag -> ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> a) -> (b -> b) -> b -> b
  appTDM :: Monad m => FlagToken flag -> ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> m a) -> (b -> m b) -> b -> m b

instance (ClassyPlate c b, c b) => App 'True c b where
  {-# INLINE app #-}
  app _ _ f a = f a
  {-# INLINE appM #-}
  appM _ _ f a = f a

  {-# INLINE appTD #-}
  appTD _ _ f _ a = f a
  {-# INLINE appTDM #-}
  appTDM _ _ f _ a = f a

instance App 'False c b where
  {-# INLINE app #-}
  app _ _ _ a = a
  {-# INLINE appM #-}
  appM _ _ _ a = return a

  {-# INLINE appTD #-}
  appTD _ _ _ d a = d a
  {-# INLINE appTDM #-}
  appTDM _ _ _ d a = d a

-- | A class for traversals that use a polymorphic function to visit all applicable elements.
class GoodOperationFor c b => ClassyPlate c b where
  bottomUp_ :: ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
  bottomUpM_ :: Monad m => ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b

  descend_ :: ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
  descendM_ :: Monad m => ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b

  topDown_ :: ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
  topDownM_ :: Monad m => ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b

type SmartClassyPlate c b = SmartClassyPlate' c (ClassIgnoresSubtree c b) b

-- | A class for traversals that use a polymorphic function to visit all applicable elements but only visit the 
-- parts where the applicable elements could be found.
class (GoodOperationForAuto c b) => SmartClassyPlate' c (sel :: Bool) b where
  smartTraverse_ :: FlagToken sel -> ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> a) -> b -> b
  smartTraverseM_ :: Monad m => FlagToken sel -> ClsToken c -> (forall a . (ClassyPlate c a, c a) => a -> m a) -> b -> m b

instance (GoodOperationForAuto c b) => SmartClassyPlate' c True b where
  smartTraverse_ _ t f a = app (undefined :: FlagToken (AppSelector c b)) t f a
  {-# INLINE smartTraverse_ #-}
  smartTraverseM_ _ t f a = appM (undefined :: FlagToken (AppSelector c b)) t f a
  {-# INLINE smartTraverseM_ #-}
