{-# LANGUAGE TemplateHaskell
           , DataKinds
           , TypeApplications
           , TypeFamilies
           , FlexibleInstances
           , MultiParamTypeClasses
           , FlexibleContexts
           , UndecidableInstances
           , ScopedTypeVariables 
           #-}
module MiniLangExample where

import GHC.Exts
import Data.Maybe
import GHC.Generics (Generic)
import qualified GHC.Generics as GG
import Data.Data (Data)
import Control.Parallel.Strategies

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH (pprint, runIO)
import Data.Type.Bool
import Data.Type.List hiding (Distinct)

import Data.Generics.ClassyPlate
import Data.Generics.ClassyPlate.TH
import Data.Generics.ClassyPlate.Core
import MiniLanguage

testExpr :: Ann Expr Dom RangeStage
testExpr = Ann (NodeInfo NoInfo NodeSpan) $ Add 
             (Ann (NodeInfo NoInfo NodeSpan) $ Var (Ann (NodeInfo NameInfo NodeSpan) Name))
             (Ann (NodeInfo NoInfo NodeSpan) $ Var (Ann (NodeInfo NameInfo NodeSpan) Name))

class Transform t where
  trf :: t -> t

instance Transform (Ann Expr dom stage) where
  trf (Ann ann (Var n)) = (Ann ann (Add (Ann ann (Var n)) (Ann ann (Var n))))
  trf e = e

instance Transform (Ann Name dom stage) where
  trf e = e

type instance AppSelector Transform x = TransformAppSelector x

type family TransformAppSelector x where 
  TransformAppSelector (Ann e dom stage) = True
  TransformAppSelector x = False

test = bottomUp @Transform trf $ testExpr
test2 = smartTraverse @Transform trf $ testExpr

makeClassyPlate [ IgnoreField '_annotation ] ''Ann

makeClassyPlate [ IgnoreArg 'Lit 0 ] ''Expr
makeClassyPlate [] ''Name

-- $( do pl <- makeClassyPlate [ '_annotation ] ''Ann
--       runIO $ putStrLn $ pprint pl
--       return [] )
