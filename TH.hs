{-# LANGUAGE TemplateHaskellQuotes #-} 
module TH (makeClassyPlate) where

import Data.Maybe
import Control.Monad
import Control.Applicative

import Language.Haskell.TH

import ClassyPlate
import TypePrune

-- | Creates ClassyPlate instances for a datatype. Can specify which fields should not be traversed.
makeClassyPlate :: [Name] -> Name -> Q [Dec]
makeClassyPlate primitives dataType 
  = do inf <- reify dataType
       case inf of (TyConI (DataD _ name tvs _ cons _)) 
                     -> return $ [ makeNormalCPForDataType name tvs (map (getConRep primitives) cons)
                                 , makeAutoCPForDataType name tvs (map (getConRep primitives) cons)
                                 ]

makeNormalCPForDataType :: Name -> [TyVarBndr] -> [ConRep] -> Dec
makeNormalCPForDataType name tvs cons
  = let headType = foldl AppT (ConT name) (map (VarT . getTVName) tvs)
        clsVar = mkName "c"
     in InstanceD Nothing (generateCtx clsVar headType cons) 
                          (ConT ''ClassyPlate `AppT` VarT clsVar `AppT` headType) 
                          (generateDefs clsVar headType name cons)

-- | Creates the @ClassyPlate@
makeAutoCPForDataType :: Name -> [TyVarBndr] -> [ConRep] -> Dec
makeAutoCPForDataType name tvs cons
  = let headType = foldl AppT (ConT name) (map (VarT . getTVName) tvs)
        clsVar = mkName "c"
     in InstanceD Nothing (generateAutoCtx clsVar headType cons) 
                          (ConT ''AutoApply 
                            `AppT` VarT clsVar 
                            `AppT` ConT 'False  
                            `AppT` headType) 
                          (generateAutoDefs clsVar headType name cons)


generateCtx :: Name -> Type -> [ConRep] -> Cxt
generateCtx clsVar selfType cons 
  = (ConT ''GoodOperationFor `AppT` VarT clsVar `AppT` selfType) 
      : map ((ConT ''ClassyPlate `AppT` VarT clsVar) `AppT`) (concatMap (\(_, args) -> catMaybes args) cons)

-- | Generates the body of the instance definitions for normal classyplates
generateDefs :: Name -> Type -> Name -> [ConRep] -> [Dec]
generateDefs clsVar headType tyName cons = 
  [ FunD 'apply (map (generateAppClause clsVar headType tyName) cons)
  , FunD 'applyM (map (generateAppMClause clsVar headType tyName) cons)
  , FunD 'applySelective (map (generateSelectiveAppClause tyName) cons)
  , FunD 'applySelectiveM (map (generateSelectiveAppMClause tyName) cons)
  ]


generateAutoCtx :: Name -> Type -> [ConRep] -> Cxt
generateAutoCtx clsVar selfType cons 
  = (ConT ''GoodOperationForAuto `AppT` VarT clsVar `AppT` selfType) 
      : map (\t -> (ConT ''AutoApply `AppT` VarT clsVar
                      `AppT` (ConT ''ClassIgnoresSubtree `AppT` VarT clsVar `AppT` t)) `AppT` t)
            (concatMap (\(_, args) -> catMaybes args) cons)

-- | Generates the body of the instance definition for auto classy plate
generateAutoDefs :: Name -> Type -> Name -> [ConRep] -> [Dec]
generateAutoDefs clsVar headType tyName cons = 
  [ FunD 'applyAuto (map (generateAppAutoClause clsVar headType tyName) cons)
  , FunD 'applyAutoM (map (generateAppAutoMClause clsVar headType tyName) cons)
  ]

-- * Normal definitions

-- | Creates the clause for the @apply@ function for one constructor: @apply t f (Add e1 e2) = app (undefined :: FlagToken (AppSelector c (Expr dom stage))) t f $ Add (apply t f e1) (apply t f e2)@
generateAppClause :: Name -> Type -> Name -> ConRep -> Clause
generateAppClause clsVar headType tyName (conName, args) 
  = Clause [VarP tokenName, VarP funName, ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (generateAppExpr clsVar headType tokenName funName 
                 `AppE` generateRecombineExpr conName tokenName funName (zip (map isJust args) argNames))) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"

generateAppExpr :: Name -> Type -> Name -> Name -> Exp
generateAppExpr clsVar headType tokenName funName
  = VarE 'app `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''AppSelector `AppT` VarT clsVar `AppT` headType)))
              `AppE` VarE tokenName `AppE` VarE funName

generateRecombineExpr :: Name -> Name -> Name -> [(Bool, Name)] -> Exp
generateRecombineExpr conName tokenName funName args
  = foldl AppE (ConE conName) (map mapArgRep args)
  where mapArgRep (True, n) = VarE 'apply `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (False, n) = VarE n

-- * Monadic definitions

-- | Creates the clause for the @applyM@ function for one constructor: @applyM t f (Ann ann e) = appM (undefined :: FlagToken (AppSelector c (Ann e dom stage))) t f =<< (Ann <$> return ann <*> applyM t f e)@
generateAppMClause :: Name -> Type -> Name -> ConRep -> Clause
generateAppMClause clsVar headType tyName (conName, args) 
  = Clause [VarP tokenName, VarP funName, ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (InfixE (Just $ generateAppMExpr clsVar headType tokenName funName)
                       (VarE '(=<<))
                       (Just $ generateRecombineMExpr conName tokenName funName (zip (map isJust args) argNames)) )) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"

generateAppMExpr :: Name -> Type -> Name -> Name -> Exp
generateAppMExpr clsVar headType tokenName funName
  = VarE 'appM `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''AppSelector `AppT` VarT clsVar `AppT` headType)))
               `AppE` VarE tokenName `AppE` VarE funName

generateRecombineMExpr :: Name -> Name -> Name -> [(Bool, Name)] -> Exp
generateRecombineMExpr conName tokenName funName []
  = AppE (VarE 'return) (ConE conName)
generateRecombineMExpr conName tokenName funName (fst:args)
  = foldl (\base -> InfixE (Just base) (VarE '(<*>)) . Just) 
          (InfixE (Just $ ConE conName) (VarE '(<$>)) (Just $ mapArgRep fst)) 
          (map mapArgRep args)
  where mapArgRep (True, n) = VarE 'applyM `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (False, n) = VarE 'return `AppE` VarE n

-- * Selective definitions

-- | Creates the clause for the @applySelective@ function for one constructor: @applySelective t f pred val@(CB b) = appIf t f pred val (CB (applySelective t f pred b))@
generateSelectiveAppClause :: Name -> ConRep -> Clause
generateSelectiveAppClause tyName (conName, args) 
  = Clause [VarP tokenName, VarP funName, VarP predName, AsP valName $ ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (generateAppIfExpr tokenName funName predName valName
                 `AppE` generateSelectiveRecombineExpr conName tokenName funName predName (zip (map isJust args) argNames))) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"
        predName = mkName "p"
        valName = mkName "v"

generateAppIfExpr :: Name -> Name -> Name -> Name -> Exp
generateAppIfExpr tokenName funName predName valName
  = VarE 'appIf `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE predName `AppE` VarE valName

generateSelectiveRecombineExpr :: Name -> Name -> Name -> Name -> [(Bool, Name)] -> Exp
generateSelectiveRecombineExpr conName tokenName funName predName args
  = foldl AppE (ConE conName) (map mapArgRep args)
  where mapArgRep (True, n) = VarE 'applySelective `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE predName `AppE` VarE n
        mapArgRep (False, n) = VarE n

-- * Monadic selective definitions

-- | Creates the clause for the @applySelectiveM@ function for one constructor:
generateSelectiveAppMClause :: Name -> ConRep -> Clause
generateSelectiveAppMClause tyName (conName, args) 
  = Clause [VarP tokenName, VarP funName, VarP predName, AsP valName $ ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (generateAppIfMExpr tokenName funName predName valName
                 `AppE` generateSelectiveRecombineMExpr conName tokenName funName predName (zip (map isJust args) argNames))) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"
        predName = mkName "p"
        valName = mkName "v"

generateAppIfMExpr :: Name -> Name -> Name -> Name -> Exp
generateAppIfMExpr tokenName funName predName valName
  = VarE 'appIfM `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE predName `AppE` VarE valName

generateSelectiveRecombineMExpr :: Name -> Name -> Name -> Name -> [(Bool, Name)] -> Exp
generateSelectiveRecombineMExpr conName tokenName funName predName []
  = AppE (VarE 'return) (ConE conName)
generateSelectiveRecombineMExpr conName tokenName funName predName (fst:args)
  = foldl (\base -> InfixE (Just base) (VarE '(<*>)) . Just) 
          (InfixE (Just $ ConE conName) (VarE '(<$>)) (Just $ mapArgRep fst)) 
          (map mapArgRep args)
  where mapArgRep (True, n) = VarE 'applySelectiveM `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE predName `AppE` VarE n
        mapArgRep (False, n) = VarE 'return `AppE` VarE n

-- * Automatic definitions

-- | Creates the clause for the @applyAuto@ function for one constructor
generateAppAutoClause :: Name -> Type -> Name -> ConRep -> Clause
generateAppAutoClause clsVar headType tyName (conName, args) 
  = Clause [WildP, VarP tokenName, VarP funName, ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (generateAppExpr clsVar headType tokenName funName 
                 `AppE` generateAutoRecombineExpr clsVar conName tokenName funName (zip args argNames))) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"

generateAutoRecombineExpr :: Name -> Name -> Name -> Name -> [(Maybe Type, Name)] -> Exp
generateAutoRecombineExpr clsVar conName tokenName funName args
  = foldl AppE (ConE conName) (map mapArgRep args)
  where mapArgRep (Just t, n) 
          = VarE 'applyAuto 
              `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''ClassIgnoresSubtree `AppT` VarT clsVar `AppT` t))) 
              `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (Nothing, n) = VarE n

-- * Monadic automatic definitions

-- | Creates the clause for the @applyAutoM@ function for one constructor
generateAppAutoMClause :: Name -> Type -> Name -> ConRep -> Clause
generateAppAutoMClause clsVar headType tyName (conName, args) 
  = Clause [WildP, VarP tokenName, VarP funName, ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (InfixE (Just $ generateAppMExpr clsVar headType tokenName funName)
                       (VarE '(=<<))
                       (Just $ generateAutoRecombineMExpr clsVar conName tokenName funName (zip args argNames)) )) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"

generateAutoRecombineMExpr :: Name -> Name -> Name -> Name -> [(Maybe Type, Name)] -> Exp
generateAutoRecombineMExpr _ conName tokenName funName []
  = AppE (VarE 'return) (ConE conName)
generateAutoRecombineMExpr clsVar conName tokenName funName (fst:args)
  = foldl (\base -> InfixE (Just base) (VarE '(<*>)) . Just) 
          (InfixE (Just $ ConE conName) (VarE '(<$>)) (Just $ mapArgRep fst)) 
          (map mapArgRep args)
  where mapArgRep (Just t, n) 
          = VarE 'applyAutoM 
             `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''ClassIgnoresSubtree `AppT` VarT clsVar `AppT` t))) 
             `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (Nothing, n) = VarE 'return `AppE` VarE n

-- | Gets the name of a type variable
getTVName :: TyVarBndr -> Name
getTVName (PlainTV n) = n
getTVName (KindedTV n _) = n

-- | The information we need from a constructor.
type ConRep = (Name, [Maybe Type])

-- | Extracts the necessary information from a constructor.
getConRep :: [Name] -> Con -> ConRep
getConRep primitives (NormalC n args) = (n, map (Just . snd) args)
getConRep primitives (RecC n args) = (n, map (\(fldN,_,t) -> if fldN `elem` primitives then Nothing else Just t) args)
getConRep primitives (InfixC (_,t1) n (_,t2)) = (n, [Just t1, Just t2])
getConRep primitives (ForallC _ _ c) = getConRep primitives c
getConRep _ _ = error "GADTs are not supported"