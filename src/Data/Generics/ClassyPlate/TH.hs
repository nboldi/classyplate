{-# LANGUAGE TemplateHaskellQuotes #-} 
module Data.Generics.ClassyPlate.TH (makeClassyPlate, TraverseSelector(..)) where

import Data.Maybe
import Data.Either
import Control.Monad
import Control.Applicative

import Language.Haskell.TH

import Data.Generics.ClassyPlate.Core
import Data.Generics.ClassyPlate.TypePrune

-- TODO: make the definitions inlineable, and try speed gains by inlining

data TraverseSelector = IgnoreField Name
                      | IgnoreArg Name Integer
                      | IsPrimitive
  deriving Eq

type PrimitiveMarkers = [TraverseSelector]

-- | Creates ClassyPlate instances for a datatype. Can specify which fields should not be traversed.
makeClassyPlate :: PrimitiveMarkers -> Name -> Q [Dec]
makeClassyPlate primitives dataType 
  = do inf <- reify dataType
       case inf of (TyConI (DataD _ name tvs _ cons _)) -> createClassyPlate name tvs cons
                   (TyConI (NewtypeD _ name tvs _ con _)) -> createClassyPlate name tvs [con]
                   _ -> error $ "Cannot create classyplate for " ++ show dataType ++ " only data and newtype declarations are supported."
  where createClassyPlate name tvs cons 
          = let headType = foldl AppT (ConT name) (map (VarT . getTVName) tvs)
             in sequence $ [ makeNormalCPForDataType name headType tvs (map (getConRep primitives) cons)
                           , makeAutoCPForDataType name headType tvs (map (getConRep primitives) cons)
                           , return $ makeIgnoredFieldsTF headType primitives
                           ]

makeNormalCPForDataType :: Name -> Type -> [TyVarBndr] -> [ConRep] -> Q Dec
makeNormalCPForDataType name headType tvs cons
  = do clsVar <- newName "c"
       return $ InstanceD Nothing (generateCtx clsVar headType cons) 
                          (ConT ''ClassyPlate `AppT` VarT clsVar `AppT` headType) 
                          (generateDefs clsVar headType name cons)

-- | Creates the @ClassyPlate@
makeAutoCPForDataType :: Name -> Type -> [TyVarBndr] -> [ConRep] -> Q Dec
makeAutoCPForDataType name headType tvs cons
  = do clsVar <- newName "c"
       return $ InstanceD Nothing (generateAutoCtx clsVar headType cons) 
                          (ConT ''SmartClassyPlate'
                            `AppT` VarT clsVar 
                            `AppT` ConT 'False  
                            `AppT` headType) 
                          (generateAutoDefs clsVar headType name cons)

-- | Creates an @IgnoredFields@ type instance according to the ignored fields specified
makeIgnoredFieldsTF :: Type -> PrimitiveMarkers -> Dec
makeIgnoredFieldsTF typ ignored 
  = TySynInstD ''IgnoredFields (TySynEqn [typ] (foldr typeListCons PromotedNilT ignored))
  where typeListCons :: TraverseSelector -> Type -> Type
        typeListCons (IgnoreField fld) = ((PromotedConsT `AppT` (PromotedT 'PrIgnoreField `AppT` (LitT $ StrTyLit $ nameBase fld))) `AppT`)
        typeListCons (IgnoreArg cons n) = ((PromotedConsT `AppT` (PromotedT 'PrIgnoreArg `AppT` (LitT $ StrTyLit $ nameBase cons) `AppT` (LitT $ NumTyLit $ fromIntegral n))) `AppT`)
        typeListCons IsPrimitive = ((PromotedConsT `AppT` (PromotedT 'PrIsPrimitive)) `AppT`)

generateCtx :: Name -> Type -> [ConRep] -> Cxt
generateCtx clsVar selfType cons 
  = (ConT ''GoodOperationFor `AppT` VarT clsVar `AppT` selfType) 
      : map ((ConT ''ClassyPlate `AppT` VarT clsVar) `AppT`) (concatMap (\(_, args) -> catMaybes args) cons)

-- | Generates the body of the instance definitions for normal classyplates
generateDefs :: Name -> Type -> Name -> [ConRep] -> [Dec]
generateDefs clsVar headType tyName cons = 
  [ FunD 'bottomUp_ (map (generateAppClause clsVar headType tyName) cons)
  , FunD 'bottomUpM_ (map (generateAppMClause clsVar headType tyName) cons)
  , FunD 'topDown_ [generateTopDownClause generateTopDownExpr clsVar headType cons]
  , FunD 'topDownM_ [generateTopDownClause generateTopDownMExpr clsVar headType cons]
  , FunD 'descend_ (map (generateDescendAppClause clsVar headType tyName) cons)
  , FunD 'descendM_ (map (generateDescendMAppClause clsVar headType tyName) cons)
  ]


generateAutoCtx :: Name -> Type -> [ConRep] -> Cxt
generateAutoCtx clsVar selfType cons 
  = (ConT ''GoodOperationForAuto `AppT` VarT clsVar `AppT` selfType) 
      : map (\t -> (ConT ''SmartClassyPlate' `AppT` VarT clsVar
                      `AppT` (ConT ''ClassIgnoresSubtree `AppT` VarT clsVar `AppT` t)) `AppT` t)
            (concatMap (\(_, args) -> catMaybes args) cons)

-- | Generates the body of the instance definition for auto classy plate
generateAutoDefs :: Name -> Type -> Name -> [ConRep] -> [Dec]
generateAutoDefs clsVar headType tyName cons = 
  [ FunD 'smartTraverse_ (map (generateAppAutoClause clsVar headType tyName) cons)
  , FunD 'smartTraverseM_ (map (generateAppAutoMClause clsVar headType tyName) cons)
  ]

-- * Normal definitions

-- | Creates the clause for the @classyTraverse_@ function for one constructor: @classyTraverse_ t f (Add e1 e2) = app (undefined :: FlagToken (AppSelector c (Expr dom stage))) t f $ Add (classyTraverse_ t f e1) (classyTraverse_ t f e2)@
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
  where mapArgRep (True, n) = VarE 'bottomUp_ `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (False, n) = VarE n

-- * Monadic definitions

-- | Creates the clause for the @classyTraverseM_@ function for one constructor: @classyTraverseM_ t f (Ann ann e) = appM (undefined :: FlagToken (AppSelector c (Ann e dom stage))) t f =<< (Ann <$> return ann <*> applyM t f e)@
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
  where mapArgRep (True, n) = VarE 'bottomUpM_ `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (False, n) = VarE 'return `AppE` VarE n

-- * Top-down

generateTopDownClause :: (Name -> Type -> Name -> Name -> Name -> [ConRep] -> Exp) -> Name -> Type -> [ConRep] -> Clause
generateTopDownClause expFun clsVar headType cons
  = Clause [VarP tokenName, VarP funName, VarP elemName] (NormalB $ expFun clsVar headType tokenName funName elemName cons) []
  where tokenName = mkName "t"
        funName = mkName "f"
        elemName = mkName "e"

generateTopDownExpr :: Name -> Type -> Name -> Name -> Name -> [ConRep] -> Exp
generateTopDownExpr clsVar headType tokenName funName elemName cons
  = CaseE (VarE 'app `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''AppSelector `AppT` VarT clsVar `AppT` headType)))
                     `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE elemName)
          (map (createTopDownMatch tokenName funName) cons)

createTopDownMatch :: Name -> Name -> ConRep -> Match
createTopDownMatch tokenName funName (conName, args) 
  = Match (ConP conName (map VarP formalArgs)) 
          (NormalB $ foldl AppE (ConE conName) (map mapArgRep $ zip args formalArgs)) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        formalArgs = take (length args) argNames
        mapArgRep (Just t, n) = VarE 'topDown_ `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (Nothing, n) = VarE n

-- * Monadic top-down

generateTopDownMExpr :: Name -> Type -> Name -> Name -> Name -> [ConRep] -> Exp
generateTopDownMExpr clsVar headType tokenName funName elemName cons
  = InfixE (Just $ VarE 'appM `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''AppSelector `AppT` VarT clsVar `AppT` headType)))
                              `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE elemName)
           (VarE '(>>=))
           (Just $ LamE [VarP lamName] (CaseE (VarE lamName) (map (generateTopDownMMatch tokenName funName) cons)))
  where lamName = mkName "x"

generateTopDownMMatch :: Name -> Name -> ConRep -> Match
generateTopDownMMatch tokenName funName (conName, args)
  = Match (ConP conName (map VarP argNames)) 
          (NormalB $ case formalArgs of 
                       [] -> VarE 'return `AppE` ConE conName
                       fst:rest -> foldl (\base -> InfixE (Just base) (VarE '(<*>)) . Just) 
                                         (InfixE (Just $ ConE conName) (VarE '(<$>)) (Just $ mapArgRep fst)) 
                                         (map mapArgRep rest)
          ) []
  where argNames = take (length args) $ map (mkName . ("a"++) . show) [0..]
        formalArgs = zip args argNames
        mapArgRep (Just t, n) = VarE 'topDownM_ `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (Nothing, n) = VarE 'return `AppE` VarE n


-- * descend

-- | Creates the clause for the @descend_@ function for one constructor
generateDescendAppClause :: Name -> Type -> Name -> ConRep -> Clause
generateDescendAppClause clsVar headType tyName (conName, args) 
  = Clause [VarP tokenName, VarP funName, ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (generateDescendRecombineExpr clsVar conName tokenName funName (zip args argNames))) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"

generateDescendRecombineExpr :: Name -> Name -> Name -> Name -> [(Maybe Type, Name)] -> Exp
generateDescendRecombineExpr clsVar conName tokenName funName args
  = foldl AppE (ConE conName) (map mapArgRep args)
  where mapArgRep (Just t, n) = VarE 'appTD `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''AppSelector `AppT` VarT clsVar `AppT` t))) 
                                            `AppE` VarE tokenName `AppE` VarE funName 
                                            `AppE` (VarE 'descend_ `AppE` VarE tokenName `AppE` VarE funName) `AppE` VarE n
        mapArgRep (Nothing, n) = VarE n

-- * descendM

-- | Creates the clause for the @descendM_@ function for one constructor
generateDescendMAppClause :: Name -> Type -> Name -> ConRep -> Clause
generateDescendMAppClause clsVar headType tyName (conName, args) 
  = Clause [VarP tokenName, VarP funName, ConP conName (map VarP $ take (length args) argNames)] 
      (NormalB (generateDescendMRecombineExpr clsVar conName tokenName funName (zip args argNames))) []
  where argNames = map (mkName . ("a"++) . show) [0..]
        tokenName = mkName "t"
        funName = mkName "f"

generateDescendMRecombineExpr :: Name -> Name -> Name -> Name -> [(Maybe Type, Name)] -> Exp
generateDescendMRecombineExpr clsVar conName tokenName funName []
  = AppE (VarE 'return) (ConE conName)
generateDescendMRecombineExpr clsVar conName tokenName funName (fst:args)
  = foldl (\base -> InfixE (Just base) (VarE '(<*>)) . Just) 
          (InfixE (Just $ ConE conName) (VarE '(<$>)) (Just $ mapArgRep fst)) 
          (map mapArgRep args)
  where mapArgRep (Just t, n) = VarE 'appTDM `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''AppSelector `AppT` VarT clsVar `AppT` t))) 
                                             `AppE` VarE tokenName `AppE` VarE funName 
                                             `AppE` (VarE 'descendM_ `AppE` VarE tokenName `AppE` VarE funName) `AppE` VarE n
        mapArgRep (Nothing, n) = VarE 'return `AppE` VarE n

-- * Automatic definitions

-- | Creates the clause for the @smartTraverse_@ function for one constructor
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
          = VarE 'smartTraverse_ 
              `AppE` (VarE 'undefined `SigE` (ConT ''FlagToken `AppT` (ConT ''ClassIgnoresSubtree `AppT` VarT clsVar `AppT` t))) 
              `AppE` VarE tokenName `AppE` VarE funName `AppE` VarE n
        mapArgRep (Nothing, n) = VarE n

-- * Monadic automatic definitions

-- | Creates the clause for the @smartTraverseM_@ function for one constructor
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
          = VarE 'smartTraverseM_ 
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
getConRep :: PrimitiveMarkers -> Con -> ConRep
getConRep primitives (NormalC n args) 
  = (n, map (\(i,c) -> if IsPrimitive `elem` primitives || IgnoreArg n i `elem` primitives then Nothing else Just (snd c)) (zip [0..] args))
getConRep primitives (RecC n args) 
  = (n, map (\(i, (fldN,_,t)) -> if IsPrimitive `elem` primitives || IgnoreField fldN `elem` primitives || IgnoreArg n i `elem` primitives 
                                   then Nothing else Just t) 
          $ zip [0..] args)
getConRep primitives (InfixC (_,t1) n (_,t2)) 
  = (n, [ if IsPrimitive `elem` primitives || IgnoreArg n 0 `elem` primitives then Nothing else Just t1
        , if IsPrimitive `elem` primitives || IgnoreArg n 1 `elem` primitives then Nothing else Just t2
        ])
getConRep primitives (ForallC _ _ c) = getConRep primitives c
getConRep _ _ = error "GADTs are not supported"