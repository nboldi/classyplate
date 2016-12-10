{-# LANGUAGE KindSignatures
           , TypeOperators
           , DataKinds
           , PolyKinds
           , TypeFamilies
           , UndecidableInstances
           #-}
module Data.Generics.ClassyPlate.TypePrune (ClassIgnoresSubtree, AppSelector, AppPruning, IgnoredFields) where

import GHC.Exts (Constraint)
import GHC.Generics
import Data.Type.Bool
import Data.Type.List
import GHC.TypeLits (Symbol, Nat)

-- | This type decides if the subtree of an element cannot contain an element that is transformed.
type family ClassIgnoresSubtree (cls :: * -> Constraint) (typ :: *) :: Bool where
  ClassIgnoresSubtree cls typ = Not (AnySelected cls (MemberTypes typ))

-- | Instantiate this type family to signal what elements does your operation operate on.
-- If @AppSelector c t@ is True, there should be a @c t@ instance. AppSelector should be
-- a total type function for a given class, at least for all the types that can possibly
-- accessed.
type family AppSelector (c :: * -> Constraint) (a :: *) :: Bool

type family AppPruning (c :: * -> Constraint) (a :: *) :: Bool

-- | This type family sets which fields should not be traversed when trying to generate
-- automatically pruned versions of classy traversal.
type family IgnoredFields (t :: *) :: [Either (Symbol, Nat) Symbol]

type family AnySelected (c :: * -> Constraint) (ls :: [*]) :: Bool where
  AnySelected c (fst ': rest) = AppSelector c fst || AnySelected c rest
  AnySelected c '[] = False


type MemberTypes t = MemberTypesAcc '[] '[t]

type family MemberTypesAcc (visited :: [*]) (open :: [*]) :: [*] where
  MemberTypesAcc visited '[] = visited
  MemberTypesAcc visited (open ': rest) = MemberTypesAcc (open ': visited) (Difference (open ': visited) (DirectMembers open))

type family DirectMembers (typ :: *) :: [*] where
  DirectMembers t = GetElementTypes t (Rep t)

type family GetElementTypes (t :: *) (typ :: * -> *) :: [*] where 
  GetElementTypes t (D1 md cons) = GetElementTypesCons t cons

type family GetElementTypesCons (t :: *) (typ :: * -> *) where 
  GetElementTypesCons t (C1 (MetaCons consName pref flag) flds) = GetElementTypesFields consName 0 t flds
  GetElementTypesCons t (c1 :+: c2) = GetElementTypesCons t c1 `Union` GetElementTypesCons t c2

type family GetElementTypesFields (cons :: Symbol) (n :: Nat) (t :: *) (typ :: * -> *) where 
  GetElementTypesFields cons n t (fld1 :*: fld2) 
    = -- only one field should be on the lhs
      GetElementTypesFields cons n t fld1 `Union` GetElementTypesFields cons n t fld2
  GetElementTypesFields cons n t (S1 (MetaSel fld unp str laz) (Rec0 innerT)) 
    = If (IsIgnoredField cons n fld (IgnoredFields t)) '[] '[innerT]
  GetElementTypesFields cons n t U1 = '[]

type family IsIgnoredField (cons :: Symbol) (fldNum :: Nat) (fldSelector :: Maybe Symbol)
                           (ignored :: [Either (Symbol, Nat) Symbol]) :: Bool where
  IsIgnoredField cons fldNum (Just sel) ignored = Find (Right sel) ignored || Find (Left '(cons, fldNum)) ignored
  IsIgnoredField cons fldNum Nothing ignored = Find (Left '(cons, fldNum)) ignored
