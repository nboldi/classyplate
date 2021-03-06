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
import GHC.TypeLits (Symbol, Nat)

type family Union xs ys where
  Union '[] ys = ys
  Union (x ': xs) ys = Insert x (Union xs ys)

type family Find x ys where
  Find x '[]       = 'False
  Find x (x ': ys) = 'True
  Find x (y ': ys) = Find x ys

type family Insert a xs where
  Insert a '[]       = (a ': '[])
  Insert a (a ': xs) = (a ': xs)
  Insert a (x ': xs) = x ': (Insert a xs)

--------------------------------

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

type family MemberTypes (typ :: *) :: [*] where
  MemberTypes t = GetMemberTypes '[] t

type family GetMemberTypes (checked :: [*]) (typ :: *) :: [*] where
  GetMemberTypes checked t = GetElementTypes t checked (Rep t)

type family GetElementTypes (t :: *) (checked :: [*]) (typ :: * -> *) :: [*] where 
  GetElementTypes t checked (D1 md cons) = GetElementTypesCons t checked cons

type family GetElementTypesCons (t :: *) (checked :: [*]) (typ :: * -> *) where 
  GetElementTypesCons t checked (C1 (MetaCons consName pref flag) flds) = GetElementTypesFields consName 0 t checked flds
  GetElementTypesCons t checked (c1 :+: c2) = GetElementTypesCons t checked c1 `Union` GetElementTypesCons t checked c2

type family GetElementTypesFields (cons :: Symbol) (n :: Nat) (t :: *) (checked :: [*]) (typ :: * -> *) where 
  GetElementTypesFields cons n t checked (fld1 :*: fld2) 
    = -- only one field should be on the lhs
      GetElementTypesFields cons n t checked fld1 `Union` GetElementTypesFields cons n t checked fld2
  GetElementTypesFields cons n t checked (S1 (MetaSel fld unp str laz) (Rec0 innerT)) 
    = If (IsIgnoredField cons n fld (IgnoredFields t)) '[] (GetElementTypesField checked (Find innerT checked) innerT)  
  GetElementTypesFields cons n t checked U1 = '[]

type family IsIgnoredField (cons :: Symbol) (fldNum :: Nat) (fldSelector :: Maybe Symbol)
                           (ignored :: [Either (Symbol, Nat) Symbol]) :: Bool where
  IsIgnoredField cons fldNum (Just sel) ignored = Find (Right sel) ignored || Find (Left '(cons, fldNum)) ignored
  IsIgnoredField cons fldNum Nothing ignored = Find (Left '(cons, fldNum)) ignored

type family GetElementTypesField (checked :: [*]) (inChecked :: Bool) (typ :: *) where 
  GetElementTypesField checked True typ = '[]
  GetElementTypesField checked False typ = Insert typ (GetMemberTypes (typ ': checked) typ)
