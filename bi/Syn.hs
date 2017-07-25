{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE BangPatterns #-}
-- |
module Syn where

import Bound
import Control.Monad (ap)
import Data.Functor.Classes
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)

newtype ExV = ExV Int
  deriving (Show, Eq, Ord)

data Typ a
  = One
  | TV !a
  | Ex !ExV
  | All (Scope () Typ a)
  | Typ a :-> Typ a
  deriving (Functor, Foldable, Traversable)

fall :: (Eq a) => a -> Typ a -> Typ a
fall tv = All . abstract1 tv

freeEV :: Typ a -> [ExV]
freeEV typ = case typ of
  One -> []
  TV _ -> []
  Ex a -> [a]
  a :-> b -> freeEV a ++ freeEV b
  All s -> (freeEV (fromScope s))

isMonoTy :: Typ a -> Bool
isMonoTy TV{} = True
isMonoTy Ex{} = True
isMonoTy One = True
isMonoTy (:->){} = True
isMonoTy _ = False

data Term a b
  = V b
  | Unit
  | Lam (Scope () (Term a) b)
  | Term a b :@ Term a b
  | In (Term a b) (Typ a)
  -- | Let (Term a b) (Scope () (Term a) b)
  deriving (Functor, Foldable, Traversable)

lam :: (Eq b) => b -> Term a b -> Term a b
lam v term = Lam $ abstract1 v term

instance Applicative Typ where
  pure = TV
  (<*>) = ap
instance Monad Typ where
  TV a >>= f = f a
  Ex v >>= _ = Ex v
  One >>= _ = One
  All s >>= f = All (s >>>= f)
  (t1 :-> t2) >>= f = (t1 >>= f) :-> (t2 >>= f)
deriveEq1 ''Typ
deriveOrd1 ''Typ
deriveShow1 ''Typ
instance Eq a => Eq (Typ a) where (==) = eq1
instance Ord a => Ord (Typ a) where compare = compare1
instance Show a => Show (Typ a) where showsPrec = showsPrec1

instance Applicative (Term a) where
  pure = V
  (<*>) = ap
instance Monad (Term a) where
  V b >>= f = f b
  Unit >>= _ = Unit
  Lam s >>= f = Lam (s >>>= f)
  (t1 :@ t2) >>= f = (t1 >>= f) :@ (t2 >>= f)
  In t ty >>= f = In (t >>= f) ty
  -- Let t s >>= f = Let (t >>= f) (s >>>= f)
deriveEq1 ''Term
deriveOrd1 ''Term
deriveShow1 ''Term
instance (Eq a, Eq b) => Eq (Term a b) where (==) = eq1
instance (Ord a, Ord b) => Ord (Term a b) where compare = compare1
instance (Show a, Show b) => Show (Term a b) where showsPrec = showsPrec1
