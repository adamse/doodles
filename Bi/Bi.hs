{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}

{-# OPTIONS -Wno-unused-matches #-}
{-# OPTIONS -fdefer-typed-holes #-}
-- |
module Bi.Bi where

import Bound
-- import Control.Applicative
-- import Control.Monad (ap)
-- import Data.Functor.Classes
-- import Data.Foldable
-- import Data.Traversable
-- import Control.Monad.Except
import Data.List (notElem)


import Bi.Syn
-- import Ctx
import Bi.Tc

type TcC a b = (Show a, Show b, Eq a, Eq b)

-- | <=
check :: (TcC a b) => Term a b -> Typ a -> Tc a b ()

-- 1I
check Unit One = do
  traceTc $ "1I: Unit : One"
  return ()

-- AllI
check term (All s) = do
  traceTc $ "AllI: " ++ show term ++ " : " ++ show (All s)
  tv <- newTV
  let s' = instantiate1 tv s
  check term s'
  dropTV tv

-- ->I
check (Lam s) ty@(ty1 :-> ty2) = do
  traceTc $ "->I: " ++ show (Lam s) ++ " : " ++ show ty
  v <- newV ty1
  let s' = instantiate1 v s
  check s' ty2
  dropV v

-- Sub
check e bigB = do
  traceTc $ "Sub1: " ++ show e ++ " : " ++ show bigB
  bigA <- synth e
  traceTc $ "Sub2: " ++ show e ++ " : " ++ show bigA
  bigA' <- subst bigA
  bigB' <- subst bigB
  traceW ["Sub3:", show (bigA', bigB')]
  sub bigA' bigB'

synth' :: (TcC a b) => Term a b -> Tc a b (Typ a)
synth' term = do
  ty <- synth term
  subst ty

-- | =>
synth :: (TcC a b) => Term a b -> Tc a b (Typ a)

-- Var
synth (V v) = do
  t <- lookupV v
  traceTc $ "Var: " ++ show v ++ " : " ++ show t
  return t

-- Anno
synth (In term typ) = do
  check term typ
  traceW ["Anno:", show term, ":", show typ]
  return typ

-- 1I=>
synth Unit = do
  traceW ["1I=>: Unit : One"]
  return One

-- ->I=>
synth (Lam s) = do
  a <- newEx
  b <- newEx
  x <- newV a
  traceW ["->I=>1: (x, a, b) =", show (x, a, b)]
  let s' = instantiate1 x s
  traceW ["->I=>2: (s, s') =", show (s, s')]
  check s' b
  traceW ["->I=>3:", show s', ":", show b]
  dropV x
  traceTc $ "->I=>4: " ++ show (Lam s) ++ " : " ++ show (a :-> b)
  return (a :-> b)

-- ->E
synth (e1 :@ e2) = do
  traceTc $ "->E1: term: " ++ show (e1 :@ e2)
  bigA <- synth e1
  traceTc $ "->E2: " ++ show (e1, bigA)
  bigA' <- subst bigA
  app bigA' e2

-- synth term = _

-- | =>=>
app
  :: (TcC a b)
  => Typ a
  -> Term a b
  -> Tc a b (Typ a)

-- AllApp
app t@(All s) e = do
  traceW ["AllApp:", show (t, e)]
  ahat <- newEx
  let bigA = instantiate1 ahat s
  app bigA e

-- ExAp
app ev@(Ex a) e = do
  traceW ["ExAp:", show (ev, e)]
  (a1, a2) <- addExArr a
  check e a1
  return a2

-- ->App
app t@(bigA :-> bigC) e = do
  traceW ["->App:", show (t, e)]
  check e bigA
  return bigC

app typ1 term = _

-- | <:
sub
  :: (TcC a b)
  => Typ a
  -> Typ a
  -> Tc a b ()

-- <:Var
sub (TV a) (TV a')
  | a == a'
  = hasTV a

-- <:Unit
sub One One = return ()

-- <:Exvar
sub (Ex a) (Ex a')
  | a == a' =
    hasEV a

-- <:->
sub (a1 :-> a2) (b1 :-> b2) = do
  sub b1 a1
  a2' <- subst a2
  b2' <- subst b2
  sub a2' b2'

-- <:AllL
sub (All bigA) bigB = do
  a <- newMarkEx
  let bigA' = instantiate1 (Ex a) bigA
  sub bigA' bigB
  dropMark a

-- <:AllR
sub bigA (All bigB) = do
  a <- newTV
  let bigB' = instantiate1 a bigB
  sub bigA bigB'
  dropTV a

-- <:InstantiateL
sub (Ex a) bigA
  | a `elem` freeEV bigA
  = tcErrMsg $ "sub: <:InstantiateL: " ++ show a ++ " free in " ++ show bigA
  | otherwise = do
    traceW ["<:InstantiateL:", show (a, bigA)]
    hasEV a
    instantiateL a bigA


-- <:InstantiateR
sub bigA (Ex a) = do
  traceW ["<:InstantiateR:", show (bigA, a)]
  hasEV a
  if a `notElem` freeEV bigA
    then instantiateR bigA a
    else tcErrMsg $ "sub: <:InstantiateR: " ++ show a ++ " free in " ++ show bigA

instantiateL
  :: (TcC a b)
  => a
  -> Typ a
  -> Tc a b ()

-- InstLReach
instantiateL a (Ex b) = do
  traceW ["InstLReach:", show (a, b)]
  hasEV a
  hasEV b -- TODO: ensure that order is correct
  solve b (Ex a)

-- InstLArr
instantiateL a (bigA1 :-> bigA2) = do
  hasEV a
  (Ex a1, Ex a2) <- addExArr a
  instantiateR bigA1 a1
  bigA2' <- subst bigA2
  instantiateL a2 bigA2'

-- InstLAllR
instantiateL a (All bigB) = do
  hasEV a
  b <- newTV
  let bigB' = instantiate1 b bigB
  instantiateL a bigB'
  dropTV b

-- InstLSolve
instantiateL a ty
  | isMonoTy ty = do
    hasEV a
    locally $ do
      dropEV a
      wf ty
    solve a ty
  | otherwise = tcErrMsg $ "instantiateL: don't want: " ++ show a ++ " with " ++ show ty

instantiateR
  :: (TcC a b)
  => Typ a
  -> a
  -> Tc a b ()

-- InstRReach
instantiateR (Ex b) a = do
  hasEV a
  hasEV b -- TODO: ensure order
  solve b (Ex a)

-- InstRArr
instantiateR (bigA1 :-> bigA2) a = do
  hasEV a
  (Ex a1, Ex a2) <- addExArr a
  instantiateL a1 bigA1
  bigA2' <- subst bigA2
  instantiateR bigA2' a2

-- InstRAllL
instantiateR (All bigB) a = do
  hasEV a
  b <- newMarkEx
  let bigB' = instantiate1 (Ex b) bigB
  instantiateR bigB' a
  dropMark b

-- InstRSolve
instantiateR ty a
  | isMonoTy ty = do
    traceW ["InstRSolve:", show (ty, a)]
    hasEV a
    locally $ do
      dropEV a
      wf ty
    solve a ty
    traceW ["InstRSolve2:"]
  | otherwise = tcErrMsg $ "instantiateR: don't want: " ++ show a ++ " with " ++ show ty

wf
  :: (TcC a b)
  => Typ a
  -> Tc a b ()
wf (TV a) = hasTV a
wf (Ex a) = hasEV a
wf One = return ()
wf (a :-> b) = wf a >> wf b
wf (All bigA) = do
  a <- newTV
  let bigA' = instantiate1 a bigA
  wf bigA'
