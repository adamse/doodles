{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- |
module Bi.Tc where

import Prelude hiding (lookup)
import Data.String

import Control.Monad.State.Strict
import Control.Monad.Except

import Bi.Syn
import Bi.Ctx as Ctx

newtype A = A String
newtype B = B String

newtype Fresh v = Fresh (v, v -> v)

instance Show v => Show (Fresh v) where
  show (Fresh (v, _)) = show v

data S a b = S
  { sCtx :: Ctx a b
  , sFreshTV :: Fresh a
  , sFreshV :: Fresh b
  , sTrace :: [(String, Ctx a b)]
  } deriving (Show)

newtype Error a b = Error String
 deriving (Show, Eq, IsString)

newtype Tc a b r =
  Tc (ExceptT (Error a b) (State (S a b)) r)
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadState (S a b)
    , MonadError (Error a b)
    )

runTc
  :: Fresh a -- ^ fresh typevariables
  -> Fresh b -- ^ fresh variables
  -> Ctx a b -- ^ initial context
  -> Tc a b r
  -> (Either (Error a b) r, S a b)
runTc freshA freshB ctx0 (Tc act) =
  runState (runExceptT act) s0
  where
    s0 = S
      { sCtx = ctx0
      , sFreshTV = freshA
      , sFreshV = freshB
      , sTrace = []
      }

runTc'
  :: Tc Integer Integer r
  -> (Either (Error Integer Integer) r, S Integer Integer)
runTc' =
  runTc (Fresh (1, succ)) (Fresh (0, pred)) emptyCtx

runIO tc = do
  let (res, s) = runTc' tc
  case res of
    Right r -> do
      mapM_ printTrace (reverse $ sTrace s)
      print r
    Left e -> do
      mapM_ printTrace (reverse $ sTrace s)
      print e
  where
    printTrace (s, ctx) = putStrLn s >> putStr "    " >> print ctx


tcErrMsg :: String -> Tc a b r
tcErrMsg = throwError . Error

traceTc :: String -> Tc a b ()
traceTc msg = do
  trace <- gets sTrace
  ctx <- gets sCtx
  modify (\s -> s { sTrace = (msg, ctx):trace })

traceW :: [String] -> Tc a b ()
traceW = traceTc . unwords

modifyCtx :: (Ctx a b -> Tc a b (Ctx a b)) -> Tc a b ()
modifyCtx f = do
  ctx <- gets sCtx
  ctx' <- f ctx
  modify (\s -> s { sCtx = ctx' })

-- | Run a Tc computation but restore the context afterwards
locally :: Tc a b r -> Tc a b r
locally act = do
  ctx <- gets sCtx
  res <- act
  modify (\s -> s { sCtx = ctx })
  return res

freshTV :: Tc a b a
freshTV = do
  Fresh (v, fv) <- gets sFreshTV
  modify' (\s -> s { sFreshTV = Fresh (fv v, fv)})
  return v

newTV :: Tc a b (Typ a)
newTV = do
  tv <- freshTV
  ctx <- gets sCtx
  modify (\s -> s { sCtx = CtxTV tv ctx })
  return (TV tv)

newEx :: Tc a b (Typ a)
newEx = do
  tv <- freshTV
  ctx <- gets sCtx
  modify (\s -> s { sCtx = CtxEx tv ctx })
  return (Ex tv)

newMarkEx :: Tc a b a
newMarkEx = do
  tv <- freshTV
  ctx <- gets sCtx
  modify (\s -> s { sCtx = CtxEx tv (CtxMark tv ctx) })
  return tv


freshV :: Tc a b b
freshV = do
  Fresh (v, fv) <- gets sFreshV
  modify' (\s -> s { sFreshV = Fresh (fv v, fv)})
  return v

newV :: Typ a -> Tc a b (Term a b)
newV ty = do
  v <- freshV
  ctx <- gets sCtx
  modify (\s -> s { sCtx = CtxV v ty ctx })
  return (V v)

lookupV
  :: (Show b, Eq b)
  => b
  -> Tc a b (Typ a)
lookupV v = do
  ctx <- gets sCtx
  case lookupVarCtx v ctx of
    Just t -> return t
    Nothing -> throwError (Error $ "lookup: Variable not bound: " ++ show v)

hasTV
  :: (Show a, Eq a)
  => a
  -> Tc a b ()
hasTV tv = do
  ctx <- gets sCtx
  if hasTVCtx tv ctx
    then return ()
    else tcErrMsg $ "hasTV: type-variable not in context: " ++ show tv

hasEV
  :: (Show a, Eq a)
  => a
  -> Tc a b ()
hasEV ev = do
  ctx <- gets sCtx
  if hasEVCtx ev ctx
    then return ()
    else tcErrMsg $ "hasEV: existential variable not in context: " ++ show ev

dropTV
  :: (Show a, Eq a)
  => Typ a
  -> Tc a b ()
dropTV (TV tv) = do
  ctx <- gets sCtx
  case dropCtxTV tv ctx of
    Just ctx' -> do
      modify' (\s -> s { sCtx = ctx' })
    Nothing ->
      throwError (Error $ "dropTV: Type-variable not bound: " ++ show tv)
dropTV ty = throwError (Error $ "dropTV: argument not a type-variable: " ++ show ty)

dropMark
  :: (Show a, Eq a)
  => a
  -> Tc a b ()
dropMark tv = do
  modifyCtx $ paraCtx (constAlg (tcErrMsg $ "dropMark: marker not in context: " ++ show tv))
    { paMark =
        (\tv' ctx' r -> if tv == tv'
          then return ctx'
          else r)
    }

dropEV
  :: (Show a, Eq a)
  => a
  -> Tc a b ()
dropEV tv = do
  modifyCtx $ paraCtx (constAlg (tcErrMsg $ "dropMark: marker not in context: " ++ show tv))
    { paEx =
      (\tv' ctx r -> if tv == tv'
        then return ctx
        else r)
    }

dropV
  :: (Show a, Show b, Eq b)
  => Term a b
  -> Tc a b ()
dropV (V v) = do
  ctx <- gets sCtx
  case dropCtxV v ctx of
    Just ctx' -> do
      modify' (\s -> s { sCtx = ctx' })
    Nothing ->
      throwError (Error $ "dropV: Variable not bound: " ++ show v)
dropV t = throwError (Error $ "dropV: argument not a variable: " ++ show t)

subst
  :: (Show a, Eq a)
  => Typ a
  -> Tc a b (Typ a)
subst ty = do
  ctx <- gets sCtx
  case substSolCtx ty ctx of
    Just ty' -> return ty'
    Nothing -> throwError (Error $ "subst: existential variable not bound in context: " ++ show ty)

solve
  :: (Show a, Eq a)
  => a
  -> Typ a
  -> Tc a b ()
solve a ty = modifyCtx $ paraCtx mAlg
  { paNil = (tcErrMsg $ "solve: existential variable not in context: " ++ show a)
  , paEx =
    (\a' ctx r -> if a == a'
      then return $ CtxSol a ty ctx
      else r)
  }

addExArr
  :: (Show a, Eq a)
  => a
  -> Tc a b (Typ a, Typ a)
addExArr a = do
  a1 <- freshTV
  a2 <- freshTV
  modifyCtx $ paraCtx mAlg
    { paNil = (tcErrMsg $ "addExArr: existential variable not bound: " ++ show a)
    , paEx =
      (\a' ctx' r -> if a == a'
        then -- Found: no more work to be done
          return (CtxSol a (Ex a1 :-> Ex a2) (CtxEx a1 (CtxEx a2 ctx')))
        else r)
    }
  return (Ex a1, Ex a2)
