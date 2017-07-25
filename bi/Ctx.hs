{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
-- |
module Ctx where

import Bound

import Syn

-- data Elem a b
--   = ETV a
--   | EV b (Typ a)
--   | EEX a
--   | ESol a (Typ a) -- ^ invariant: 'Typ a' is monotype
--   | EMark a
--   deriving (Show, Eq)

-- newtype Ctx1 a b = Ctx [Elem a b]
--   deriving (Show, Eq)

-- type EAlg a b r =
--   ( a -> r
--   , b -> Typ a -> r
--   ,

-- paraCtx1

data Ctx a b
  = CtxNil
  | CtxTV !a (Ctx a b)
  | CtxV !b !(Typ a) (Ctx a b)
  | CtxEx !ExV (Ctx a b)
  | CtxSol !ExV (Typ a) (Ctx a b)
  | CtxMark !ExV (Ctx a b)
  deriving (Show, Eq)

emptyCtx :: Ctx a b
emptyCtx = CtxNil

data CtxAlg a b r =
  CtxAlg
  { paNil :: r -- ^ CtxNil
  , paTV :: (a -> Ctx a b -> r -> r) -- ^ CtxTV
  , paV :: (b -> Typ a -> Ctx a b -> r -> r) -- ^ CtxV
  , paEx :: (ExV -> Ctx a b -> r -> r) -- ^ CtxEx
  , paSol :: (ExV -> Typ a -> Ctx a b -> r -> r) -- ^ CtxSol
  , paMark :: (ExV -> Ctx a b -> r -> r) -- ^ CtxMark
  }

idAlg :: CtxAlg a b (Ctx a b)
idAlg = CtxAlg
  CtxNil
  (\a _ r -> CtxTV a r)
  (\b t _ r -> CtxV b t r)
  (\a _ r -> CtxEx a r)
  (\a ty _ r -> CtxSol a ty r)
  (\a _ r -> CtxMark a r)

mAlg :: Monad m => CtxAlg a b (m (Ctx a b))
mAlg = CtxAlg
  (return CtxNil)
  (\a _ r -> r >>= return . CtxTV a)
  (\b t _ r -> r >>= return . CtxV b t)
  (\a _ r -> r >>= return . CtxEx a)
  (\a ty _ r -> r >>= return . CtxSol a ty)
  (\a _ r -> r >>= return . CtxMark a)

const1 _ r = r
const2 _ _ r = r
const3 _ _ _ r = r

constAlg :: r -> CtxAlg a b r
constAlg r = CtxAlg
  r
  const2
  const3
  const2
  const3
  const2

paraCtx
  :: CtxAlg a b r
  -> Ctx a b
  -> r
paraCtx CtxAlg{..} ctx = go ctx
  where
    go ctx = case ctx of
      CtxNil -> paNil
      CtxTV a ctx' -> paTV a ctx' (go ctx')
      CtxV b t ctx' -> paV b t ctx' (go ctx')
      CtxEx a ctx' -> paEx a ctx' (go ctx')
      CtxSol a t ctx' -> paSol a t ctx' (go ctx')
      CtxMark a ctx' -> paMark a ctx' (go ctx')

mapTV
  :: (a -> x)
  -> Ctx a b
  -> Ctx x b
mapTV f = paraCtx CtxAlg
  { paNil = CtxNil
  , paTV = (\tv _ r -> CtxTV (f tv) r)
  , paEx = (\ex _ r -> CtxEx ex r)
  , paV = \v ty _ r -> CtxV v (fmap f ty) r
  , paSol = (\ex ty _ r -> CtxSol ex (fmap f ty) r)
  , paMark = (\ex _ r -> CtxMark ex r)
  }

lookupVarCtx
  :: (Eq b)
  => b
  -> Ctx a b
  -> Maybe (Typ a)
lookupVarCtx v = paraCtx (constAlg Nothing)
  { paV = (\v' t _ r -> if v == v' then Just t else r)
  }

hasTVCtx
  :: (Eq a)
  => a
  -> Ctx a b
  -> Bool
hasTVCtx tv = paraCtx (constAlg False)
  { paTV = (\tv' _ r -> tv == tv' || r)
  }

hasEVCtx
  :: (Eq a)
  => ExV
  -> Ctx a b
  -> Bool
hasEVCtx ev = paraCtx (constAlg False)
  { paEx = (\ev' _ r -> ev == ev' || r)
  }

lookupSolCtx
  :: (Eq a)
  => ExV
  -> Ctx a b
  -> Maybe (Typ a)
lookupSolCtx tv = paraCtx (constAlg Nothing)
  { paSol = (\tv' t _ r -> if tv == tv' then Just t else r)
  }

lookupExCtx
  :: (Eq a)
  => ExV
  -> Ctx a b
  -> Maybe ()
lookupExCtx tv = paraCtx (constAlg Nothing)
  { paEx = (\tv' _ r -> if tv == tv' then Just () else r)
  }

-- | Drop all context until type variable 'a' is reached. Nothing if
-- the tv is not in the context.
dropCtxTV
  :: (Eq a)
  => a
  -> Ctx a b
  -> Maybe (Ctx a b)
dropCtxTV tv = paraCtx (constAlg Nothing)
  { paTV = (\tv' ctx' r -> if tv == tv' then Just ctx' else r)
  }

dropCtxV
  :: (Eq b)
  => b -- ^ tv
  -> Ctx a b
  -> Maybe (Ctx a b)
dropCtxV v = paraCtx (constAlg Nothing)
  { paV = (\v' _ ctx' r -> if v == v' then Just ctx' else r)
  }

substSolCtx
  :: forall a b. (Eq a)
  => Typ a
  -> Ctx a b
  -> Maybe (Typ a)
substSolCtx t@TV{} _ = Just t
substSolCtx One _ = Just One
substSolCtx (t1 :-> t2) ctx = do
  t1' <- substSolCtx t1 ctx
  t2' <- substSolCtx t2 ctx
  return (t1' :-> t2')
substSolCtx (Ex tv) ctx
  | Just ty <- lookupSolCtx tv ctx
  = substSolCtx ty ctx
  | Just () <- lookupExCtx tv ctx
  = Just (Ex tv)
  | otherwise
  = Nothing
substSolCtx (All s) ctx = do
  let ns = fromScope s :: Typ (Var () a)
  let ctx' = mapTV F ctx :: Ctx (Var () a) b
  ns' <- substSolCtx ns ctx'
  let s' = toScope ns' :: Scope () Typ a
  return (All s')
