{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
-- |
module MonadAlgebra where

import Data.Set

-- I for Initial monad algebra
data I a = Ret a | Join (I (I a))

-- GADT to see the types easier
data Free f a where
  Pure :: a -> Free f a
  Free :: f (Free f a) -> Free f a

-- Fancy Fix -- what does it really mean?
data Fix a b = In (a (Fix a) b)

unFix :: Fix a b -> a (Fix a) b
unFix (In a) = a

type I' a = Fix Free a

m :: I a -> I' a
m (Ret a) = In (Pure a)
m (Join iia) = In (Free (m (fmap (unFix . m) iia)))

m' :: I' a -> I a
m' (In (Pure a)) = Ret a
m' (In (Free iia)) = Join (m' (fmap (m' . In) iia))

instance Functor I where
  fmap f (Ret a) = Ret $ f a
  fmap f (Join iia) = Join $ fmap (fmap f) iia

instance Functor (Fix Free) where
  fmap f (In (Pure a)) = In (Pure (f a))
  fmap f (In (Free fa)) = In (Free (fmap (fmap f) fa))

instance Applicative I where
  pure = Ret
  Ret f <*> ia = fmap f ia
  Join iif <*> ia = fmap ($ ia) undefined

-- h :: Monad m => I a -> m a
-- h (Ret a) = return a
-- h (Join iia) = _


-- h :: M ((->) b) a -> I a
-- h (Pure a) = Ret a
-- h (Free fma) = fma _

instance Functor f => Functor (Free f) where
  fmap f (Pure a) = Pure (f a)
  fmap f (Free fa) = Free (fmap (fmap f) fa)

instance Functor f => Applicative (Free f) where
  pure = Pure


-- instance Functor f => Monad (M f) where
--   return = Pure

-- data M f a where
--   Pure :: a -> M f a
--   Free :: M (f (M a) -> M f a
