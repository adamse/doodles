{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
-- |
module Main where

import Prelude hiding (return, (>>=), (>>), fail, Monad)
import qualified Prelude as P

data Monad f =
  Monad {_return :: forall a. a -> f a
        ,_bind :: forall a b. f a -> (a -> f b) -> f b}

type M f a = Monad f -> f a

return :: a -> M f a
return a Monad{..} = _return a

(>>=) :: M f a -> (a -> M f b) -> M f b
(fa >>= k) m@Monad{..} = _bind (fa m) (\x -> k x m)

(>>) :: M f a -> M f b -> M f b
a >> b = a >>= (\_ -> b)

fail :: String -> M f a
fail str _ = error str

monad'IO :: Monad IO
monad'IO = Monad {_return = P.return, _bind = (P.>>=)}

monad'List :: Monad []
monad'List = Monad {_return = \a -> [a], _bind = flip concatMap}

putStrLn' :: String -> M IO ()
putStrLn' str _ = putStrLn str

thing :: M [] Integer
thing = do s <- const [1,2,3,4]
           return (s + 12)

main = (do putStrLn' "hej"
           return ()
       ) monad'IO
