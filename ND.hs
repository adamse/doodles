-- | Playing around with nondeterministic sorting
module ND where

type ND a = [a]

p :: a -> ND Bool
p _ = [True, False]

c :: a -> a -> ND Bool
c _ _ = [True, False]

-- | Let m be []: then we get all sublists
-- filterM p [1,2,3] == [[1,2,3],[2,3],[1,3],[3],[1,2],[2],[1],[]]
filterM
  :: Monad m
  => (a -> m Bool) -> [a] -> m [a]
filterM _ [] = return []
filterM p (x:xs) = do
  xs' <- filterM p xs
  t <- p x
  return $
    if t
      then x : xs'
      else xs'

insertM
  :: Monad m
  => (t -> t -> m Bool) -> t -> [t] -> m [t]
insertM _ y [] = return [y]
insertM cmp y (x:xs) = do
  t <- cmp y x
  if t
    then return (y : x : xs)
    else fmap (x :) (insertM cmp y xs)

sortM
  :: Monad m
  => (t -> t -> m Bool) -> [t] -> m [t]
sortM _ [] = return []
sortM cmp (x:xs) = do
  xs' <- sortM cmp xs
  insertM cmp x xs'

groupM
  :: Monad m
  => (t -> t -> m Bool) -> [t] -> m [[t]]
groupM _ [] = return []
groupM _ (x:[]) = return [[x]]
groupM cmp (x:y:ys) = do
  t <- cmp x y
  (y':ys') <- groupM cmp (y : ys)
  return
    (if not t
       then [x] : y' : ys'
       else (x : y') : ys')
