-- |
module Find where

import Text.Megaparsec.Pos

import Annot
import Ast3
import Fix

newtype Finder target =
  Finder (SourcePos -> target -> target)
  -- ^ Stack of things

find :: Finder target -> SourcePos -> target -> target
find (Finder f) = f

findExpr
  :: (AnnotSpan ann)
  => Finder e
  -> Finder (AnnotF ann (ExprF name) e)
findExpr fe = Finder $ \pos tgt -> case tgt of
  e -> _
