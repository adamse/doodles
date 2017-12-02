-- |

module Syntax where

import qualified Data.Map as Map
import qualified Data.Text as Text

-- Bound machinery
import Bound
import Control.Monad (ap)
import Data.Functor.Classes
import Data.Deriving (deriveEq1, deriveOrd1, deriveShow1)

-- | Primitive types
data Type a
  = Nat
  | TVar a
  | Forall
  | Record (Map.Map Text (Type a)) (Maybe a)
