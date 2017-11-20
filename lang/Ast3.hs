{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
-- |
module Ast3 where

import           Data.Deriving (deriveShow1, deriveShow2)
import           Data.Functor.Classes
import qualified Data.List.NonEmpty as NE
import           Data.Semigroup
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Functor.Compose (Compose(..))

import           Text.Megaparsec.Pos
-- import qualified Text.Megaparsec.Char.Lexer as L
-- import qualified Text.Megaparsec.Char as C


data Span
  = Span SourcePos SourcePos
  deriving (Show, Eq, Ord)

initialSpan f = Span i i
  where
    i = initialPos f

instance Semigroup Span where
  Span s11 s12 <> Span s21 s22
    = Span (min s11 s21) (max s12 s22)

prettySpan :: Span -> String
prettySpan (Span (SourcePos n l1 c1) (SourcePos _ l2 c2))
  | null n = showLC
  | otherwise = n <> ":" <> showLC
  where
    showLC =
      show (unPos l1) <> ":" <>
      show (unPos c1) <> "-" <>
      show (unPos l2) <> ":" <>
      show (unPos c2)

data AnnotF ann e =
  Annot ann e
  deriving (Show, Functor)

deriveShow2 ''AnnotF
instance (Show ann) => Show1 (AnnotF ann) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

data DeclF name e
  = LetF name e
  -- ^ > let name = expression
  deriving (Show, Functor)

deriveShow2 ''DeclF
instance (Show name) => Show1 (DeclF name) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

-- type Decl ann name = AnnotF ann (DeclF name) (Expr ann name)

pattern Let ann name body = Annot ann (LetF name body)

data ExprF name e
  = LambdaF name e
  -- ^ > \ name -> expression
  | ParenF e
  -- ^ > ( expression )
  | IdentF name
  -- ^ > name
  | ApplyF e e
  -- ^ > expression expression
  deriving (Show, Functor)

deriveShow2 ''ExprF

instance (Show name) => Show1 (ExprF name) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

newtype F f = In (f (F f))

out :: F f -> f (F f)
out (In f) = f

cata :: Functor f => (f a -> a) -> F f -> a
cata f = c where c = f . fmap c . out

deriving instance (Show (f (F f))) => Show (F f)

-- type Expr ann name = F (AnnotF ann (ExprF name))

pattern Lambda ann name body = (Annot ann (LambdaF name body))
pattern Paren ann body = (Annot ann (ParenF body))
pattern Ident ann name = (Annot ann (IdentF name))
pattern Apply ann e1 e2 = (Annot ann (ApplyF e1 e2))

class Annot n where
  type Ann n
  getAnn :: n -> Ann n

instance Annot (AnnotF ann e) where
  type Ann (AnnotF ann e) = ann
  getAnn (Annot ann _) = ann

instance (Annot (f (F f))) => Annot (F f) where
  type Ann (F f) = Ann (f (F f))
  getAnn (In ann) = getAnn ann

class AnnotSpan sp where
  getSpan' :: sp -> Span

instance AnnotSpan Span where
  getSpan' = id

getSpan :: (Annot annot, AnnotSpan (Ann annot)) => annot -> Span
getSpan = getSpan' . getAnn

type ParseName = Text
type ParseAnn = Span

prettyName :: ParseName -> String
prettyName n = Text.unpack $ "'" <> n <> "'"

type Expr ann name = F (Compose (AnnotF ann) (ExprF name))
type Decl ann name = AnnotF ann (DeclF name (Expr ann name))
