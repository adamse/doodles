{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}
-- |
module Ast3 where

import           Data.Deriving (deriveShow2)
import           Data.Functor.Classes
import           Data.Semigroup
import           Data.Text (Text)
import qualified Data.Text as Text

import           Annot
import           Fix

data DeclF name e
  = LetF name e
  -- ^ > let name = expression
  deriving (Show, Functor)

deriveShow2 ''DeclF
instance (Show name) => Show1 (DeclF name) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

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

pattern Lambda ann name body = Annot ann (LambdaF name body)
pattern Paren ann body = Annot ann (ParenF body)
pattern Ident ann name = Annot ann (IdentF name)
pattern Apply ann e1 e2 = Annot ann (ApplyF e1 e2)

type ParseName = Text
type ParseAnn = Span

prettyParseName :: ParseName -> String
prettyParseName n = "'" <> Text.unpack n <> "'"

type Expr ann name = F (AnnotF ann (ExprF name))
type Decl ann name = AnnotF ann (DeclF name) (Expr ann name)
