{-# LANGUAGE RankNTypes #-}
-- |
module Pretty3 where

import           Data.Functor.Contravariant (Contravariant(..))
import           Data.Text (Text)
import qualified Data.Text as Text
import           Text.PrettyPrint.Annotated (Doc, (<+>), char, text, parens, annotate)

import           Annot
import           Ast3
import           Fix

newtype Pretty ann e = Pretty (e -> Doc ann)
ugly :: Pretty ann e -> e -> Doc ann
ugly (Pretty u) = u

instance Contravariant (Pretty ann) where
  contramap f (Pretty pretty) = Pretty (pretty . f)

class PrettyName name where
  prettyName :: Pretty ann name

instance PrettyName Text where
  prettyName = Pretty $ text . Text.unpack

expr :: (PrettyName name) => Pretty ann e -> Pretty ann (ExprF name e)
expr pe = Pretty $ \ exp -> case exp of
  LambdaF n e -> char '\\' <+> ugly prettyName n <+> text "->" <+> ugly pe e
  ParenF e -> parens (ugly pe e)
  IdentF n -> ugly prettyName n
  ApplyF e1 e2 -> ugly pe e1 <+> ugly pe e2

annot :: Pretty ann (f e) -> Pretty ann (AnnotF ann f e)
annot pfe = Pretty $ \ (Annot ann fe) -> annotate ann (ugly pfe fe)

decl :: (PrettyName name) => Pretty ann e -> Pretty ann (DeclF name e)
decl pe = Pretty $ \ (LetF n e) -> text "let" <+> ugly prettyName n <+> char '=' <+> ugly pe e

fixPretty :: (forall a. Pretty ann a -> Pretty ann (f a)) -> Pretty ann (F f)
fixPretty = cfixF

prettyExpr :: (PrettyName name) => Pretty ann (Expr ann name)
prettyExpr = fixPretty (annot . expr)

prettyDecl :: (PrettyName name) => Pretty ann (Decl ann name)
prettyDecl = annot (decl prettyExpr)
