{-# LANGUAGE OverloadedStrings #-}
-- |
module Parse2 where

import qualified Control.Monad.RWS.Strict as S
import           Data.Text (Text)
import qualified Data.Text as Text
-- import Data.Void (Void)
import           Control.Applicative (pure, (<$>), (<*>), empty)
import           Control.Monad (void, unless)
import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NE
import           Data.List (intercalate)
import           Data.Semigroup

import           Text.Megaparsec hiding (runParser, parseTest)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C

data Span
  = Span SourcePos SourcePos
  deriving (Show, Eq, Ord)

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

type Name
  = Text
  -- Infix Span Text
  -- deriving (Show, Eq, Ord)

prettyName :: Name -> String
prettyName n = "'" <> Text.unpack n <> "'"

data Problem
  = IdentifierNotInScope Name Context
  deriving (Show, Eq, Ord)

identNotInScope :: Name -> Parser a
identNotInScope n = do
  ctx <- S.ask
  fancyFailure $ Set.fromList [ErrorCustom (IdentifierNotInScope n ctx)]

instance ShowErrorComponent Problem where
  showErrorComponent (IdentifierNotInScope ident scope) =
    prettyName ident <>
    " is not in scope.\n" <>
    prettyContext scope

-- | In scope names
type Context = [(Span, Name)]

prettyContext :: Context -> String
prettyContext = unlines . map (\(sp, n) -> prettyName n <> " (" <> prettySpan sp <> ")")

-- |
-- - R = local names
-- - S = global names
type Parser = ParsecT Problem Text (S.RWS Context () Context)

-- runParser :: Context -> Parser a -> Text
runParser
  :: Context
  -> Parser a
  -> Text
  -> Either (ParseError Char Problem) a
runParser inCtx parser input = a
  where
    rws = runParserT parser "" input
    (a, _, ()) = S.runRWS rws inCtx []

parseTest :: Show a => Context -> Parser a -> Text -> IO ()
parseTest c p t = case runParser c p t of
  Left errs -> putStrLn (parseErrorPretty errs)
  Right a -> print a

localScope :: Span -> Name -> Parser a -> Parser a
localScope s n = S.local ((s, n):)

checkScope :: Name -> Parser ()
checkScope n = do
  ns <- S.ask
  unless (n `elem` (map snd ns)) $
    identNotInScope n

withSpan :: Parser a -> Parser (Span, a)
withSpan p = do
  s1 <- NE.head . statePos <$> getParserState
  a <- p
  s2 <- NE.head . statePos <$> getParserState
  pure (Span s1 s2, a)

space :: Parser ()
space = L.space C.space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme space

symbol :: Text -> Parser Text
symbol = L.symbol space

equals :: Parser ()
equals = void $ symbol "="

arrow :: Parser ()
arrow = void $ symbol "->"

lambda :: Parser ()
lambda = void $ symbol "\\"

letnorec :: Parser ()
letnorec = void $ symbol "let"

letrec :: Parser ()
letrec = void $ symbol "letrec"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

name :: Parser Name
name = lexeme . try $ fmap Text.pack p
  where
    p = (:) <$> C.letterChar <*> many C.alphaNumChar

spanName :: Parser (Span, Name)
spanName = withSpan name

class AnnotSpan sp where
  getSpan :: sp -> Span

instance AnnotSpan Span where
  getSpan = id

-- instance (AnnotSpan ann) => AnnotSpan [ann] where
--   getSpan = sconcat . map getSpan

-- instance (AnnotSpan ann) => AnnotSpan (NE.NonEmpty ann) where
--   getSpan = sconcat . NE.map getSpan

data Decl ann
  = Let ann Name (Expr ann)
  -- ^ > let name = expression
  deriving (Show)

instance (AnnotSpan ann) => AnnotSpan (Decl ann) where
  getSpan (Let ann _ _) = getSpan ann

decl :: Parser (Decl Span)
decl = choice
  [ letDecl
  ]
  where
    -- letrecDecl = annot $ do
    --   letrec
    --   (span, name) <- spanName
    --   equals
    --   expression <- localScope span name expr
    --   pure $ LetRec n e
    letDecl = do
      (sp, ne) <- withSpan $ do
        letnorec
        name <- name
        equals
        expression <- expr
        pure (name, expression)
      pure $ uncurry (Let sp) ne

data Expr ann
  = Lambda ann Name (Expr ann)
  -- ^ > \ name -> expression
  | Paren ann (Expr ann)
  -- ^ > ( expression )
  | Ident ann Name
  -- ^ > name
  | Apply ann (Expr ann) (Expr ann)
  -- ^ > expression expression
  deriving (Show)

instance (AnnotSpan ann) => AnnotSpan (Expr ann) where
  getSpan (Lambda ann _ _) = getSpan ann
  getSpan (Paren ann _) = getSpan ann
  getSpan (Ident ann _) = getSpan ann
  getSpan (Apply ann _ _) = getSpan ann

expr :: Parser (Expr Span)
expr = fixupApply <$> some nonApp
  where
    fixupApply = foldl1 (\l r -> Apply (getSpan l <> getSpan r) l r)

    nonApp :: Parser (Expr Span)
    nonApp = choice
      [ exprLambda
      , exprParen
      , exprIdent
      ]

    exprLambda :: Parser (Expr Span)
    exprLambda = do
      (sp, (var, body)) <- withSpan $ do
        lambda
        (span, var) <- spanName
        arrow
        body <- localScope span var expr
        pure (var, body)
      pure $ Lambda span var body

    exprParen = do
      (sp, b) <- withSpan $ do
        parens expr
      pure $ Paren sp b

    exprIdent = do
      (sp, i) <- withSpan $ do
        ident <- name
        checkScope ident
        pure ident
      pure $ Ident sp i
