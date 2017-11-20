{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
-- |
module Parse3 where

import qualified Control.Monad.RWS.Strict as S
import           Data.Text (Text)
import qualified Data.Text as Text
-- import Data.Void (Void)
import           Control.Applicative (pure, (<$>), (<*>), empty)
import           Control.Monad (void, unless)
import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NE
import           Data.Semigroup
import           Data.Function (fix)
import           Data.Functor.Compose (Compose(..))

import           Text.Megaparsec hiding (runParser, parseTest)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C

import           Ast3

data Problem
  = IdentifierNotInScope ParseName Context
  deriving (Show, Eq, Ord)

identNotInScope :: ParseName -> Parser a
identNotInScope n = do
  ctx <- S.ask
  fancyFailure $ Set.fromList [ErrorCustom (IdentifierNotInScope n ctx)]

instance ShowErrorComponent Problem where
  showErrorComponent (IdentifierNotInScope ident scope) =
    prettyName ident <>
    " is not in scope.\n" <>
    prettyContext scope

-- | In scope names
type Context = [(Span, ParseName)]

prettyContext :: Context -> String
prettyContext = unlines . map (\(sp, n) -> prettyName n <> " (" <> prettySpan sp <> ")")

-- |
-- - R = local names
-- - S = global names
type Parser = ParsecT Problem Text (S.RWS Context () Context)

fixParser :: (forall a. Parser a -> Parser (f a)) -> Parser (F f)
fixParser pp = fix (fmap (fmap In) pp) --fix (fmap (fmap In) pp)

composeParser
  :: (Functor f, Functor g)
  => (forall e. Parser e -> Parser (f e))
  -> (forall e. Parser e -> Parser (g e))
  -> (forall e. Parser e -> Parser (Compose f g e))
composeParser p1 p2 = fmap Compose . p1 . p2

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

localScope :: Span -> ParseName -> Parser a -> Parser a
localScope s n = S.local ((s, n):)

checkScope :: ParseName -> Parser ()
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

-- letrec :: Parser ()
-- letrec = void $ symbol "letrec"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

name :: Parser ParseName
name = lexeme . try $ fmap Text.pack p
  where
    p = (:) <$> C.letterChar <*> many C.alphaNumChar

spanName :: Parser (Span, ParseName)
spanName = withSpan name

-- instance (AnnotSpan ann) => AnnotSpan [ann] where
--   getSpan = sconcat . map getSpan

-- instance (AnnotSpan ann) => AnnotSpan (NE.NonEmpty ann) where
--   getSpan = sconcat . NE.map getSpan

annotParser :: Parser e -> Parser (AnnotF ParseAnn e)
annotParser p = uncurry Annot <$> withSpan p

decl :: Parser e -> Parser (DeclF ParseName e)
decl e = choice
  [ letDecl
  ]
  where
    letDecl = do
      letnorec
      (span, name) <- spanName
      equals
      expression <- localScope span name e
      pure $ LetF name expression

expr :: Parser e -> Parser (ExprF ParseName e)
expr e = choice
  [ exprLambda
  , exprParen
  , exprIdent
  ]
  where
    exprLambda = do
      lambda
      (span, var) <- spanName
      arrow
      body <- localScope span var e
      pure $ LambdaF var body

    exprParen = do
      b <- parens e
      pure $ ParenF b

    exprIdent = do
      ident <- name
      checkScope ident
      pure $ IdentF ident


parseDecl :: Parser (Decl ParseAnn ParseName)
parseDecl = annotParser . decl $ parseExpr

parseExpr :: Parser (Expr ParseAnn ParseName)
parseExpr = foldApply (fixParser (some `composeParser` (annotParser `composeParser` expr)))

foldApply
  :: (Semigroup ann)
  => Parser (F (Compose [] (Compose (AnnotF ann) (ExprF name))))
  -> Parser (F (Compose (AnnotF ann) (ExprF name)))
foldApply =
  fmap $
  cata $
  In .
  foldl1 (\l r ->
    Compose $
    Annot
      (getAnn (getCompose l) <> getAnn (getCompose r))
      (ApplyF (In l) (In r))) .
  getCompose
