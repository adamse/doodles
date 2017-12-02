{-# LANGUAGE OverloadedStrings #-}
-- |
module Parse where

import qualified Data.Text as Text
import Data.Text (Text)
import qualified Control.Monad.RWS.Strict as S
-- import Data.Void (Void)
import Control.Applicative (pure, (<$>), (<*>), empty)
import Control.Monad (void, unless)
import qualified Data.Set as Set

import Text.Megaparsec hiding (runParser, parseTest)
import qualified Text.Megaparsec.Char.Lexer as L
import qualified Text.Megaparsec.Char as C

type Name = Text

data Problem
  = IdentifierNotInScope Name
  deriving (Show, Eq, Ord)

identNotInScope :: Name -> Parser a
identNotInScope n = fancyFailure $ Set.fromList [ErrorCustom (IdentifierNotInScope n)]

instance ShowErrorComponent Problem where
  showErrorComponent = show

-- | In scope names
type Context = [Name]

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

localScope :: Name -> Parser a -> Parser a
localScope n = S.local (n:)

checkScope :: Name -> Parser ()
checkScope n = do
  ns <- S.ask
  unless (n `elem` ns) $ identNotInScope n

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

data Decl
  = Let Name Expr
  -- ^ > let name = expression
  | LetRec Name Expr
  -- ^ > letrec name = expression
  deriving (Show)

decl :: Parser Decl
decl = choice
  [ letrecDecl
  , letnorecDecl
  ]
  where
    letrecDecl = do
      letrec
      name <- name
      equals
      expression <- localScope name expr
      pure $ LetRec name expression
    letnorecDecl = do
      letnorec
      name <- name
      equals
      expression <- expr
      pure $ Let name expression

data Expr
  = Lambda Name Expr
  -- ^ > \ name -> expression
  | Paren Expr
  -- ^ > ( expression )
  | Ident Name
  -- ^ > name
  | Apply Expr Expr
  -- ^ > expression expression
  deriving (Show)

expr :: Parser Expr
expr = foldl1 Apply <$> some nonApp
  where
    nonApp = choice
      [ exprLambda
      , exprParen
      , exprIdent
      ]

    exprLambda = do
      lambda
      var <- name
      arrow
      body <- localScope var expr
      pure $ Lambda var body

    exprParen = do
      body <- parens expr
      pure $ Paren body

    exprIdent = do
      ident <- name
      checkScope ident
      pure $ Ident ident
