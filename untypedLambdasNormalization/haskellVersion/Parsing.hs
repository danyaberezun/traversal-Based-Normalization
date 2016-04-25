module Parsing (parseExpr,identifier) where
import           Text.ParserCombinators.Parsec

import           DataTypes

identifier  = do
  c  <- letter
  cs <- many (alphaNum <|> char '_')
  return (c:cs)
parseExpr = try parseApp <|> parseExpr'
parseExpr' = parseAbs <|> parseVar <|> between (char '(') (char ')') parseExpr
parseVar = do
  name <- identifier
  return $ UVar name
parseApp = do
  t1 <- parseExpr'
  char '@'
  t2 <- parseExpr'
  return $ UApp t1 t2
parseAbs = do
  char '\\'
  name <- identifier
  char '.'
  expr <- parseExpr
  return $ UAbs name expr
