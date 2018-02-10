-- module Parser (parseTerm) where
module Parser where

import Text.ParserCombinators.Parsec
import DataTypes
import Data.Char

variableIdentifier :: Parser String
variableIdentifier = many1 (noneOf " .\\()")

singleLambdaParser :: Parser Term
singleLambdaParser = 
    (do char '\\'  -- abstraction: \vars . e 
        spaces
        vl <- (endBy1 variableIdentifier spaces)
        char '.'
        spaces
        e <- lambdaParser
        return $ foldr (\x f -> x :>> f) e vl)
    <|> (do char '(' -- parenthesized expression: (e)
            e <- lambdaParser
            char ')'
            return e)
    <|> do v <- variableIdentifier -- simple variable: v
           return $ (:!!) v

lambdaParser :: Parser Term
lambdaParser = do l <- endBy1 singleLambdaParser spaces
                  return $ foldl1 (\f x -> f :@@ x) l

parseTerm :: String -> Maybe Term
parseTerm s = case parse lambdaParser "(unknown)" s of
  Right a -> Just a
  Left  _ -> Nothing
