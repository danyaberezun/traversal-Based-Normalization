module Testing where

import AuxiliaryFunctions
import DataTypes
import Data.Maybe (fromJust)
import Parser

-- testExamples returns list of unpassed tests
-- testExamples :: a list of expressions (strings) to be tested
--              -> a list of expected results
--              -> normalization procedure of type Exp -> Exp
--              -> Result
-- Returns a list of failed tests (pairs (expression, expected result))
testExamples :: [String] -> [String] -> (Exp -> Exp) -> [(String, String)]
testExamples exps ress normalizer =
  foldl (\ acc (a, b) ->
           let a' = normalizer . term2Exp . fromJust . parseTerm $ a
               b' = normalizer . term2Exp . fromJust . parseTerm $ b
           in if areExpsAlphaEq a' b' then acc else (a,b):acc)
        []
        (zip exps ress)
