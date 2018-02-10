module Main where

import AuxiliaryFunctions
import LambdaExpressionExamples
import Testing
import UNP
import UNPNormalizer
import Data.Maybe (fromJust)

-- main run tests from LambdaExpressionExamples.hs
main :: IO ()
main = putStrLn testingResult where
  testingResult   =
    if areTestesPassed
    then "All tests from LambdaExpressionExamples are succesfully passed"
    else "Fail to pass some test: look into Testing.hs"
  areTestesPassed = null $ testExamples examples expectedResults
    (term2Exp . extractNormalFormFromTheTraversal . unp)
