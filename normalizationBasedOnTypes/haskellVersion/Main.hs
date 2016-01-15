import HindleyMilner
import ToEtaLong
import DataTypes
import Data.Char
import Data.List
import qualified Data.Map as Map
import Traversal

--generate names for variabes
generateNames :: [String]
generateNames = [a : if n == 0 then "" else show n | n <- [1..], a <- ['a'..'z']]
--generateNames = [a : if n == 0 then "" else show n | n <- [0..], a <- ['\1040'..'\1073']]

ex_R     = "g @ (\\ b . b)"
ex_P     = "\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y) "
ex_N     = "\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))"
ex_NPR   = "((\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))) @ (\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y))) @ (g @ (\\ n . n))"
ex_succ2 = "(\\ m . \\ s . \\ z . (m @ s) @ (s @ z)) @ (\\ p . \\ o . p @ (p @ o))"

ex_mult_3_2 = "((\\ m . \\ n . \\ s . m @ (n @ s)) @ (\\ w . \\ p . w @ (w @ (w @ p)))) @ (\\ d . \\ l . d @ (d @ l))"

-- will produce a type error
ex_omega =
  "(((\\ x . x @ x) @ (\\ y . y @ y)) @ (\\ z . z)) @ (\\ w . w)"

main = 
	let
		--freeVeriablesTypes = [("g", Arrow (Arrow (TyVar (show '\969')) (TyVar (show '\969')))
		--	(Arrow (TyVar (show '\969')) (TyVar (show '\969')))), ("a", (TyVar (show '\969')))]
		freeVeriablesTypes = []
		env = fst $ mapAccumL (\acc (v, t) -> (Map.insert (ULVar v) t acc, (v, t))) Map.empty freeVeriablesTypes
	in do
		putStrLn "typed term"
		putStrLn $ (show . typeTerm env) ex_mult_3_2
		putStrLn "\ntyped eta-expanded version"
		putStrLn $ (show . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		putStrLn "\neta-long form"
		putStrLn $ (show . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		putStrLn "\ntreaversals"
		putStrLn $ (printCT . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		putStrLn $ "traversal size == " ++ show ((length . head . snd . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2)
		putStrLn "abstract syntax tree"
		putStrLn $ (show . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		putStrLn "eta-long beta-normal for"
		putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_omega


		--putStrLn $ show $ ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R
		--putStrLn $ show $ ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_P
		--putStrLn $ show $ ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_N
		--putStrLn $ show $ ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_NPR
		--putStrLn $ show $ ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn $ show $ (generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R
		--putStrLn $ show $ (generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_P
		--putStrLn $ show $ (generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_N
		--putStrLn $ show $ (generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_NPR
		--putStrLn $ show $ (generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn $ show $ (normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R
		--putStrLn $ show $ (normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_P
		--putStrLn $ show $ (normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_N
		--putStrLn $ show $ (normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_NPR
		--putStrLn $ show $ (normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_NPR
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn ""
		--putStrLn $ show $ ((typeTerm env)) ex_RPR
		--putStrLn ""
		--putStrLn $ show $ ( (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_RPR
		--putStrLn ""
		--putStrLn $ show $ ((typeTerm env)) ex_succ2
		--putStrLn ""
		--putStrLn $ show $ ( (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn ""
		--putStrLn $ show $ ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn ""
		--putStrLn $ show $ (generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn ""
		--putStrLn $ show $ (createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2
		--putStrLn ""
		--putStrLn $ show $ (getMaximalPaths . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ2

--	normalize :: LNF -> Tree
--normalize = createTree . getMaximalPaths . createTraversalTree