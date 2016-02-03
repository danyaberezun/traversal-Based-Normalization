import HindleyMilner
import ToEtaLong
import DataTypes
import Data.Char
import Data.List
import qualified Data.Map as Map
import Traversal

--generate names for variabes
generateNames :: [String]
generateNames = [a : a : if n == 0 then "" else show n | n <- [1..], a <- ['a'..'z']]
--generateNames = [a : if n == 0 then "" else show n | n <- [0..], a <- ['\1040'..'\1073']]

ex_R     = "g @ (\\ b . b)"
ex_P     = "\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y) "
ex_N     = "\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))"
ex_NPR   = "((\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))) @ (\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y))) @ (g @ (\\ n . n))"
ex_succ2 = "(\\ m . \\ s . \\ z . (m @ s) @ (s @ z)) @ (\\ p . \\ o . p @ (p @ o))"

--ex_succ = "\\ n . \\ s . \\ z . s @ ((n @ s) @ z)"
ex_succ = "(\\ n . \\ s . \\ z . s @ ((n @ s) @ z)) @ ( \\ s1 . \\ z1 . (m @ s1) @ z1)"

ex_mult_3_2 = "((\\ m . \\ n . \\ s . m @ (n @ s)) @ (\\ w . \\ p . w @ (w @ (w @ p)))) @ (\\ d . \\ l . d @ (d @ l))"

-- will produce a type error
ex_omega =
  "(((\\ x . x @ x) @ (\\ y . y @ y)) @ (\\ z . z)) @ (\\ w . w)"

plus = "(\\ s . (\\ d . (\\ f . (\\ g . ((s @ f) @ ((d @ f) @ g))))))"
fib2 = "(\\ n . (\\ p4 . p4 @ (\\ x4 . \\ y4 . y4)) @ ((n @ (\\ p . ((\\ x3 . \\ y3 . \\ f3 . (f3 @ x3) @ y3) @ ((\\ p0 . p0 @ (\\ x6 . \\ y0 . y0)) @ p)) @ (((\\ m0 . \\ n0 . \\ f0 . \\ x0 . (m0 @ f0) @ ((n0 @ f0) @ x0)) @ ((\\ p1 . p1 @ (\\ x5 . \\ y5 . x5)) @ p)) @ ((\\ p2 . p2 @ (\\ x2 . \\ y2 . y2)) @ p)))) @ (((\\ x1 . \\ y1 . \\ f1 . (f1 @ x1) @ y1) @ (\\ e . \\ r . r)) @ (\\ q . \\ w . q @ w)))) @ (\\ z1 . \\ z2 . z1 @ (z1 @ (z1 @ (z1 @ z2))))"

-- UNTYPABLE!!!
ex_9 = "(\\ x . \\ y . x @ y) @ (\\ z . z)"

main = 
	let
		--freeVeriablesTypes = [("g", Arrow (Arrow (TyVar (show '\969')) (TyVar (show '\969')))
		--	(Arrow (TyVar (show '\969')) (TyVar (show '\969')))), ("a", (TyVar (show '\969')))]
		--freeVeriablesTypes = [("s1", Arrow (TyVar (show '\969')) (TyVar (show '\969'))),
		--					  ("z1", (TyVar (show '\969')))]
		--freeVeriablesTypes = [("m",
		--	Arrow
		--		(Arrow (TyVar (show '\969')) (TyVar (show '\969')))
		--		(Arrow (TyVar (show '\969')) (TyVar (show '\969')))
		--		),
		--	("g", Arrow
		--		(Arrow (TyVar (show '\969')) (TyVar (show '\969')))
		--		(TyVar (show '\969')))]
		freeVeriablesTypes = []
		env = fst $ mapAccumL (\acc (v, t) -> (Map.insert (ULVar v) t acc, (v, t))) Map.empty freeVeriablesTypes
	in do
		--putStrLn "typed term"
		--putStrLn (show (parse parseExpr "" (filter (not . isSpace) ex_succ)))
		--putStrLn "eta-long"
		--putStrLn $ (show . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ
		--putStrLn $ (show . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ

		----succ
		--putStrLn "typed term"
		--putStrLn (show (parse parseExpr "" (filter (not . isSpace) ex_succ)))
		--putStrLn "typed term"
		--putStrLn $ (show . (typeTerm env)) ex_succ
		--putStrLn "typed term"
		--putStrLn $ (show . (typeTerm3 env)) ex_succ
		--putStrLn "typed term"
		--putStrLn $ (show . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ
		--putStrLn "typed term"
		--putStrLn $ (show . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_succ

		---- ex_R
		--putStrLn "typed term"
		--putStrLn (show (parse parseExpr "" (filter (not . isSpace) ex_R)))
		--putStrLn "typed term"
		--putStrLn $ (show . (typeTerm env)) ex_R
		--putStrLn "typed term"
		--putStrLn $ (show . (typeTerm3 env)) ex_R
		--putStrLn "typed term"
		--putStrLn $ (show . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R
		--putStrLn "typed term"
		--putStrLn $ (show . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_R

		---- ex_9
		--putStrLn "typed term"
		--putStrLn (show (parse parseExpr "" (filter (not . isSpace) ex_9)))
		--putStrLn "typed term"
		--putStrLn $ (show . (typeTerm env)) ex_9
		--putStrLn ""
		--putStrLn $ (show . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_9
		--putStrLn ""
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_9
		--putStrLn ""
		--putStrLn $ (show . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_9
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_9
		--putStrLn ""
		--putStrLn $ show $ (createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_9
		--putStrLn ""
		--putStrLn $ (printCT . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_9

		-- fib2
		putStrLn "1"
		putStrLn (show (parse parseExpr "" (filter (not . isSpace) fib2)))
		putStrLn "2"
		putStrLn $ (show . (typeTerm env)) fib2
		putStrLn "3"
		putStrLn $ (show . (typeTerm3 env)) fib2
		putStrLn "4"
		putStrLn $ (show . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) fib2
		putStrLn "5"
		putStrLn $ (show . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) fib2
		putStrLn "6"
		putStrLn $ (show . map length . snd. createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) fib2
		putStrLn "7"
		putStrLn $ (show . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) fib2
		putStrLn "8"
		putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) fib2

		--putStrLn "\ntyped eta-expanded version"
		--putStrLn $ (show . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		--putStrLn "\neta-long form"
		--putStrLn $ (show . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		--putStrLn "\ntreaversals"
		--putStrLn $ (printCT . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		--putStrLn $ "traversal size == " ++ show ((length . head . snd . createTraversalTree . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2)
		--putStrLn "abstract syntax tree"
		--putStrLn $ (show . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2
		--putStrLn "eta-long beta-normal for"
		--putStrLn $ (toLambdaString . normalize . generateLNF . (\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) freeVeriablesTypes) generateNames O False) . (typeTerm env)) ex_mult_3_2

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