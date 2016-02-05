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

ex_R     = "g @ (\\ b . b)"
ex_P     = "\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y) "
ex_N     = "\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))"
ex_NPR   = "((\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))) @ (\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y))) @ (g @ (\\ n . n))"
ex_succ2 = "(\\ n . \\ s . \\ z . (n @ s) @ (s @ z)) @ (\\ p . \\ o . p @ (p @ o))"

--ex_succ = "\\ n . \\ s . \\ z . s @ ((n @ s) @ z)"
ex_succ = "(\\ n . \\ s . \\ z . s @ ((n @ s) @ z)) @ ( \\ s1 . \\ z1 . (m @ s1) @ z1)"

ex_mult = "\\ m . \\ n . \\ s . m @ (n @ s)"
ex_mult_3_2 = "((\\ m . \\ n . \\ s . m @ (n @ s)) @ (\\ w . \\ p . w @ (w @ (w @ p)))) @ (\\ d . \\ l . d @ (d @ l))"


-- will produce a type error
ex_omega =
  "(((\\ x . x @ x) @ (\\ y . y @ y)) @ (\\ z . z)) @ (\\ w . w)"

plus = "(\\ s . (\\ d . (\\ f . (\\ g . ((s @ f) @ ((d @ f) @ g))))))"
fib2 = "(\\ n . (\\ p4 . p4 @ (\\ x4 . \\ y4 . y4)) @ ((n @ (\\ p . ((\\ x3 . \\ y3 . \\ f3 . (f3 @ x3) @ y3) @ ((\\ p0 . p0 @ (\\ x6 . \\ y0 . y0)) @ p)) @ (((\\ m0 . \\ n0 . \\ f0 . \\ x0 . (m0 @ f0) @ ((n0 @ f0) @ x0)) @ ((\\ p1 . p1 @ (\\ x5 . \\ y5 . x5)) @ p)) @ ((\\ p2 . p2 @ (\\ x2 . \\ y2 . y2)) @ p)))) @ (((\\ x1 . \\ y1 . \\ f1 . (f1 @ x1) @ y1) @ (\\ e . \\ r . r)) @ (\\ q . \\ w . q @ w)))) @ (\\ z1 . \\ z2 . z1 @ (z1 @ z2))"
fib4 = "(\\ n . (\\ p4 . p4 @ (\\ x4 . \\ y4 . y4)) @ ((n @ (\\ p . ((\\ x3 . \\ y3 . \\ f3 . (f3 @ x3) @ y3) @ ((\\ p0 . p0 @ (\\ x6 . \\ y0 . y0)) @ p)) @ (((\\ m0 . \\ n0 . \\ f0 . \\ x0 . (m0 @ f0) @ ((n0 @ f0) @ x0)) @ ((\\ p1 . p1 @ (\\ x5 . \\ y5 . x5)) @ p)) @ ((\\ p2 . p2 @ (\\ x2 . \\ y2 . y2)) @ p)))) @ (((\\ x1 . \\ y1 . \\ f1 . (f1 @ x1) @ y1) @ (\\ e . \\ r . r)) @ (\\ q . \\ w . q @ w)))) @ (\\ z1 . \\ z2 . z1 @ (z1 @ (z1 @ (z1 @ z2))))"

-- UNTYPABLE!!!
-- NB: Unfortunately, W is powerfull enough to infer some type with no errors but in STLC they are untypable!
ex_9 = "(\\ x . x @ x) @ (\\ z . z)"
ex_10 = "\\ f . ((\\ x1 . \\ y1 . \\ p . (p @ x1) @ y1) @ (f @ (\\ x2 . \\ y2 . x2 @ y2))) @ (f @ (\\ x3 . \\ y3 . y3 @ x3))"

-- INCORRECT TYPE INFERECE
fib = "\\ n . (\\ p4 . p4 @ (\\ x4 . \\ y4 . y4)) @ ((n @ (\\ p . ((\\ x3 . \\ y3 . \\ f3 . (f3 @ x3) @ y3) @ ((\\ p0 . p0 @ (\\ x6 . \\ y0 . y0)) @ p)) @ (((\\ m0 . \\ n0 . \\ f0 . \\ x0 . (m0 @ f0) @ ((n0 @ f0) @ x0)) @ ((\\ p1 . p1 @ (\\ x5 . \\ y5 . x5)) @ p)) @ ((\\ p2 . p2 @ (\\ x2 . \\ y2 . y2)) @ p)))) @ (((\\ x1 . \\ y1 . \\ f1 . (f1 @ x1) @ y1) @ (\\ e . \\ r . r)) @ (\\ q . \\ w . q @ w)))"

-- name -> free_variables_types -> environment -> term_itself -> IO
run_algorithm :: String -> [(Var, SimpleType)] -> Environment -> String -> IO ()
run_algorithm name fv env term =
	let
		typed_version = ((\x -> postprocess x False) . (\x -> toEtaLong x (map (\(v, t) -> (v, simpleTypeToChType t)) fv) generateNames O False) . (typeTerm env)) term
		eta_long = generateLNF typed_version
		traversal_tree = normalize eta_long
		ela_long_beta_normal_form = toLambdaString traversal_tree
	in do
		putStrLn "============================================================================="
		putStrLn name
		putStrLn "============================================================================="
		putStrLn $ (++) "\nInput term: " term
		putStrLn "\nTyped Version"
		putStrLn $ show typed_version
		putStrLn "\nEta-long form"
		putStrLn $ show eta_long
		putStrLn "\nTraversals tree"
		putStrLn $ show traversal_tree
		putStrLn $ "Traversals length: " ++ (show . map length . snd . createTraversalTree) eta_long
		putStrLn "\nEta-long beta-normal form"
		putStrLn ela_long_beta_normal_form
		putStrLn "============================================================================="

main = let
		fv_empty = []
		env_empty = Map.empty
		fv_NPR = [("g", Arrow (Arrow (TyVar (show '\969')) (TyVar (show '\969')))
			(Arrow (TyVar (show '\969')) (TyVar (show '\969')))), ("a", (TyVar (show '\969')))]
		env_NPR = fst $ mapAccumL (\acc (v, t) -> (Map.insert (ULVar v) t acc, (v, t))) Map.empty fv_NPR
		fv_succ = [("m",
			Arrow
				(Arrow (TyVar (show '\969')) (TyVar (show '\969')))
				(Arrow (TyVar (show '\969')) (TyVar (show '\969')))
				),
			("g", Arrow
				(Arrow (TyVar (show '\969')) (TyVar (show '\969')))
				(TyVar (show '\969')))]
		env_succ = fst $ mapAccumL (\acc (v, t) -> (Map.insert (ULVar v) t acc, (v, t))) Map.empty fv_succ
	in do
		run_algorithm "NPR example" fv_NPR env_NPR ex_NPR
		run_algorithm "SUCC example" fv_succ env_succ ex_succ
		run_algorithm "SUCC TWO example" fv_empty env_empty ex_succ2
		run_algorithm "MULT example (already in normal form)" fv_empty env_empty ex_mult
		run_algorithm "MULT THREE TWO example" fv_empty env_empty ex_mult_3_2
		run_algorithm "FIB TWO example" fv_empty env_empty fib2
		run_algorithm "FIB FOUR example" fv_empty env_empty fib4