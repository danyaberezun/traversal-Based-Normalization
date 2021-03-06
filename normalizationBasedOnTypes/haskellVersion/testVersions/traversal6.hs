--- like traversal5 but with representing bp as [Int, Int] 
import Data.List
import Data.String
import Debug.Trace

type Var    = String
type Vars   = [Var]
data B      = At As | CB Var As deriving (Eq, Show)
data A      = Lam Vars B deriving (Eq, Show)
type As     = [A]
--data LNF    = Root B deriving Show
data LNF    = Root A deriving Show
data TT = TTA A | TTB B deriving (Eq, Show)

zero = (Root (Lam [] (At [
	(Lam ["s", "z"] (CB "z" [])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
one = (Root (Lam [] (At [
	(Lam ["s", "z"] (CB "s" [(Lam [] (CB "z" []))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
two = (Root (Lam [] (At [
	(Lam ["s", "z"] (CB "s" [(Lam [] (CB "s" [(Lam [] (CB "z" []))]))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
three = (Root (Lam [] (At [
	(Lam ["s", "z"] (CB "s" [(Lam [] (CB "s" [(Lam [] (CB "s" [(Lam [] (CB "z" []))]))]))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
four = (Root (Lam [] (At [
	(Lam ["s", "z"] (CB "s" [(Lam [] (CB "s" [(Lam [] (CB "s" [(Lam [] (CB "s" [(Lam [] (CB "z" []))]))]))]))])),
	(Lam ["zz"] (CB "plus_one" [(Lam [] (CB "zz" []))])),
	(Lam [] (CB "zero" []))
	])))

succ0 = (Root (Lam [] (At [
	(Lam ["m", "s", "z"] (At [
							(Lam ["zpp"] (CB "m" [(Lam ["zp"] (CB "s" [(Lam [] (CB "zp" []))])), (Lam [] (CB "zpp" []))])),
							(Lam [] (CB "s" [(Lam [] (CB "z" []))]))])),
	-- zero
	(Lam ["s0", "z0"] (CB "z0" [])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
succ1 = (Root (Lam [] (At [
	(Lam ["m", "s", "z"] (At [
							(Lam ["zpp"] (CB "m" [(Lam ["zp"] (CB "s" [(Lam [] (CB "zp" []))])), (Lam [] (CB "zpp" []))])),
							(Lam [] (CB "s" [(Lam [] (CB "z" []))]))])),
	-- one
	(Lam ["s0", "z0"] (CB "s0" [(Lam [] (CB "z0" []))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
succ2 = (Root (Lam [] (At [
	(Lam ["m", "s", "z"] (At [
							(Lam ["zpp"] (CB "m" [(Lam ["zp"] (CB "s" [(Lam [] (CB "zp" []))])), (Lam [] (CB "zpp" []))])),
							(Lam [] (CB "s" [(Lam [] (CB "z" []))]))])),
	-- two
	(Lam ["s0", "z0"] (CB "s0" [(Lam [] (CB "s0" [(Lam [] (CB "z0" []))]))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
succ4 = (Root (Lam [] (At [
	(Lam ["m", "s", "z"] (At [
							(Lam ["zpp"] (CB "m" [(Lam ["zp"] (CB "s" [(Lam [] (CB "zp" []))])), (Lam [] (CB "zpp" []))])),
							(Lam [] (CB "s" [(Lam [] (CB "z" []))]))])),
	-- four
	(Lam ["s4", "z4"] (CB "s4" [(Lam [] (CB "s4" [(Lam [] (CB "s4" [(Lam [] (CB "s4" [(Lam [] (CB "z4" []))]))]))]))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))
succ_ = (Root (Lam [] (At [
	(Lam ["m", "s", "z"] (At [
							(Lam ["zpp"] (CB "m" [(Lam ["zp"] (CB "s" [(Lam [] (CB "zp" []))])), (Lam [] (CB "zpp" []))])),
							(Lam [] (CB "s" [(Lam [] (CB "z" []))]))])),
	-- arbitrary number
	(Lam ["s0", "z0"] (CB "number" [(Lam ["z01"] (CB "s0" [(Lam [] (CB "z01" []))])), (Lam [] (CB "z0" []))])),
	(Lam ["z1"] (CB "plus_one" [(Lam [] (CB "z1" []))])),
	(Lam [] (CB "zero" []))
	])))



createTraversalTree (Root a) = let t = TTA a in map postprocess (ctt [(t , (1, 0))] 1 (createBounders t))
	where
		postprocess [] = []
		postprocess (((TTA (Lam vs _)), bp) : xs) = (((TTA (Lam vs (At []))), bp) : (postprocess xs))
		postprocess (((TTB (At _)), bp) : xs) = (((TTB (At [])), bp) : (postprocess xs))
		postprocess (((TTB (CB v _)), bp) : xs) = (((TTB (CB v [])), bp) : (postprocess xs))


createBounders :: TT -> [(Var, A)]
createBounders (TTB (At as))      = concat $ map (\a -> createBounders (TTA a)) as
createBounders (TTB (CB _ as))    = concat $ map (\a -> createBounders (TTA a)) as
createBounders a@(TTA (Lam vs b)) = (map (\v -> (v, (Lam vs b))) vs) ++ (createBounders (TTB b))
getBounder :: Var -> [(Var, A)] -> [A]
getBounder v [] = []
getBounder v ((v1, tta):bs)
	| v == v1   = [tta]
	| otherwise = getBounder v bs
isFree :: Var -> [(Var, A)] -> Bool
isFree v bs = null $ getBounder v bs

--- -> Int -> --- current |t*n|
ctt :: [(TT, (Int, Int))] -> Int -> [(Var, A)] -> [[(TT, (Int, Int))]]
ctt tree@(n:_) len bounders = case fst n of
	TTB (At (a:as)) -> ctt (((TTA a), (len, 1)):tree) (len + 1) bounders
	TTA (Lam vs (At as)) -> ctt (((TTB (At as)), (0, 0)):tree) (len + 1) bounders
	TTA (Lam vs (CB v as)) -> ctt ((new_node, (new_bp, 0)):tree) (len + 1) bounders where
		(new_node, new_bp) = if isFree v bounders then (TTB (CB v as), 1) else (TTB (CB v as), f (tree) len)
		q_bounder = TTA (head $ getBounder v bounders)
		f [] llen = error "f : empty list"
		f ((term, (bp, bb)):tt) llen = if (term == q_bounder) then llen
							else f (drop (llen - bp + 1) ((term, (bp, bb)):tt)) (bp - 1)
	TTB (CB x as) ->
		if isFree x bounders then
			case length as of
				0 -> [(tree)]
				_ ->  if (length as == 0)
					then [(tree)]
					else concat $ snd $ mapAccumL (\acc a -> (acc + 1, ctt ((TTA a, (len, acc)) : tree) (len + 1) bounders)) 1 as
		else let
				(((TTA (Lam qs b)), bp_q), p, new_bp) =
					let pq = drop (len - fst(snd n)) (tree) in (head pq, head $ tail pq, (fst $ snd n) - 1)
				index = (get_n qs x)
			in case p of
				((TTB (At as_p))     , bp_p) -> if (index + 1 > length as_p) then [[]]
												else let new_node = get_child p (index + 1) in (ctt ((new_node, (new_bp, index + 1)):tree) (len + 1) bounders)
				((TTB (CB vs_p as_p)), bp_p) ->
					if isFree vs_p bounders then [(tree)]
					else if (index > length as_p) then [[]]
						else let new_node = get_child p index in ctt ((new_node, (new_bp, index)):tree) (len + 1) bounders
				_ -> error ((show p) ++ " q == " ++ (show (TTA (Lam qs b))))
			where
				get_child_as _ 0 = error ("get_child_as 0" ++ " " ++ (show (tree)))
				get_child_as (a:ass) 1 = TTA a
				get_child_as (a:ass) i = get_child_as ass (i-1)
				get_child_as [] _ = error ("get_child_as []" ++ "\n" ++ (show (tree)))
				get_child ((TTB (CB _ as_p)), _) i = get_child_as as_p i
				get_child ((TTB (At as_p)  , _)) i = get_child_as as_p i
				get_n (x:xs) y
					| x == y    = 1
					| otherwise = 1 + get_n xs y
	_ -> error "ctt: no such case"

--ex1 = (Root (At [
--		(Lam ["phi", "z"] (CB "phi" [(Lam ["x"] (CB "phi" [(Lam ["xPr"] (CB "x" [])), (Lam [] (CB "a" []))])), (Lam [] (CB "z" [(Lam [] (CB "a" []))]))])),
--		(Lam ["f", "y"] (CB "f" [(Lam [] (CB "g" [(Lam ["b"] (CB "b" [])), (Lam [] (CB "y" []))]))])),
--		(Lam ["w"] (CB "g" [(Lam ["bPr"] (CB "bPr" [])), (Lam [] (CB "w" []))]))
--		]))
--ex1 = (Root (Lam []
--	(At [
--		(Lam ["phi", "z"] (CB "phi" [(Lam ["x"] (CB "phi" [(Lam ["xPr"] (CB "x" [])), (Lam [] (CB "a" []))])), (Lam [] (CB "z" [(Lam [] (CB "a" []))]))])),
--		(Lam ["f", "y"] (CB "f" [(Lam [] (CB "g" [(Lam ["b"] (CB "b" [])), (Lam [] (CB "y" []))]))])),
--		(Lam ["w"] (CB "g" [(Lam ["bPr"] (CB "bPr" [])), (Lam [] (CB "w" []))]))
--		]))
--	)

--ex2 = (Root (At [
--		(Lam ["h", "z"] (CB "h" [(Lam ["x"] (CB "h" [(Lam ["xPr"] (CB "x" [])), (Lam [] (CB "a" []))])), (Lam [] (CB "z" [(Lam [] (CB "a" []))]))])),
--		(Lam ["f", "y"] (CB "f" [(Lam [] (CB "g" [(Lam [] (CB "y" []))]))])),
--		(Lam ["w"] (CB "g" [(Lam [] (CB "w" []))]))
--		]))


canReachBegin :: [(TT, (Int, Int))] -> Bool
canReachBegin []                 = False
canReachBegin ((_, (1, _)):_)    = True
canReachBegin ((tt, (bp, bb)):tts) = canReachBegin (drop (length(tts) - bp) tts)

myfilter :: [(TT, (Int, Int))] -> [(TT, (Int, Int))]
myfilter [] = []
myfilter tree@(t:ts)
	| canReachBegin tree = t:(myfilter ts)
	| otherwise = myfilter ts

getMaximalPaths :: [[(TT, (Int, Int))]] -> [[(TT, (Int, Int))]]
getMaximalPaths tree = map (\ts -> myfilter ts) tree

data Tree = Leaf (TT, (Int, Int)) | Node (TT, (Int, Int)) [Tree] deriving Show
createTree :: [[(TT, (Int, Int))]] -> Tree
f [] tt = tt
f (t:ts) (Leaf tt) = buildTreeFromList (tt:t:ts)
f (t:ts) (Node tt childs) =
	let i = getIndex childs t 1 in case i of
		0 -> Node tt ((buildTreeFromList (t:ts)):childs)
		_ -> Node tt (changeChild childs i ts)
	where
		getIndex [] y acc = 0
		getIndex ((Node x _):xs) y acc
			| x == y    = acc
			| otherwise = getIndex xs y (acc + 1)
		getIndex ((Leaf x):xs) y acc
			| x == y    = acc
			| otherwise = getIndex xs y (acc + 1)
		changeChild (c:cs) 1 ts = (f ts c):cs
		changeChild (c:cs) i ts = c : (changeChild cs (i-1) ts)

buildTreeFromList [t] = Leaf t
buildTreeFromList (t:ts) = Node t [(buildTreeFromList ts)]

createTree tts = let tts1 = map (\x -> reverse x) tts in
	foldl (\x y -> f (tail y) x) (buildTreeFromList $ head tts1) (tail tts1)

printTree1 t = do putStrLn $ printTree t "" where
	printTT (TTA (Lam vs _)) = "Lam " ++ show vs
	printTT (TTB (At _))     = "@ "
	printTT (TTB (CB v _))   = "Var " ++ show v
	printTree (Node (tt, (bp, bb)) ts) spaces = 
		spaces ++ "Node " ++ (printTT tt) ++ " " ++ show (bp, bb) ++ "\n" ++ foldl (\x t -> x ++ printTree t (spaces ++ "|  ")) "" ts
	printTree (Leaf (tt, (bp, bb))) spaces = 
		spaces ++ "Leaf " ++ (show (tt, (bp, bb))) ++ "\n"

--answer =  getMaximalPaths $ createTraversalTree ex1

--main = do
--	putStrLn "Example with g: o -> o"
--	printTree1 $ createTree $ getMaximalPaths $ createTraversalTree ex2
--	putStrLn "Example with g: (o -> o) -> o -> o"
--	printTree1 $ createTree $ getMaximalPaths $ createTraversalTree ex1

main = do
	putStrLn "zero"
	printTree1 $ createTree $ getMaximalPaths $ createTraversalTree zero
	putStrLn "four"
	printTree1 $ createTree $ getMaximalPaths $ createTraversalTree four
	putStrLn "succ4"
	printTree1 $ createTree $ getMaximalPaths $ createTraversalTree succ4
	putStrLn "succ_"
	printTree1 $ createTree $ getMaximalPaths $ createTraversalTree succ_
