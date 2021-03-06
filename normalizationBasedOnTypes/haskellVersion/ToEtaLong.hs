module ToEtaLong (generateLNF, postprocess, toEtaLong) where

import DataTypes

-- ==============================================================
--  Main function : toEtaLong that generates an eta-long form
--  from typed lambda expression
-- ==============================================================

-- postprocess to concat neiber LamChlbdas
-- Bool -- is itselft an ardument or not
postprocess :: ChL -> Bool -> ChL2
postprocess (LamChl anvs1 (LamChl anvs2 t)) _ = postprocess (LamChl (anvs1 ++ anvs2) t) False
postprocess (LamChl anvs t) _ = LamChl2 anvs (postprocess t False)
postprocess (App (App t11 t12) t2) b = let pp = postprocess t11 False in
	case pp of
		App2 t3 ts3 -> App2 t3 (ts3 ++ [postprocess t12 True, postprocess t2 True])
		LamChl2 [] t -> case b of
			True -> LamChl2 [] (App2 t [postprocess t12 True, postprocess t2 True])
			False -> (App2 t [postprocess t12 True, postprocess t2 True])
		LamChl2 v t -> case b of
			True  -> LamChl2 [] (App2 (LamChl2 v t) [postprocess t12 True, postprocess t2 True])
			False -> (App2 (LamChl2 v t) [postprocess t12 True, postprocess t2 True])
		V2 v -> case b of
			True  -> LamChl2 [] (App2 (V2 v) [postprocess t12 True, postprocess t2 True])
			False -> App2 (V2 v) [postprocess t12 True, postprocess t2 True]
		_ -> error $ "postprocess : error??? " ++ show pp ++ "!!!" ++ (show (App (App t11 t12) t2)) ++ " b = " ++ show b
postprocess (App (LamChl [] t1) t2) True  = LamChl2 [] (App2 (postprocess t1 True) [(postprocess t2 True)])
postprocess (App (LamChl [] t1) t2) False = postprocess (App t1 t2) False
postprocess (App (LamChl anvs t1) t2) _ = App2 (postprocess (LamChl anvs t1) True) [(postprocess t2 True)]
postprocess (App t1 t2) b = App2 (postprocess t1 b) [(postprocess t2 True)]
postprocess (V v) _ = V2 v
postprocess t _ = error $ "postprocess error: " ++ show t

generateLNF :: ChL2 -> LNF
generateLNF chl = case chl of
	LamChl2 _ _ -> Root (generateLNFA chl)
	App2    _ _ -> Root (Lam [] (generateLNFB chl))
	V2      v   -> Root (Lam [] (CB v []))
	where
	generateLNFA (LamChl2 anvs t) = Lam (fst $ unzip anvs) (generateLNFB t)
	generateLNFA t = error $ "generateLNFA : given not a Lam: " ++ show t
	generateLNFB (App2 (V2 v) t2) = CB v (map generateLNFA t2)
	generateLNFB (App2 t1 t2) = At ((generateLNFA t1) : map generateLNFA t2)
	generateLNFB (V2 v) = CB v [] 
	generateLNFB t = error $ "generateLNFB : given not a B: " ++ show t


toTypeLamChlbda [] acc = error "toTypeLamChlbda : empty anvs"
toTypeLamChlbda ((v, vt):[]) acc = P vt acc
toTypeLamChlbda ((v, vt):vs) acc = P vt (toTypeLamChlbda vs acc)

getType :: ChL -> AnnVars -> ChType
getType (LamChl [] t) banvs   = getType t banvs
getType (LamChl anvs t) banvs = toTypeLamChlbda anvs (getType t (anvs ++ banvs))
getType (App t1 t2) banvs =
	let (P tt1 tt2) = P (getType t1 banvs) (getType t2 banvs)
	in case tt1 of
		(P tt11 tt12) -> if tt11 == tt2 then tt12 else error $ "getType: App : type error in application " ++ show tt11 ++ " =/= " ++ show tt2
		_ -> error $ "getType: type error: tt1 " ++ show tt1 ++ " is applied to type tt2: " ++ show tt2
-- Var case
getType (V v) banvs = lookup v banvs where
	lookup :: Var -> AnnVars -> ChType
	lookup y [] = error $ "getType : lookup : untyped variable" ++ show y
	lookup y ((x, tx):xs)
		| x == y    = tx
		| otherwise = lookup y xs

toEtaLong :: ChL -> AnnVars -> [String] -> ChType -> Bool -> ChL
toEtaLong t p1 p2 p3 p4 = fst $ toEtaLong' t p1 p2 True
toEtaLong' :: ChL -> AnnVars -> [String] -> Bool -> (ChL, [String])
toEtaLong' (LamChl anvs t) banvs free_names _ = let (t', nfn) = toEtaLong' t (anvs ++ banvs) free_names True
	in (LamChl anvs t', nfn)
toEtaLong' t@(App t1 t2) banvs free_names False =
	let
		(t1', nfn1) = toEtaLong' t1 banvs free_names False
		(t2', nfn2) = toEtaLong' t2 banvs nfn1 True
	in (App t1' t2', nfn2)
toEtaLong' t@(V v) banvs free_names False = (LamChl [] (V v), free_names)
toEtaLong' t banvs free_names True = case getType t banvs of
	O         -> toEtaLong' t banvs free_names False
	P ty1 ty2 ->
		let new_name = head free_names
		in toEtaLong' (LamChl [(new_name, ty1)] (App t (V new_name))) banvs (tail free_names) True