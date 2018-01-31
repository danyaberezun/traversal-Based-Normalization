module UNP where

import Tests
import DataTypes
import qualified Data.List as L
import qualified Data.Map.Strict as Map
--import Debug.Trace
trace _ b = b

-- =================
--     Tests
-- =================

runTestSet :: IO ()
runTestSet = putStrLn . show $ foldr 
  (\(t,r) acc -> (&&) acc (testEq r (normalize t))) True tests

tests = zip testSet expectedResults
testSet = [varity2, mul22, testR]
expectedResults = [Lam "x1" (Lam "x11" (Lam "sva2" (Lam "zva2" (App 0 (App 0 (V "x1") (V "sva2")) (App 0 (App 0 (V "x11") (V "sva2")) (V "zva2")))))),
  App 0 (V "S") (App 0 (V "S") (App 0 (V "S") (App 0 (V "S") (V "Z")))),
  Lam "y" (App 0 (V "z") (V "y"))]

-- ========================================
--     Some case of equality check ....
-- ========================================

testEq :: Exp -> Exp -> Bool
testEq e1 e2 = expEq (todeBruijn e1) (todeBruijn e2) where
  expEq :: Exp -> Exp -> Bool
  expEq (Bound _  i ) (Bound _  j ) = i == j
  expEq (Lam   _  e1) (Lam   _  e2) = expEq e1 e2
  expEq (App _ e1 e2) (App _ e3 e4) = expEq e1 e3 && expEq e2 e4
  expEq (FREE x) (FREE y) = x == y
  expEq _ _ = False
  todeBruijn :: Exp -> Exp
  todeBruijn e = fst . snd $ ff where
    (tdb, ind) = todeBruijn' [] e 0
    ff         = fixFREE Map.empty tdb (ind + 1)
  fixFREE :: Map.Map String Int -> Exp -> Int -> (Map.Map String Int, (Exp, Int))
  fixFREE m (FREE x) i = case Map.lookup x m of
      Just j  -> (m, ((FREE (show j)), i))
      Nothing -> (Map.insert x i m, ((FREE (show i)), i+1))
  fixFREE m e@(Bound _ _) i = (m, (e, i))
  fixFREE m (Lam x e) i = 
    let (m', (e', i')) = fixFREE m e i
    in (m', (Lam x e', i'))
  fixFREE m (App k e1 e2) i = 
    let (m' , (e1', i' )) = fixFREE m  e1 i
        (m'', (e2', i'')) = fixFREE m' e2 i'
    in (m'', (App k e1' e2', i''))
  fixFREE m (V v) i = error $ "V"
  todeBruijn' vars (V x)         acc = (defind x vars 1, acc)
  todeBruijn' vars (App i e1 e2) acc = 
    let (e1', acc')  = todeBruijn' vars e1 acc
        (e2', acc'') = todeBruijn' vars e2 acc'
    in (App i e1' e2', acc'')
  todeBruijn' vars (Lam x e)     acc = 
    let (e', acc') = todeBruijn' (x:vars) e (acc+1)
    in (Lam x e', acc')
  todeBruijn' vars (FREE  x)      acc = (FREE x, acc)
  todeBruijn' vars (Bound x _)    acc = (defind x vars 1, acc)
  defind x []       j = FREE x
  defind x (y:vars) j = if x==y then Bound x j else defind x vars (j+1)


-- ======================================
--   Run the traversal generator
-- ======================================
runTraverser :: Exp -> H
runTraverser e =
  let e'    = (adddeBruijn e)
      alpha = False
      bh    = []
      ch    = []
      h     = [It e' alpha bh ch]
  in eval e' alpha bh ch h

-- =============================================
--   Normalize expression ny traversal
-- =============================================
normalize :: Exp -> Exp
normalize = fst . displ . runext where
  displ ((It e _ _ _):hs) =
    let (e1, cont) = displ hs
    in case e of
      Lam x _ -> (Lam x e1, cont)
      App _ _ _ -> let (e2, cont') = displ cont in (App 0 e1 e2, cont')
      Bound x _ -> (V x, hs)
      FREE y -> (FREE y, hs)
  runext = extens . reverse . renameVariables . runTraverser
  renameVariables :: H -> H
  renameVariables h = renameVariables' (length h) h where
    renameVariables' :: Int -> H -> H
    renameVariables' 0 [] = []
    renameVariables' l ((It (Bound x i) alpha bh ch):h) = it':h' where
      it' = (It (Bound (show (getBinderIndex i bh)) i) alpha bh ch)
      h' = renameVariables' (l-1) h
    renameVariables' l ((It (Lam x e) alpha bh ch):h) = it':h' where
      it' = (It (Lam (show l) e) alpha bh ch)
      h' = renameVariables' (l-1) h
    renameVariables' l (it:h) = it:(renameVariables' (l-1) h)
  getBinderIndex :: Int -> H -> Int
  getBinderIndex 1 h = length h
  getBinderIndex i ((It _ _ bh _):_) = getBinderIndex (i-1) bh
  extens h = snd . unzip . trace (show ii) $ filter (\(i,_) -> notElem i ii) hh where
    hh = snd $ L.mapAccumL (\acc x -> (acc+1, (acc,x))) 1 h
    ii :: [Int]
    ii = extens' h 1 []
  extens' :: H -> Int -> [Int] -> [Int]
  extens' [] _ acc = acc
  extens' ((It (Lam _ _) True  bh []):hs) i acc = extens' hs (i+1) acc
  extens' ((It (Lam _ _) False bh ch):hs) i acc = extens' hs (i+1) acc
  extens' ((It (Lam _ _) True  bh ch):hs) i acc = extens' hs (i+1) (i : (length ch) : acc)
  extens' ((It (Bound x j) _   bh ch):hs) i acc = 
    extens' hs (i+1) (if elem (getBinderIndex j bh) acc then i : acc else acc)
  extens' ((It _ _  bh ch):hs) i acc = extens' hs (i+1) acc


-- =================
-- Traversal History
-- ================= 
type H    = [Item]  -- Item = top of current history
type CH   = H  --  Control history (realises continuation)
type BH   = H  --  Binder  history (realises environment)

data Item = It Exp Bool BH CH

-- ======================================= 
--   EVALUATION OF EXPRESSIONS 
-- =======================================

eval :: Exp -> Bool -> BH -> CH -> H -> H
eval (FREE x) _ _ ch h         =  apk (FREE x) ch h
eval (Bound x i) alpha bh ch h =  lookvar i alpha bh ch h
eval (Lam x e0) alpha _ ch h   = 
   if alpha then apk (Lam x e0) ch h 
            else eval e0 False h ch ((It e0 False h ch):h)
eval (App i e1 e2) _ bh ch h   = 
                 eval e1 True bh h ((It e1 True  bh h):h)
eval _ _ _ _ h                 =  h

-- ====================================
--     BINDER HISTORY: find variable 
-- ====================================

lookvar :: Int -> Bool -> BH -> CH -> H -> H

lookvar 1 alpha ((It _ True _ ch'):h') ch h =
 case ch' of 
  (It apn _ bh _):_ -> evaloperand apn alpha bh ch h
  _                 -> error ("bad ch: " ++ show ch)

lookvar 1 _ ((It _ False _ ch'):h') ch h = apk (Bound "VAR?" 1) ch h 
 
lookvar i alpha ((It _ _ bh' _):_) ch h  = lookvar (i - 1) alpha bh' ch h

-- ======================================================== 
--   APPLY CONTROL HISTORY (i.e., EXPRESSION CONTINUATION)
-- ========================================================

apk :: Exp -> CH -> H -> H
apk e ch h = 
 
 case e of
  (Lam x e0) -> case ch of
                 [] -> h
                 ((It apn alpha bh ch'):_) -> eval e0 alpha h ch' ((It e0 alpha h ch'):h)

  _          ->  case ch of
                 [] -> h
                 ((It apn alpha bh ch'):_) -> evaloperand apn False bh ch' h
--
-- =======================================================================
--  "the trick" : Find operand of dynamic application, and make it static  
-- =======================================================================

evaloperand (App i e1 e2) alpha bh ch h = 
                  eval e2 alpha bh ch ((It e2 alpha bh ch):h)

evaloperand e alpha bh ch h = error ("EXPECTED APPLICATION, BUT FOUND: " ++ (top e))

-- ============= 
-- ADD deBruijn INDICES
-- ============= 

adddeBruijn :: Exp -> Exp
adddeBruijn e = deBaux [] e

deBaux vars (V x)         = deBfind x vars 1
deBaux vars (App i e1 e2) = App i (deBaux vars e1) (deBaux vars e2)
deBaux vars (Lam x e)     = Lam x (deBaux (x:vars) e) 
deBaux vars _             = Bugexp

deBfind x []       j = FREE x
deBfind x (y:vars) j = if x==y then Bound x j else deBfind x vars (j+1)

-- ================
-- Input and output format stuff
-- ================

top :: Exp -> String
top (App i e1 e2)  = "@" ++ (numstr i)
top (V x)          = x
top (Lam x e)      = "Lam " ++ x
top (FREE x)       = "FREE " ++ x
top (Bound x j)    = "Bvar " ++ (numstr j) ++ " " ++ x
top Bugexp         = " BUG!! "

numstr :: Int -> String
numstr n = if n<10 then [['0'..'9']!!n] 
                   else (numstr (div n 10)) ++ (numstr (mod n 10))

display h = trace("\nHISTORY=\n" ++ daux h ++ "\n") $ "end-of-history"

daux [] = []
daux ((It e alpha bh ch):h) =
  (top e) ++ " bh " ++ " alpha = " ++ show alpha 
  ++ " control back pointer " ++ numstr (length ch)

instance Show Exp where
  showsPrec _ (App n e1 e2) s =
    "(@" ++ show n ++ " " ++ show e1 ++ " " ++ show e2 ++ ")" ++ s
  showsPrec _ (Lam a e) s     = "(Lam " ++  a ++ "." ++ show e ++ ")" ++ s
  showsPrec _ (V x) s         =  x ++ s
  showsPrec _ (FREE x) s      = "(FREE " ++ x ++ ")" ++ s
  showsPrec _ (Bound x j) s   = "(Bvar " ++ x ++ " " ++ numstr j ++ ")" ++ s
  showsPrec _ Bugexp s        = "Bugexp" ++ s

instance Show Item where
  show (It e alpha bh h) = doLen (top e) 10 ++ " | "
    ++ doLen (show alpha) 5  ++ " | "
    ++ doLen (show (length bh)) 5 ++ " | "
    ++ doLen (show (length h)) 5
  showsPrec _ it s = "Item " ++ show it ++ s

doLen s l
  | l <= len  = s
  | otherwise = s ++ [a | a <- " ", j <- [1..(l - len)]]
  where len = length s
