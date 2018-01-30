module UNP where

import qualified Data.List as L  
--import Debug.Trace
trace _ b = b

type Var = String 

data Exp   = 
      V Var           -- bound variable in input expression
    | FREE Var        -- free variable
    | Bound Var Int   -- bound variable plus deBruijn tag
    | App Int Exp Exp -- application
    | Lam Var Exp     -- abstraction
    | Bugexp 
  deriving (Eq)

mul22 = App 1 (App 2 b1 (App 5 b2 (V "S"))) (V "Z")
b1 = Lam "s1" (Lam "z1" (App 3 (V "s1") (App 4 (V "s1") (V "z1"))))
b2 = Lam "s2" (Lam "z2" (App 6 (V "s2") (App 7 (V "s2") (V "z2"))))

-- ==============================
--     MAIN
-- ==============================
main :: IO()             
main = putStrLn . show . normalize $ mul22

-- ====================================================================== 
--    Display: function displ extracts normal form from the traversal
-- ====================================================================== 

normalize = fst . displ . runext where
  displ ((It e _ _ _):hs) =
    let (e1, cont) = displ hs
    in case e of
      Lam x _ -> (Lam x e1, cont)
      App _ _ _ -> let (e2, cont') = displ cont in (App 0 e1 e2, cont')
      _ -> (e, hs)
  runext e = extens (reverse (eval [It e False emptybh []]))
  extens h = snd . unzip . trace (show ii) $ filter (\(i,_) -> notElem i ii) hh where
    hh = snd $ L.mapAccumL (\acc x -> (acc+1, (acc,x))) 1 h
    ii :: [Int]
    ii = extens' h 1
  extens' :: H -> Int -> [Int]
  extens' [] _ = []
  extens' ((It (Lam _ _) True  bh []):hs) i = extens' hs (i+1)
  extens' ((It (Lam _ _) False bh ch):hs) i = extens' hs (i+1)
  extens' ((It (Lam _ _) True  bh ch):hs) i = i : (length ch) : (extens' hs (i+1))
  extens' ((It (V x) _   bh ch):hs) i = 
    case UNP.lookup bh x of 
      (FREE _, _) -> extens' hs (i+1)
      _           -> i : (extens' hs (i+1))
  extens' ((It _ _  bh ch):hs) i = extens' hs (i+1)

-- =================================== 
--    RUN PROGRAM
-- ===================================

run :: Exp -> String
run e = trace (raux (reverse (eval [It e False emptybh []])) 1) $ ""

raux :: H -> Int -> String
raux [] t     = ""
raux (it:h) t = 
 "\n" ++ doLen (show t) 3 ++ show it ++ raux h (t+1)

-- =================

-- =================
-- Traversal History
-- ================= 

type H    = [Item]  -- Item = top of current history
type CH   = H  --  Control history (realises continuation)
type BH   = H  --  Binder  history (realises environment)

data Item = It Exp Bool BH CH
 
  -- Item form: It e1 alpha bh ch where flag alpha = True iff M contains  
  -- e1 @ e2, i.e., alpha = True iff subexpression e1 is applied to e2

-- =================================== 
--    EVALUATE EXPRESSION
-- ===================================

eval :: H -> H 

eval h =
  case h of 
    []                  -> [It Bugexp False  emptybh []]
    (It e alpha bh ch):_ ->
      --trace("\nEVAL Item: e = " ++ show (top e) ++ " alpha = " ++ show alpha ++ " |bh| = " ++ show (length bh) ++ show (length ch)) $
      case e of
        (V x)       -> case UNP.lookup bh x of 
          (FREE _, _)  -> apk ch e h
          (e', bh')  -> let it = It e' alpha bh' ch
                         in eval (it:h) 
        (Lam x e0) -> if alpha then apk ch e h
                               else eval ((It e0 False h ch):h)
        (App i e1 e2) -> let it = It e1 True bh h in eval (it:h)
        _  -> h

-- =================================== 
--    EFFECT: APPLY EXPR. CONTINUATION
-- ===================================

apk :: H -> Exp -> BH -> H
apk ch e h = trace("apk : e = " ++ show (top e)) $ case ch of
  [] -> h
  ((It (App i e1 e2) alpha bh' ch'):_) -> 
    let it = case e of
              (Lam x e0) -> It e0 alpha h ch'
              _          -> It e2 False bh' ch'
    in eval (it:h)

-- ====================================
--     ENVIRONMENT BINDER MANIPULATION 
-- ====================================

emptybh = []

lookup :: BH -> Var -> (Exp, BH)
lookup [] x = (FREE x, [])
lookup ((It (Lam y e) False bh ch):_) x 
  | x==y      = (FREE x, [])
  | otherwise = UNP.lookup bh x
lookup (((It (Lam y e) True bh ch):_)) x
  | x==y      = case ch of
    ((It (App _ _ e2) _ bh' _):_) -> (e2, bh')
    otherwise                        ->
      error "lookup: alpha == True and \
        \ ch is empty or points not to the application"
  | otherwise = UNP.lookup bh x
lookup ((It _ _ bh _):_) x = UNP.lookup bh x


-- ================
-- Input and output format stuff
-- ================

top :: Exp -> String
top (App i e1 e2)  = "@" ++ (numstr i)
top (V x)          = x
top (Lam x e)      = "Lam " ++ x
top (FREE _)           = " FreeVariable "
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
    "(" ++ show e1 ++ " @ " ++ show e2 ++ ")" ++ s
  showsPrec _ (Lam a e) s     = "(Lam " ++  a ++ "." ++ show e ++ ")" ++ s
  showsPrec _ (V x) s         =  x ++ s
  showsPrec _ (FREE _) s          = "FreeVariable" ++ s
  showsPrec _ Bugexp s        = "Bugexp" ++ s

instance Show Item where
  show (It e alpha bh h) = doLen (top e) 10 ++ " | "
    ++ doLen (show (length bh)) 5 ++ " | "
    ++ doLen (show alpha) 5  ++ " | "
    ++ doLen (show (length h)) 5
  showsPrec _ it s = "Item " ++ show it ++ s

doLen s l
  | l <= len  = s
  | otherwise = s ++ [a | a <- " ", j <- [1..(l - len)]]
  where len = length s
