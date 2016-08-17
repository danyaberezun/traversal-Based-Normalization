module Main where

import           Data.List

data Exp =
  -- for delta rules
  ConstE Int -- integer constants
  | AddE Exp Exp -- Plus function
  | MinE Exp Exp -- Minus function
  | IfE Exp Exp Exp -- if-then-else
  -- Lambda
  | AppE Int Exp Exp -- function application
  | LamE String Exp -- lambda expression
  | VE String -- variable (for input perrpoise only)
  | BVarE String Int -- Bound variable
  | FreeE String -- free variable
  | NoE -- Fake node (no expression)
  -- | LetE String Exp Exp -- Let expression (call-by-value)
  | YE String Exp -- Y-combinator
  deriving (Eq)

type Value = Exp

-- traversal. arguments:
--    Exp --- an expression
--    H   --- binders (including functions)
--    H   --- pending applies
type H     = [Itemt]
data Itemt =
    It Exp H H
  | Res Exp H H
  -- BP constructor cannot occur in the resulting traversal
  -- It is used to denote a an evaluation of the right
  -- child and may occur is "as" list only
  | BP Exp H H
  --- following Itemt's may appear only in "history"
  | Pause
  | Substitution
  | SubstY
  deriving (Eq)

-- ===================
-- Auxiliary functions
-- ===================

getLeftChild :: Exp -> Exp
getLeftChild (AddE   e _) = e
getLeftChild (MinE   e _) = e
getLeftChild (AppE _ e _) = e
getLeftChild (IfE  e _ _) = e

getRightChild :: Exp -> Exp
getRightChild (AddE   _ e) = e
getRightChild (MinE   _ e) = e
getRightChild (AppE _ _ e) = e

getArithmOp :: Exp -> (Int -> Int -> Int)
getArithmOp (AddE{}) = (+)
getArithmOp (MinE{}) = (-)

isArithmOp :: Exp -> Bool
isArithmOp (AddE{}) = True
isArithmOp (MinE{}) = True
isArithmOp _        = False

replaceFinstChildOfArithmOp :: Exp -> Exp -> Exp
replaceFinstChildOfArithmOp (AddE _ e) v = AddE v e
replaceFinstChildOfArithmOp (MinE _ e) v = MinE v e

calcConsts :: (Int -> Int -> Int) -> Exp -> Exp -> Exp
calcConsts f (ConstE c1) (ConstE c2) = ConstE $ f c1 c2
calcConsts f e1 e2 =
  error $ "ERROR: calcConsts: one of arguments is not a constant: e1 = "
  ++ show e1 ++ "; e2 = " ++ show e2

-- ================================================
-- Traverse expression
-- ================================================

eval :: Exp -> H -> H
eval e h@((It _ bs as):_) =
  if   isRecurciveCase e
  then let e1 = getLeftChild e in eval e1 ((It e1 bs h):h)
  else
    case e of
      ConstE n    -> pause e as h
      FreeE  y    -> pause e as h
      BVarE  x i  -> subst i h
      YE     f e0 -> eval e0 ((It e0 h as  ):h)
      LamE   _ e0 -> eval e0 ((It e0 h  as'):h) where
        as' = case as of
          []                  -> []
          ((It NoE _ as''):_) -> as
          ((It _   _ as''):_) -> as''
      otherwise   -> error $ "eval: error: e = " ++ show e
  where
    isRecurciveCase :: Exp -> Bool
    isRecurciveCase e = case e of
      IfE{}  -> True
      AddE{} -> True
      MinE{} -> True
      AppE{} -> True
      other  -> False

-- =========================================
-- PAUSE
-- =========================================

pause _ []                             h = h
pause e ((It NoE           _  _ ):as ) h = pause e as h
-- Popup last pending application
pause _ ((It (AppE _ _ e2) bs as):_  ) h =
  eval e2 ((It e2 bs ((It NoE [] []):as)):(Pause):h)
-- If-then-else
pause e@(ConstE b) ((It (IfE _ e1 e2) bs as):as') h =
  let ee = if b == 0 then e2 else e1
  in eval ee ((It ee bs as):(Pause):h)
pause e ((It (IfE _ e1 e2) bs as):as') h =
  error $ "pause: error: if case: condition is not a value: " ++ show e
-- Arithmetic operations (Add && Min)
pause v ((It e bs as):as') h 
  | isArithmOp e
    = let e2 = getRightChild e
          e' = replaceFinstChildOfArithmOp e v
      in case v of
        ConstE _  -> eval e2 ((It e2 bs ((BP e' bs as):as')):(Pause):h)
        otheriwse -> error "ERROR: pause: rigat child of Arithmetic \
          \operation is not a value"
pause v h'@((BP e bs as):_) h
  | isArithmOp e
    = let binOp = getArithmOp e
          ee    = calcConsts binOp (getLeftChild e) v
      in pause ee as ((Res ee bs h'):(Pause):h)

-- =========================================
-- LOOK UP BOUND VARIABLE via deBruijn index
-- =========================================

subst i h@((It _ bs as):_) = subst' i bs where
  subst' 1 ((It e@(YE _ _) bs _):_) = eval e ((It e bs as):(SubstY):h)
  subst' 1 ((It _ _ ((It NoE bs _):_)):_) = pause (NoE) as h
  subst' 1 ((It (LamE _ _) _ ((It (AppE _ _ e2) bs _):_)):_) =
    eval e2 ((It e2 bs as):(Substitution):h)
  subst' 1 ar = error $ "error: subst' 1: " ++ show ar ++ "\nh = " ++ show h
  subst' j ((It _ bs _):_) = subst' (j-1) bs
  subst' j ar = error $ "ERROR: subst' 2: " ++ show j
    ++ " ;r=" ++ show ar ++ "\nh = " ++ show h

-- ================
-- Input and output format stuff
-- ================

instance Show Exp where
  showsPrec _ (FreeE a) s   =  a ++ s
  showsPrec _ (AppE n e1 e2) s = "(@" ++ show n ++ " " ++ show e1 ++ " "
    ++ show e2 ++ ")" ++ s
  showsPrec _ (BVarE a i) s =  a ++ " ^" ++ show i ++ s
  showsPrec _ (LamE a e) s  = "(LamE " ++  a ++ "." ++ show e ++ ")" ++ s
  -- showsPrec _ (LetE v e1 e2) s  = "(LetE " ++ v ++ " = " ++ show e1
  -- ++ " in " ++ show e2 ++ ")" ++ s
  showsPrec _ (ConstE n)   s    = show n ++ s
  showsPrec _ (AddE e1 e2) s    = "(" ++ show e1 ++ "+" ++ show e2 ++ ")"++ s
  showsPrec _ (MinE e1 e2) s    = "(" ++ show e1 ++ "-" ++ show e2 ++ ")"++ s
  showsPrec _ (IfE e0 e1 e2) s  =
    "if " ++ show e0 ++ " then [" ++ show e1 ++ "] else [" ++ show e2 ++
    "]" ++ s
  showsPrec _ (VE e) s = "VE " ++ e
  showsPrec _ NoE s = "NoE"
  showsPrec _ (YE f e) s = "YE " ++ f ++ " " ++ show e ++ " " ++ s

instance Show Itemt where
  showsPrec _ (It e bs as) s = "\n[" ++ show e  ++ " bs = "
    ++ show (length bs) ++ " as = " ++ show (length as) ++ "]" ++ s
  showsPrec _ (BP e bs as) s = "\n[" ++ show e  ++ " bs = "
    ++ show (length bs) ++ " as = " ++ show (length as) ++ "]" ++ s
  showsPrec _ (Res e bs as) s = "\n[" ++ show e  ++ " bs = "
    ++ show (length bs) ++ " as = " ++ show (length as) ++ s
  showsPrec _ (Pause) s = "\n[PAUSE]" ++ s
  showsPrec _ (Substitution) s = "\n[Substitution]" ++ s

-- =============
-- ADD deBruijn INDICES
-- =============

adddeBruijn :: Exp -> Exp
adddeBruijn e = f [] 1 e where
  f :: [(String, Int)] -> Int -> Exp -> Exp
  f vars l (VE x)         =
    let v = filter (\(y, _) -> x == y) vars
    in if v == []
      then FreeE x
      else BVarE x (l - (snd $ head v))
  f vars l (AppE i e1 e2) = AppE i (f vars l e1) (f vars l e2)
  f vars l (LamE x e)     = LamE x (f ((x,l):vars) (l+1) e)
  f vars l e@(ConstE _)   = e
  f vars l e@(FreeE  _)   = e
  f vars l (AddE e1 e2)   = AddE (f vars l e1) (f vars l e2)
  f vars l (MinE e1 e2)   = MinE (f vars l e1) (f vars l e2)
  f vars l (IfE e0 e1 e2) =
    IfE (f vars l e0) (f vars l e1) (f vars l e2)
  --f vars l (LetE v e1 e2) = f vars l (AppE 0 (LamE v e2) e1)
  f vars l (YE fu e)      = YE fu (f ((fu,l):vars) (l+1) e)
  f vars l e              = error $ "f: error: " ++ show e

-- ==============================
-- TRAVERSE an EXPRESSION
-- ==============================

top :: Exp -> String
top (VE x)  = x
top (FreeE x) = x
top (BVarE x _) = x
top (LamE x e)    = "Lam " ++ x
top (AppE i e1 e2) = "@"++(numstr i)
top NoE   = "-"
top (ConstE n) = "Const " ++ show n
top (AddE e1 e2) = "Add "
top (MinE e1 e2) = "Min "
top (IfE e0 e1 e2) = "If " ++ show e0
--top (LetE v e1 e2) = "Let " ++ v ++ " = " ++ show e1 ++ " in " ++ show e2
top (YE f e) = "Y " ++ f


numstr :: Int -> String
numstr 0 = "0"
numstr 1 = "1"
numstr 2 = "2"
numstr 3 = "3"
numstr 4 = "4"
numstr 5 = "5"
numstr 6 = "6"
numstr 7 = "7"
numstr 8 = "8"
numstr 9 = "9"
numstr n = (numstr (div n 10)) ++ (numstr (mod n 10))

-- cleanup as and bs lists
filt = filter (\ x -> x /= Pause && x /= Substitution)

raux :: H -> Int -> String
raux [] i     = ""
raux ((Res e bs as):t) i =
  fitToLen ("\n time " ++ show i) ++ ": e = RES " ++ raux' e bs as t i
raux ((BP e bs as):t) i =
  "\n ERROR: function raux: BP constructor found in the resulting traversal:"
  ++ raux' e bs as [] i
raux ((Pause):t) i = "\nPause" ++ raux t i
raux ((Substitution):t) i = "\nSubstitution" ++ raux t i
raux ((SubstY):t) i = "\nSubstY" ++ raux t i
raux ((It e bs as):t) i =
  fitToLen ("\n time " ++ show i) ++ ": e = It  " ++ raux' e bs as t i
raux' e bs as t i = 
  let e' = top e
  in fitToLen e' ++ fitToLen ("bs = " ++ (show . length $ filt bs))
    ++ fitToLen ("as = " ++ (show . length $ filt as))
    ++ raux t (i + 1)
olen = 15
fitToLen str = let j = length str
  in str ++ if j < olen then blank $ olen - j else ""
blank i | i == 0 = ""
        | True   = (++) " " $ blank $ i - 1

run m =
  "\nINPUT : \n " ++ show m ++
  let
    mdB  = adddeBruijn m
    hout = eval mdB [It mdB [] []]
  in "\n VALUE IS: " ++  raux (reverse hout) 1

-- =============
-- TEST EXAMPLES
-- =============

numexample1 = ConstE 1
numexample2 = AddE (ConstE 1) (ConstE 2)
numexample3 = AddE (ConstE 1) (AddE (ConstE 2) (ConstE 3))
numexample4 = AddE (AddE (ConstE 1) (ConstE 2)) (ConstE 2)
numexample5 = AddE (AddE (ConstE 1) (ConstE 2)) (AddE (ConstE 3) (ConstE 4))

numexample6 = IfE (ConstE 0) (ConstE 99) (ConstE 100)
numexample7 = IfE (ConstE 1) (ConstE 99) (ConstE 100)
numexample8 = IfE (AddE (ConstE 0) (ConstE 0))  (ConstE 99) (ConstE 100)
numexample9 = IfE (AddE (ConstE 0) (ConstE 1))  (ConstE 99) (ConstE 100)
numexample10 = IfE (AddE (ConstE 0) (ConstE 1))  numexample4 numexample5

example1  =  (FreeE "y1")
example2  =  AppE 1 (FreeE "y1") (FreeE "y2")
example3  =  AppE 1 (FreeE "y1") (AppE 2 (FreeE "y2") (FreeE "y3"))
example4  =  AppE 1
  (AppE 2 (FreeE "y1") (FreeE "y2"))
  (AppE 3 (FreeE "y3") (FreeE "y4"))

ongexample' = AppE 1 (AppE 2 a1' a6') (AppE 11 (VE "g2") (LamE "q" (VE "q")))
a1' = LamE "phi" (LamE "z" a2')
a2' = AppE 3 a3' (AppE 7 (VE "z") (VE "a2"))
a3' = AppE 4 (VE "phi") a4'
a4' = LamE "x" (AppE 5 a5' (VE "a1"))
a5' = AppE 6 (VE "phi") (LamE "x1" (VE "x"))
a6' = LamE "f" (LamE "y" a7')
a7' = AppE 8 (VE "f") (AppE 9 (AppE 10
  (VE "g1")
  (LamE "b" (VE "b1"))) (VE "y"))

mixEx  = AppE 0 (LamE "x" (VE "x")) (AddE (ConstE 1) (ConstE 2))
--letEx  = LetE "x" (AddE (ConstE 1) (ConstE 2)) (VE "x")
minEx  = MinE (ConstE 2) (ConstE 1)
minEx2 = AppE 1 (LamE "x" (MinE (VE "x") (ConstE 1))) (ConstE 2)
yEx   = AppE 1
  (YE "sum" (LamE "x" (IfE (VE "x")
    (AddE (VE "x") (AppE 2 (VE "sum") (MinE (VE "x") (ConstE 1))))
    (ConstE 0))))
  (ConstE 2)
ee1 = AddE (AddE (ConstE 1) (ConstE 2)) (AddE (ConstE 3) (ConstE 4))
ee2 = AppE 1 (AppE 2 (VE "x") (VE "y")) (AppE 3 (VE "z") (VE "w"))
ee3 = AppE 1 (AppE 2
    (LamE "x" (AddE (AddE (ConstE 1) (ConstE 2)) (ConstE 3)))
    (VE "y"))
  (VE "z")
sumS = YE "sum"
  (LamE "x" (IfE (VE "x")
    (AddE (VE "x") (AppE 2 (VE "sum") (MinE (VE "x") (ConstE 1))))
    (ConstE 0)))
sum1 = AppE 1 sumS (ConstE 1)
sum5 = AppE 1 sumS (ConstE 5)

examples = [ee1, ee2, ee3, ongexample', sum1, sum5]

-- ==============================
--     MAIN
-- ==============================

main :: IO()
main =
  putStrLn $ fst $ mapAccumL
    (\acc e ->
      (acc ++ "EXAMPLE : \n" ++ run e ++ "\n====================\n", e))
    ""
    examples