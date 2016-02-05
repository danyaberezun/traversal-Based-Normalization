import qualified Data.Map as Map
import Data.Maybe
import Data.Char
import Text.ParserCombinators.Parsec
--import Control.Monad

-- untyped simple lambda expression
data UntypedLambda = ULVar Char String
  | ULApp Char UntypedLambda UntypedLambda
  | ULAbs Char String UntypedLambda
  deriving (Eq, Ord)
instance Show UntypedLambda where
  show (ULVar _ v)                   = v
  show (ULApp _ e1@(ULAbs _ _ _) e2) = "(" ++ show e1 ++ ")" ++ show e2
  show (ULApp _ e (ULVar _ v))       = show e ++ v
  show (ULApp _ e1 e2)               = show e1 ++ "(" ++ show e2 ++ ")"
  show (ULAbs _ v e)                 = "\\" ++ v ++ " . " ++ show e

data ULambda = UVar String
  | UApp ULambda ULambda
  | UAbs String ULambda

-- term (is the end of sub-traversal, (history pointer, (pointer to last unfinished application, (lambda associate pointer, binder pointer)))
newtype Traversal = Tr [(UntypedLambda, (Bool, (Int, (Int, (Int, Int)))))]
instance Show Traversal where
  show (Tr tr) = show' (reverse tr) 1 where
    show' [] _ = ""
    show' (x:xs) i =
      -- change 350 for something greater if program goes to infinite loop
      --up2 i ++ ". " ++ show1 x 350 ++ "\n" ++ show' xs ((+) i 1)
      up2 i ++ ". " ++ show1 x 70 ++ "\n" ++ show' xs ((+) i 1)
      where
        up2 i
          | i < 10    = "_" ++ show i
          | otherwise = show i
        upb True  = "True_"
        upb False = "False"
        show1 (t, (b, (hp, (un, (bp, bi))))) l =
          let
            st = show t
            lt = (-) l (length st)
          in st ++ spac lt ++ upb b ++ "_" ++ up2 hp ++ "_" ++ up2 un ++ "_" ++ up2 bp ++ "_" ++ up2 bi
        spac 0  = ""
        spac ltt = "_" ++ (spac ((-) ltt 1))
--instance Show Traversal where
--  show (Tr tr) = show' tr where
--    show' [] = ""
--    show' ((t, (b, (hp, (un, (bp, bi))))):xs) =
--      (show t) ++ "\n" ++ show b ++ "_" ++ show hp ++ "_" ++ show un ++ "_" ++ show bp ++ "_" ++ show bi ++ "\n" ++ show' xs

--instance Show Traversal where
--  show (Tr tr) = show' (reverse tr) 1 where
--    show' [] _ = ""
--    show' (x@(_, (True, _)):xs) i = show i ++ " " ++ show x ++ "\n" ++ show' xs ((+) i 1)
--    show' ((_, (False, _)):xs) i = show' xs ((+) i 1)

-- parsing
identifier  = do
  c  <- letter
  cs <- many (alphaNum <|> char '_')
  return (c:cs)
parseExpr = try parseApp <|> parseExpr'
parseExpr' = parseAbs <|> parseVar <|> between (char '(') (char ')') parseExpr
parseVar = do
  name <- identifier
  return $ UVar name
parseApp = do
  t1 <- parseExpr'
  char '@'
  t2 <- parseExpr'
  return $ UApp t1 t2
parseAbs = do
  char '\\'
  name <- identifier
  char '.'
  expr <- parseExpr
  return $ UAbs name expr

computeBoundVariables :: UntypedLambda -> [String]
computeBoundVariables t = computeBoundVariables' t [] where
  computeBoundVariables' (ULAbs _ x  e ) xs = computeBoundVariables' e  (x:xs)
  computeBoundVariables' (ULApp _ e1 e2) xs = computeBoundVariables' e1 (computeBoundVariables' e2 xs)
  computeBoundVariables' _ xs = xs

findDynamicBinder :: String -> Traversal -> Int -> Int
findDynamicBinder z tr len = findDynamicBinder' z tr len tr where
  findDynamicBinder' z (Tr []) _ trr = error $ "findDynamicBinder : error: empty traversal" ++ show z ++ " tr = " ++ show trr
  findDynamicBinder' z (Tr ((ULAbs _ x t, _):tr)) len _ | x == z = len
  findDynamicBinder' z (Tr tr@((_, (_, (_, (_, (_, bi_z))))):_)) len trr = findDynamicBinder' z (Tr (drop (len - bi_z) tr)) bi_z trr

findAbstractionBP :: Traversal -> Int -> Int
findAbstractionBP (Tr []) len = 0
findAbstractionBP (Tr tr@((ULAbs _ _ _, (_, (_, (_, (bp_x, bi_x))))):xs)) len =
  let bp_x' = bp_x - 1
  in findAbstractionBP (Tr $ drop (len - bp_x') tr) bp_x'
findAbstractionBP (Tr tr@((ULApp _ _ _, (_, (_, (_, (bp_x, bi_x))))):xs)) len =
  len
findAbstractionBP (Tr tr@((ULVar _ _, (_, (_, (_, (bp_x, bi_x))))):xs)) len =
  findAbstractionBP (Tr $ drop (len - bp_x) tr) bp_x

findLastUnapplied :: Traversal -> Int -> Int
findLastUnapplied (Tr []) len = 0
findLastUnapplied (Tr tr@((ULAbs _ _ _, (_, (_, (0, _)))):xs)) len = 0
findLastUnapplied (Tr tr@((ULAbs _ _ _, (_, (_, (un_x, _)))):xs)) len =
  --let un_x' = un_x - 1
  --in findLastUnapplied (Tr $ drop (len - un_x') tr) un_x'
  let tr'@((_, (_, (_, (bp2', (_, _))))):_) = drop (len - un_x) tr
  in findLastUnapplied (Tr (drop (un_x - bp2') tr')) bp2'
findLastUnapplied (Tr tr@((ULApp _ _ _, (_, (_, (un_x, _)))):xs)) len =
  len
findLastUnapplied (Tr tr@((ULVar _ _, (_, (_, (un_x, _)))):xs)) len =
  findLastUnapplied (Tr $ drop (len - un_x) tr) un_x

travers :: Traversal -> [String] -> Int -> Traversal
travers (Tr tr@((x, (b_x, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv len = case x of
  ULApp _ e _ -> travers (Tr ((e, (False, (len, (un_e e len, (bp_ee e len, computeBI tr e bv len))))):tr)) bv (len + 1)
  --ULApp _ e _ -> travers (Tr ((e, (False, (hp_e e len, (un_e e len, (bp_ee e len, computeBI tr e bv len))))):tr)) bv (len + 1)
  --ULApp _ e _ -> travers (Tr ((e, (False, (0, (un_e e len, (bp_ee e len, computeBI tr e bv len))))):tr)) bv (len + 1)
  ULAbs _ z e -> travers (Tr ((e, (False, (len, (un_e e len, (bp_ee e len, computeBI tr e bv len))))):tr)) bv (len + 1)
  --ULAbs _ z e -> travers (Tr ((e, (False, (hp_e' e len, (un_e e len, (bp_ee e len, computeBI tr e bv len))))):tr)) bv (len + 1)
  --ULAbs _ z e -> travers (Tr ((e, (False, (0, (un_e e len, (bp_ee e len, computeBI tr e bv len))))):tr)) bv (len + 1)
  ULVar _ z   ->case elem z bv of
    False -> case findUnboundArgument (Tr tr) len of
      Nothing     -> Tr ((x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)
      Just (e, (i, j)) -> case e of
        ULAbs _ _ _ -> travers (Tr ((e, (False, (j, (j, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
        --ULAbs _ _ _ -> travers (Tr ((e, (False, (j, (i+1, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
        --ULAbs _ _ _ -> travers (Tr ((e, (False, (0, (i+1, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
        --_ -> travers (Tr ((e, (False, (j, (i, (i, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
        _ -> travers (Tr ((e, (False, (j, (i, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
        --_ -> travers (Tr ((e, (False, (0, (i, (i, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
    True  -> case findBoundArgument (Tr tr) len of
      Nothing     -> case findUnboundArgument (Tr tr) len of
        Nothing     -> Tr ((x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)
        Just (e, (i, j)) -> case e of
          ULAbs _ _ _ -> travers (Tr ((e, (False, (j, (j, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
          --ULAbs _ _ _ -> travers (Tr ((e, (False, (j, (i+1, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
          --ULAbs _ _ _ -> travers (Tr ((e, (False, (0, (i+1, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
          --_ -> travers (Tr ((e, (False, (j, (i, (i, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
          _ -> travers (Tr ((e, (False, (j, (i, (0, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
          --_ -> travers (Tr ((e, (False, (0, (i, (i, computeBI tr e bv bun_x))))):(x, (True, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) bv (len + 1)
      Just (e, (i, j)) -> travers (Tr ((e, (False, (len, (bp_ee e len, (bp_ee e len, computeBI tr e bv i))))):tr)) bv (len + 1)
      --Just (e, (i, j)) -> travers (Tr ((e, (False, (0, (bp_ee e len, (bp_ee e len, computeBI tr e bv i))))):tr)) bv (len + 1)
  where
    computeBI tr y bv i = case y of
      ULVar _ z | elem z bv -> findDynamicBinder z (Tr (drop (len - i) tr)) i
      ULVar _ z | otherwise -> 0
      _ -> i
    --bp_ee e len = findAbstractionBP (Tr tr) len
    bp_ee e len = findLastUnapplied (Tr tr) len
    un_e e len = findLastUnapplied (Tr tr) len
    hp_e e len = case e of
      --ULAbs _ _ _ -> (-) (findAbstractionBP (Tr tr) len) 1
      ULAbs _ _ _ -> findAbstractionBP (Tr tr) len
      _ -> len
    --hp_e' e len = if bp_x == 0 then len else findAbstractionBP (Tr tr) len
    hp_e' e len = if bp_x == 0 then len else findHp (Tr tr) len
    findHp (Tr []) _ = 0
    findHp (Tr tr@((x, (b_x, (hp_x, (bun_x, (bp_x, bi_x))))):xs)) len = case x of
      ULAbs _ _ _ -> if bp_x == 0 then len
        else let bp = bp_x - 1
        in findHp (Tr (drop (len - bp) tr)) bp
      _ -> len

findBoundArgument :: Traversal -> Int -> Maybe (UntypedLambda, (Int, Int))
findBoundArgument (Tr tr@((ULVar _ _, (_, (_, (_, (bp_z, bi_z))))):xs)) len =
  let tr' = drop (len - bi_z) tr
  in findBoundArgument' (Tr tr') bi_z
findBoundArgument' (Tr tr@((ULAbs _ _ _, (_, (_, (_, (0, bi_z))))):xs)) len = Nothing
findBoundArgument' (Tr tr@((ULAbs _ _ _, (_, (_, (bu_z, (bp_z, bi_z))))):xs)) len =
  let (a, (_, (hp_a, (_, (bp_a, bi_a))))) = head $ drop (len - bp_z) tr
  -- ????????????????????/ bp_a or bu_a?
  in case a of
    ULApp _ _ e2 -> Just (e2, (bp_z, hp_a))
    _ -> error $ "findBoundArgument: ULAbs: a is not an appliaction " ++ show a

--findUnboundArgument :: Traversal -> Int -> Maybe (UntypedLambda, Int)
--findUnboundArgument (Tr tr@((ULVar _ _, (_, (_, (bp_z, bi_z)))):xs)) len
--  | bp_z == 0 = Nothing
--  | otherwise = let tr' = drop (len - bp_z) tr
--    in case head tr' of
--      (ULApp _ e1 e2, (_, (_, (bp_a, bi_a)))) -> Just (e2, bp_a)
--      _ -> error "findUnboundArgument error"
findUnboundArgument :: Traversal -> Int -> Maybe (UntypedLambda, (Int, Int))
findUnboundArgument (Tr tr@((ULVar _ _, (_, (_, (un_z, (bp_z, bi_z))))):xs)) len
  | un_z == 0 = Nothing
  | otherwise = let tr' = drop (len - un_z) tr
    in case head tr' of
      (ULApp _ e1 e2, (_, (hp_a, (un_a, (bp_a, bi_a))))) -> Just (e2, (un_a, un_z))
      _ -> error "findUnboundArgument error"

normalize :: UntypedLambda -> Traversal
normalize t =
  let bv = computeBoundVariables  t
  in travers (Tr [(t, (False, (0, (0, (0, 0)))))]) bv 1

annotate :: ULambda -> UntypedLambda
annotate t = snd $ annotate' t '\1024' where
  annotate' (UVar v) l = (chr (ord l + 1), ULVar l v)
  annotate' (UApp e1 e2) l =
    let
      (l1, e1') = annotate' e1 l
      (l2, e2') = annotate' e2 l1
    in (chr (ord l2 + 1), ULApp l2 e1' e2')
  annotate' (UAbs x e) l =
    let (l', e') = annotate' e l
    in (chr (ord l' + 1), ULAbs l' x e')

ex = "(\\a . (\\w . w @ (w @ a)) @ s) @ (s @ z)"
ex_1 = "(g @ (\\ n . n))"
ex_2 = "((\\ h . h) @ (\\ f . f)) @ a"
ex_3 = "((\\ h . h @ a) @ (\\ f . f))"
ex_4 = "\\ f . \\ y . (y @ f) @ y"
ex_5 = "\\ y . \\ f . (y @ f) @ y"
ex_6 = "((\\ h . \\ z . ((h @ (\\ x . ((h @ (\\ q . x)) @ a))) @ (z @ a))) @ (\\ f . \\ y . f @ ((g @ (\\ b . b)) @ y))) @ (g @ (\\ n . n))"
ex_7 = "((\\ m . \\ n . \\ s . \\ z . (m @ (n @ s)) @ z) @ (\\ a . \\ q . a @ (a @ (a @ q)))) @ (\\ d . \\ e . d @ (d @ e))"
--ex_omega =
--  "(((\\ x . x @ x) @ (\\ y . y @ y)) @ (\\ z . z)) @ (\\ w . w)"
ex_succ2 = "(\\ n . \\ s . \\ z . (n @ s) @ (s @ z)) @ (\\ p . \\ o . p @ (p @ o))"
ex_succ = "(\\ n . \\ s . \\ z . s @ ((n @ s) @ z)) @ ( \\ s1 . \\ z1 . (m @ s1) @ z1)"
ex_mult = "\\ m . \\ n . \\ s . \\ z . (m @ (n @ s)) @ z"

fib = "\\ q . (\\ w .  w @ (\\ e . \\ r . r))  @ ((q @ (\\ t . ((\\ y .  \\ u .  \\ i . (i @ y) @ u)   @ ((\\ o .  o @ (\\ p .  \\ a . a))   @ t)) @ (((\\ s .  \\ d .  \\ f .  \\ g .  (s @ f) @ ((d @ f) @ g))     @ ((\\ h .  h @ (\\ j .  \\ k . k))   @ t)) @ ((\\ l .  l @ (\\ z . \\ x . z))    @ t)))) @ (((\\ c .  \\ v .  \\ b .  (b @ c) @ v)    @ (\\ n .  \\ m . m))  @ (\\ q1 .  \\ w1 .  q1 @ w1)))"
fib2 = "(\\ q . (\\ w .  w @ (\\ e . \\ r . r))  @ ((q @ (\\ t . ((\\ y .  \\ u .  \\ i . (i @ y) @ u)   @ ((\\ o .  o @ (\\ p .  \\ a . a))   @ t)) @ (((\\ s .  \\ d .  \\ f .  \\ g .  (s @ f) @ ((d @ f) @ g))     @ ((\\ h .  h @ (\\ j .  \\ k . k))   @ t)) @ ((\\ l .  l @ (\\ z . \\ x . z))    @ t)))) @ (((\\ c .  \\ v .  \\ b .  (b @ c) @ v)    @ (\\ n .  \\ m . m))  @ (\\ q1 .  \\ w1 .  q1 @ w1))))  @ (\\ s1 . \\ z1 . s1 @ (s1 @ z1))"
fib4 = "(\\ q . (\\ w .  w @ (\\ e . \\ r . r))  @ ((q @ (\\ t . ((\\ y .  \\ u .  \\ i . (i @ y) @ u)   @ ((\\ o .  o @ (\\ p .  \\ a . a))   @ t)) @ (((\\ s .  \\ d .  \\ f .  \\ g .  (s @ f) @ ((d @ f) @ g))     @ ((\\ h .  h @ (\\ j .  \\ k . k))   @ t)) @ ((\\ l .  l @ (\\ z . \\ x . z))    @ t)))) @ (((\\ c .  \\ v .  \\ b .  (b @ c) @ v)    @ (\\ n .  \\ m . m))  @ (\\ q1 .  \\ w1 .  q1 @ w1))))  @ (\\ s1 . \\ z1 . s1 @ (s1 @ (s1 @ (s1 @ z1))))"

--ex_8 = "(\\ x . \\ y . x @ x) @ (\\ z . z)"
--ex_9 = "(\\ x . \\ y . x @ y) @ (\\ z . z)"
-- unfypable in STLC
ex_9 = "(\\ x . x @ x) @ (\\ z . z)"

run_algorithm name t = do
  putStrLn $ "Example: " ++ name ++ " " ++ t
  case parse parseExpr "" (filter (not . isSpace) t) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term

run_algorithm_in_file name t = let filename = "result_" ++ name ++ ".txt"
  in do
    putStrLn $ "Example(see file " ++ filename ++ "): " ++ name ++ " " ++ t
    case parse parseExpr "" (filter (not . isSpace) t) of
      Left  msg  -> error $ show msg
      Right term ->
        let (Tr tr) = normalize $ annotate term
        -- this can go to infinite loop ; see show function
        --in do
          --writeFile filename (show (Tr tr))
          --writeFile filename (show (Tr [head $ tr]) ++ "\n" ++ show (Tr [last $ tr]))
        in putStrLn $ show $ length tr

examples = do
  run_algorithm "NPR" ex_6
  run_algorithm "SUCC" ex_succ
  run_algorithm "SUCC TWO" ex_succ2
  run_algorithm "MULT" ex_mult
  run_algorithm "MULT THREE TWO" ex_6
  run_algorithm_in_file "FIB" fib
  run_algorithm_in_file "FIB TWO" fib2
  run_algorithm_in_file "FIB FOUR" fib4
  run_algorithm "UNPYPABLE IN STLC" ex_9
  
main = do
  putStrLn $ "traversal for term " ++ ex
  case parse parseExpr "" (filter (not . isSpace) ex) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term " ++ ex_1
  case parse parseExpr "" (filter (not . isSpace) ex_1) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term " ++ ex_2
  case parse parseExpr "" (filter (not . isSpace) ex_2) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term " ++ ex_3
  case parse parseExpr "" (filter (not . isSpace) ex_3) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term " ++ ex_4
  case parse parseExpr "" (filter (not . isSpace) ex_4) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term " ++ ex_5
  case parse parseExpr "" (filter (not . isSpace) ex_5) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term (NPR) " ++ ex_6
  case parse parseExpr "" (filter (not . isSpace) ex_6) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  putStrLn $ "traversal for term (mult_3_2)" ++ ex_7
  case parse parseExpr "" (filter (not . isSpace) ex_7) of
    Left  msg  -> error $ show msg
    Right term -> putStrLn $ show $ normalize $ annotate term
  --putStrLn $ "traversal for term " ++ ex_8
  --case parse parseExpr "" (filter (not . isSpace) ex_8) of
  --  Left  msg  -> error $ show msg
  --  Right term -> putStrLn $ show $ normalize $ annotate term
  --putStrLn $ "traversal for term " ++ ex_9
  --case parse parseExpr "" (filter (not . isSpace) ex_9) of
  --  Left  msg  -> error $ show msg
  --  Right term -> putStrLn $ show $ normalize $ annotate term
  ----putStrLn $ "traversal for term " ++ fib2
  ----case parse parseExpr "" (filter (not . isSpace) fib2) of
  ----  Left  msg  -> error $ show msg
  ----  --Right term -> putStrLn $ show $ normalize $ annotate term
  ----  Right term ->
  ----    let (Tr tr) = normalize $ annotate term
  ----    in writeFile "result.txt" (show (Tr tr))
  --    --in writeFile "result.txt" (show (Tr [head $ tr]) ++ "\n" ++ show (Tr [last $ tr]))
  ----case parse parseExpr "" (filter (not . isSpace) ex_omega) of
  ----  Left  msg  -> error $ show msg
  ----  Right term -> putStrLn $ show $ normalize $ annotate term