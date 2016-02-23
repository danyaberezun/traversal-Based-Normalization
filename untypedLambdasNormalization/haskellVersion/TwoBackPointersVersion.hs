import qualified Data.Map as Map
import Data.Maybe
import Data.Char
import Debug.Trace
import Data.List
import Text.ParserCombinators.Parsec

import Examples
import ToPdf
import DataTypes
import Parsing
import AuxiliaryFunctions

computeBoundVariables :: UntypedLambda -> [String]
computeBoundVariables t = computeBoundVariables' t [] where
  computeBoundVariables' (ULAbs _ x  e ) xs = computeBoundVariables' e  (x:xs)
  computeBoundVariables' (ULApp _ e1 e2) xs = computeBoundVariables' e1 (computeBoundVariables' e2 xs)
  computeBoundVariables' _ xs = xs

findDynamicBinder :: String -> Traversal -> Int -> BinderPointer
findDynamicBinder z tr len = findDynamicBinder' z tr len tr where
  findDynamicBinder' z (Tr []) _ trr = error $ "findDynamicBinder : error: empty traversal" ++ show z ++ " tr = " ++ show trr
  findDynamicBinder' z (Tr ((ULAbs _ x t, _):tr)) len _ | x == z = BIP len
  findDynamicBinder' z (Tr tr@((_, (_, (_, bi_z))):_)) len trr
    | (bp2int bi_z) == len = error $ "findDynamicBinder' " ++ show bi_z ++ " " ++ show len ++ "\n" ++ show (Tr tr)
    | otherwise   = findDynamicBinder' z (Tr (drop (len - (bp2int bi_z)) tr)) (bp2int bi_z) trr

-- TODO: clean up code
travers :: Traversal -> [String] -> Int -> Bool -> Traversal
travers (Tr tr@(x@(x_e, (b_x, (up_x, bi_x))):trs)) bv len hn = case x of
  --trace (show (Tr tr) ++ "\n") $ case x of
  -- (_VAR) rules
  (ULVar _ z, (_, (LUP up_x, _))) -> case elem z bv of
    -- (FVAR) rule
    False -> 
      if hn == False then travers (hideNodes (Tr tr) len) bv len True
      else if up_x == 0 then Tr $ (x_e, (True, (LUP up_x, bi_x))):trs
      else case drop (len - up_x) tr of
        tr'@((ULApp _ _ r, (_, (up_a, _))):_) -> case r of
          ULAbs _ _ _ -> travers (Tr $ (r, (True, (LUP $ up2int up_a, computeBP' r up_x))):(x_e, (b_x, (LUP up_x, bi_x))):trs) bv (len+1) False
          _           -> travers (Tr $ (r, (True, (    up_a, computeBP' r up_x))):(x_e, (b_x, (LUP up_x, bi_x))):trs) bv (len+1) False
    -- (BVar) rule
    True  -> case isBinderApplied (Tr tr) z len of
      Just (n, i) -> -- trace ("True\n" ++ show n ++ "\n") $
        case n of
          ULAbs _ _ _ -> travers (Tr $ (n, (True, (if up_x == 0 then LUP 0 else CAP up_x, computeBP n i))):tr) bv (len + 1) False
          _           -> travers (Tr $ (n, (True, (LUP up_x, computeBP n i))):tr) bv (len + 1) False
      Nothing     -> --trace ("False\n") $
        if hn == False then travers (hideNodes (Tr tr) len) bv len True
        else if up_x == 0 then Tr tr -- $ (x_e, (True, (LUP up_x, bi_x))):trs
             else case drop (len - up_x) tr of
               tr'@((ULApp _ _ r, (_, (up_a, _))):_) -> case r of
                 ULAbs _ _ _ -> travers (Tr $ (r, (True, (LUP $ up2int up_a, computeBP' r up_x))):(x_e, (b_x, (LUP up_x, bi_x))):trs) bv (len+1) False
                 _           -> travers (Tr $ (r, (True, (    up_a, computeBP' r up_x))):(x_e, (b_x, (LUP up_x, bi_x))):trs) bv (len+1) False
  (ULVar _ z, (_, (CAP up_x, _))) -> error "travers: (VAR): variable has a CAP pointer"

  -- (App) rule
  (ULApp _ e _, (_, (LUP up_x, _))) -> let
      up_e = case e of
        ULAbs _ _ _ -> CAP len
        _           -> LUP len
    in travers (Tr $ (e, (True, (up_e, computeBP e len))):tr) bv (len + 1) False
  (ULApp _ e _, (_, (CAP up_x, _))) -> error "travers: (App): application has a CAP pointer"

  -- (Lam) rule
  (ULAbs _ v e, (_, (CAP up_x, _))) -> case e of
    ULAbs _ _ _ -> case drop (len - up_x) tr of
      (_, (_, (LUP up_x', _))):_ -> travers (Tr $ (e, (True, (if up_x' == 0 then LUP 0 else CAP up_x', DCP len))):tr) bv (len + 1) False
      p                    -> error $ "travers: (Lam): application has a CAP pointer i)" ++ show p
    _           -> case drop (len - up_x) tr of
      (_, (_, (LUP up_x', _))):_ -> travers (Tr $ (e, (True, (LUP up_x', computeBP e len))):tr) bv (len + 1) False
      _                    -> error "travers: (Lam): application has a CAP pointer ii)"
  (ULAbs _ v e, (_, (LUP up_x, _))) ->
    travers (Tr $ (e, (True, (LUP up_x, computeBP e len))):tr) bv (len + 1) False
  where
    computeBP :: UntypedLambda -> Int -> BinderPointer
    computeBP e i = case e of
      ULVar _ z | elem z bv -> findDynamicBinder z (Tr (drop (len - i) tr)) i
      _ -> LCP i
    computeBP' e i = case computeBP e i of
      LCP j -> DCP j
      k ->k

hideNodes :: Traversal -> Int -> Traversal
hideNodes (Tr tr) len =
  --trace ("hideNodes: " ++ show len) $
  let
    (tr1, l) = hideNodes' tr len []
    (tr1', l1) = {- trace ("two "++ show l) $ -} hideNodes' tr1 len l
  in 
    --trace ("hideNodes: " ++ show len ++ " " ++ show l1) $ 
    Tr $ tr1' where
    hideNodes' :: [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))]
      -> Int -> [Int]
      -> ([(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))], [Int])
    hideNodes' [] 0 is = ([],is)
    hideNodes' tr'@(x@(x_e, (_, (CAP cap, bi_x))):trs) len is =
      let
        is' = len : cap : is
        (t, l) = hideNodes' trs ((-) len 1) is'
      in ((x_e, (False, (CAP cap, bi_x))):t , l)
    hideNodes' (x@(x_e, (_, (up_x, BIP i))):trs) len is
      | i /= 0 = if member i is
        then let
            is' = len : is
            (t, l) = hideNodes' trs ((-) len 1) is'
          in {-trace ("hideNode' BIP case member : " ++ show (Tr $ x : trs)) $ -}((x_e, (False, (up_x, BIP i))):t, l)
        else let
            (t, l) = hideNodes' trs ((-) len 1) is
          in {-trace ("hideNode' BIP case otherwise : " ++ show (Tr $ x : trs) ++ " " ++ show is ++ " " ++ show i) $-} (x:t, l)
    hideNodes' (x@(x_e, (_, (bp_x, bi_x))):trs) len is =
      let (t, l) = hideNodes' trs ((-) len 1) is
      in {-trace ("hideNode' general case : " ++ show (Tr $ x : trs)) $-} if member len is
        then ((x_e, (False, (bp_x, bi_x))) : t, l)
        else (x : t, l)

normalize :: UntypedLambda -> Traversal
normalize t =
  let bv = computeBoundVariables  t
  in travers (Tr [(t, (True, (LUP 0, BIP 0)))]) bv 1 False

annotate :: ULambda -> UntypedLambda
annotate t = fst $ snd $ annotate' t '\1024' 1 where
  annotate' (UVar v) l i = (chr (ord l + 1), (ULVar (show l) v, i))
  annotate' (UApp e1 e2) l i =
    let
      (l1, (e1', i')) = annotate' e1 l i
      (l2, (e2', i'')) = annotate' e2 l1 (i' + 1)
    in (chr (ord l2 + 1), (ULApp (show i') e1' e2', i''))
  annotate' (UAbs x e) l i =
    let (l', (e', i')) = annotate' e l i
    in (chr (ord l' + 1), (ULAbs (show l') x e', i'))

run_examples xs =
  map (\x -> case parse parseExpr "" (filter (not . isSpace) x) of
    Right term -> normalize $ annotate term) xs

main = writeFile "examples.tex" $ showPdf (run_examples examples) examples examples_names