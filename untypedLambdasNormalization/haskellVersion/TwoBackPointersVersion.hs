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

-- -> Maybe (Application Child, Application позиция в траверсал?)
-- :: ... -> Maybe (ULambda, Int)
isBinderApplied :: Traversal -> String -> Int -> Maybe (UntypedLambda, Int)
isBinderApplied (Tr tr@((_, (_, (_, BIP bip))):_)) z len = let
    tr' = drop (len - bip) tr
  in case tr' of
    (ULAbs _ x _, (_, (CAP cap, _))):_ -> case drop (bip - cap) tr' of
      (ULApp _ _ r, (_, (_, _))):_ -> Just (r, cap)
      _ -> error "isBinderApplied: not an abstraction by BIP from Variable i)"
    -- TODO: м.б. поменять
    (ULAbs _ x _, (_, (LUP lup, _))):_ -> Nothing
    _ -> error "isBinderApplied: not an abstraction by BIP from Variable ii)"
isBinderApplied tr _ _ = error $ "isBinderApplied: not a BIP pointer on input" ++ show tr

travers :: Traversal -> [String] -> Int -> Traversal
travers (Tr tr@(x@(x_e, (b_x, (up_x, bi_x))):trs)) bv len = case x of
  --trace (show (Tr tr) ++ "\n") $ case x of
  -- (_VAR) rules
  (ULVar _ z, (_, (LUP up_x, _))) -> case elem z bv of
    -- (FVAR) rule
    -- TODO: дописать
    False -> if up_x == 0 then Tr $ (x_e, (True, (LUP up_x, bi_x))):trs
      else case drop (len - up_x) tr of
        tr'@((ULApp _ _ r, (_, (up_a, _))):_) -> case r of
          ULAbs _ _ _ -> travers (Tr $ (r, (False, (LUP $ up2int up_a, computeBP' r up_x))):(x_e, (True, (LUP up_x, bi_x))):trs) bv (len+1)
          _           -> travers (Tr $ (r, (False, (    up_a, computeBP' r up_x))):(x_e, (True, (LUP up_x, bi_x))):trs) bv (len+1)
    -- (BVar) rule
    -- TODO: дописать
    True  -> case isBinderApplied (Tr tr) z len of
      Just (n, i) -> -- trace ("True\n" ++ show n ++ "\n") $
        case n of
          ULAbs _ _ _ -> travers (Tr $ (n, (False, (if up_x == 0 then LUP 0 else CAP up_x, computeBP n i))):tr) bv (len + 1)
          _           -> travers (Tr $ (n, (False, (LUP up_x, computeBP n i))):tr) bv (len + 1)
      -- TODO: дописать
      --Nothing     -> Tr tr
      Nothing     -> --trace ("False\n") $
        if up_x == 0 then Tr $ (x_e, (True, (LUP up_x, bi_x))):trs
        else case drop (len - up_x) tr of
          tr'@((ULApp _ _ r, (_, (up_a, _))):_) -> case r of
            ULAbs _ _ _ -> travers (Tr $ (r, (False, (LUP $ up2int up_a, computeBP' r up_x))):(x_e, (True, (LUP up_x, bi_x))):trs) bv (len+1)
            _           -> travers (Tr $ (r, (False, (    up_a, computeBP' r up_x))):(x_e, (True, (LUP up_x, bi_x))):trs) bv (len+1)
  (ULVar _ z, (_, (CAP up_x, _))) -> error "travers: (VAR): variable has a CAP pointer"

  -- (App) rule
  (ULApp _ e _, (_, (LUP up_x, _))) -> let
      up_e = case e of
        ULAbs _ _ _ -> CAP len
        _           -> LUP len
    in travers (Tr $ (e, (False, (up_e, computeBP e len))):tr) bv (len + 1)
  (ULApp _ e _, (_, (CAP up_x, _))) -> error "travers: (App): application has a CAP pointer"

  -- (Lam) rule
  (ULAbs _ v e, (_, (CAP up_x, _))) -> case e of
    ULAbs _ _ _ -> case drop (len - up_x) tr of
      (_, (_, (LUP up_x', _))):_ -> travers (Tr $ (e, (False, (if up_x' == 0 then LUP 0 else CAP up_x', DCP len))):tr) bv (len + 1)
      p                    -> error $ "travers: (Lam): application has a CAP pointer i)" ++ show p
    _           -> case drop (len - up_x) tr of
      (_, (_, (LUP up_x', _))):_ -> travers (Tr $ (e, (False, (LUP up_x', computeBP e len))):tr) bv (len + 1)
      _                    -> error "travers: (Lam): application has a CAP pointer ii)"
  -- TODO: дописать
  --(ULAbs _ v e, (_, (LUP up_x, _))) -> Tr tr
  (ULAbs _ v e, (_, (LUP up_x, _))) ->
    travers (Tr $ (e, (False, (LUP up_x, computeBP e len))):tr) bv (len + 1)
  where
    -- :: ... -> BinderPointer
    computeBP :: UntypedLambda -> Int -> BinderPointer
    computeBP e i = case e of
      ULVar _ z | elem z bv -> findDynamicBinder z (Tr (drop (len - i) tr)) i
      ULVar _ z | otherwise -> BIP 0
      _ -> LCP i
    computeBP' e i = case computeBP e i of
      LCP j -> DCP j
      k ->k


--TODO: hideNodes

normalize :: UntypedLambda -> Traversal
normalize t =
  let bv = computeBoundVariables  t
  in travers (Tr [(t, (False, (LUP 0, BIP 0)))]) bv 1

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

run_examples xs =
  map (\x -> case parse parseExpr "" (filter (not . isSpace) x) of
    Right term -> normalize $ annotate term) xs

main = writeFile "examples.tex" $ showPdf (run_examples examples) examples