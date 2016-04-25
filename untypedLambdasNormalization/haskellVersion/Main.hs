module Main where

import           Data.Char
import           Data.List                     ()
import qualified Data.Map                      as Map ()
import           Data.Maybe                    ()
import           Debug.Trace                   ()
import           Text.ParserCombinators.Parsec

import           AuxiliaryFunctions
import           DataTypes
import           Examples
import           Parsing
import           ToPdf

computeBoundVariables :: UntypedLambda -> [String]
computeBoundVariables t = computeBoundVariables' t [] where
  computeBoundVariables' (ULAbs _ x  e ) xs = computeBoundVariables' e  (x:xs)
  computeBoundVariables' (ULApp _ e1 e2) xs =
    computeBoundVariables' e1 (computeBoundVariables' e2 xs)
  computeBoundVariables' _ xs = xs

travers :: Traversal -> [String] -> Int -> Bool -> Traversal
travers (Tr []) _ _ _ = error "travers: empty traversal"
travers (Tr tr@(x@(x_e, (b_x, (_, bi_x))):trs)) bv len hn = case x of
  --trace (show (Tr tr) ++ "\n") $ case x of
  -- (_VAR) rules
  (ULVar _ _, (_, (CAP _, _))) -> error "travers: (VAR): variable has a CAP pointer"
  (ULVar _ z, (_, (up_x , _))) ->
    let up_x' = up2int up_x
    in case z `elem` bv of
      -- (FVAR) rule
      False
        | not hn      -> travers (hideNodes (Tr tr) len) bv len True
        | up_x' == 0  -> Tr $ (x_e, (True, (up_x, bi_x))):trs
        | otherwise   -> case drop (len - up_x') tr of
            (ULApp _ _ r, (_, (up_a, _))):_ ->
              travers (Tr $ (r, (True, (PAUSE $ up2int up_a, computeBP' r up_x'))):
                (x_e, (b_x, (up_x, bi_x))):trs) bv (len + 1) False
            _ -> error "travers: (FVAR) rule: invariant is broken 1"
      -- (BVar) rule
      True  -> case isBinderApplied (Tr tr) z len of
        Just (n, i) -> case up_x of
          LUP _ ->
            case n of
              ULAbs {} ->
                travers (Tr $ (n, (True, (if up_x' == 0 then LUP 0 else CAP up_x',
                                          computeBP n i))):tr) bv (len + 1) False
              _        -> travers (Tr $ (n, (True, (LUP up_x', computeBP n i ))):tr)
                                  bv (len + 1) False
          PAUSE _ -> travers (Tr $ (n, (True, (PAUSE up_x', computeBP n i))):tr)
                             bv (len + 1) False
          CAP _ -> error "travers: (BVAR) rule: invariant is broken: \
                         \CAP pointer in BVAR"
        Nothing
          | not hn     -> travers (hideNodes (Tr tr) len) bv len True
          | up_x' == 0 -> Tr tr
          | otherwise  -> case drop (len - up_x') tr of
              (ULApp _ _ r, (_, (up_a, _))):_ ->
                travers (Tr $ (r, (True, (toPause up_a, computeBP' r up_x'))):
                         (x_e, (b_x, (up_x, bi_x))):trs) bv (len+1) False
              tr' -> error ("travers: (BVAR) rule: Nothing: invariant is broken "
                            ++ show tr')

  -- (App) rule
  (ULApp {}, (_, (CAP _, _))) -> error "travers: (App): application has a CAP pointer"
  (ULApp _ e _, (_, (_, _))) -> let
      up_e = case e of
        ULAbs {} -> CAP len
        _        -> LUP len
    in travers (Tr $ (e, (True, (up_e, computeBP e len))):tr) bv (len + 1) False

  -- (Lam) rule
  (ULAbs _ _ e, (_, (CAP up_x, _))) -> case e of
    ULAbs {} -> case drop (len - up_x) tr of
      (_, (_, (LUP   up_x', _))):_ ->
        travers (Tr $ (e, (True, (if up_x' == 0 then LUP 0
                                  else CAP up_x', DCP len))):tr)
                bv (len + 1) False
      (_, (_, (PAUSE up_x', _))):_ ->
        travers (Tr $ (e, (True, (PAUSE up_x', DCP len))):tr)
                bv (len + 1) False
      p -> error $ "travers: (Lam): application has a CAP pointer i)"
                                              ++ show p
    _           -> case drop (len - up_x) tr of
      (_, (_, (LUP   up_x', _))):_ ->
        travers (Tr $ (e, (True, (LUP   up_x', computeBP e len))):tr)
                bv (len + 1) False
      (_, (_, (PAUSE up_x', _))):_ ->
        travers (Tr $ (e, (True, (PAUSE up_x', computeBP e len))):tr)
                bv (len + 1) False
      _ -> error "travers: (Lam): application has a CAP pointer ii)"
  (ULAbs _ _ e, (_, (up_x, _)))     ->
    travers (Tr $ (e, (True, (up_x, computeBP e len))):tr) bv (len + 1) False
  where
    computeBP :: UntypedLambda -> Int -> BinderPointer
    computeBP e i = case e of
      ULVar _ z | z `elem` bv ->
        findDynamicBinder z (Tr (drop (len - i) tr)) i
      _ -> LCP i
    computeBP' e i = case computeBP e i of
      LCP j -> DCP j
      k -> k
    toPause (LUP   p) = PAUSE p
    toPause (CAP   p) = PAUSE p
    toPause (PAUSE p) = PAUSE p
    findDynamicBinder :: String -> Traversal -> Int -> BinderPointer
    findDynamicBinder z tr' len' = findDynamicBinder' z tr' len' tr' where
      findDynamicBinder' z' (Tr []) _ trr =
        error $ "findDynamicBinder : error: empty traversal"
          ++ show z' ++ " tr = "++ show trr
      findDynamicBinder' z' (Tr ((ULAbs _ x' _, _):_)) len'' _ | x' == z' = BIP len''
      findDynamicBinder' z' (Tr tr''@((_, (_, (_, bi_z))):_)) len'' trr
        | bp2int bi_z == len'' =
          error $ "findDynamicBinder' " ++ show bi_z ++ " " ++ show len''
            ++ "\n" ++ show (Tr tr'')
        | otherwise   =
          findDynamicBinder' z' (Tr (drop (len'' - bp2int bi_z) tr''))
          (bp2int bi_z) trr

hideNodes :: Traversal -> Int -> Traversal
hideNodes (Tr tr) len =
  --trace ("hideNodes: " ++ show len) $
  let
    (tr1 , l) = hideNodes' tr len []
    (tr1', _) = {- trace ("two "++ show l) $ -} hideNodes' tr1 len l
  in
    --trace ("hideNodes: " ++ show len ++ " " ++ show l1) $
    Tr tr1' where
    hideNodes' :: [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))]
      -> Int -> [Int]
      -> ([(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))], [Int])
    hideNodes' [] len' is
      | len' == 0  = ([],is)
      | otherwise = error "hideNodes': error: empty traversal with non-zero length"
    hideNodes' ((x_e, (_, (CAP cap, bi_x))):trs) len' is =
      let
        is' = len' : cap : is
        (t, l) = hideNodes' trs ((-) len' 1) is'
      in ((x_e, (False, (CAP cap, bi_x))):t , l)
    hideNodes' (x@(x_e, (_, (up_x, BIP i))):trs) len' is
      | i /= 0 = if member i is
        then let
            is' = len' : is
            (t, l) = hideNodes' trs ((-) len' 1) is'
          in {-trace ("hideNode' BIP case member : " ++ show (Tr $ x : trs)) $ -}
            ((x_e, (False, (up_x, BIP i))):t, l)
        else let
            (t, l) = hideNodes' trs ((-) len' 1) is
          in {-trace ("hideNode' BIP case otherwise : " ++ show (Tr $ x : trs)
                   ++ " " ++ show is ++ " " ++ show i) $-}
            (x:t, l)
    hideNodes' (x@(x_e, (_, (bp_x, bi_x))):trs) len' is =
      let (t, l) = hideNodes' trs ((-) len' 1) is
      in {-trace ("hideNode' general case : " ++ show (Tr $ x : trs)) $-}
        if member len' is
        then ((x_e, (False, (bp_x, bi_x))) : t, l)
        else (x : t, l)

normalize :: UntypedLambda -> Traversal
normalize t =
  let bv = computeBoundVariables  t
  in travers (Tr [(t, (True, (LUP 0, BIP 0)))]) bv 1 False

annotate :: ULambda -> UntypedLambda
annotate t = fst $ snd $ annotate' t '\1024' (1 :: Integer) where
  annotate' :: (Show t, Num t) =>
       ULambda -> Char -> t -> (Char, (UntypedLambda, t))
  annotate' (UVar v) l i = (chr (ord l + 1), (ULVar (show l) v, i))
  annotate' (UApp e1 e2) l i =
    let
      (l1, (e1', i')) = annotate' e1 l i
      (l2, (e2', i'')) = annotate' e2 l1 (i' + 1)
    in (chr (ord l2 + 1), (ULApp (show i') e1' e2', i''))
  annotate' (UAbs x e) l i =
    let (l', (e', i')) = annotate' e l i
    in (chr (ord l' + 1), (ULAbs (show l') x e', i'))

runExamples :: [String] -> [Traversal]
runExamples =
  map (\x -> case parse parseExpr "" (filter (not . isSpace) x) of
    Right term -> normalize $ annotate term
    Left _ -> error $ (++) "runExamples fail to parse input expression " x)

main :: IO ()
main = do
  writeFile "show_traversal.tex" $
    showTraversalPdf
    (runExamples examples_normalize_only)
    examples_normalize_only examples_normalize_only_names
  writeFile "examples.tex" $
    showPdf
    (runExamples examples_picture)
    examples_picture examples_picture_names
  writeFile "examplesNormalForms.tex" $
    showNormalFormPDF
    (runExamples examples_normalize_only)
    examples_normalize_only examples_normalize_only_names
