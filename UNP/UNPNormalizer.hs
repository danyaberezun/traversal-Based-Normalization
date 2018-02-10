-- ============================================================================
-- ============================================================================
--    Traversal-Based Normalization algorithm for Untyped Lambda-Calculus:
--    as described in section 3.5 of PhD-thesis:
--    Functions:
--    extractNormalFormFromTheTraversal :: Traversal -> NormalForm
--    unpCleanup                        :: Traversal -> Cleaned up Treaversal
-- ============================================================================
-- ============================================================================

module UNPNormalizer (extractNormalFormFromTheTraversal,unpCleanup) where

import           Debug.Trace
import           DataTypes
import           UNPDataTypes
import           Prelude hiding (lookup)
import qualified Data.Set  as Set

-- ===============================================================================
-- Function unpCleanup cleanups a final traversal:
-- it removes all prime redexes (see last but one cleanup' case)
--            and all bound variables being substituted (see cleanup' secod case)
--                    (== whose anstractions form prime redexes)
-- ===============================================================================

-- TermTop represent a token of cleanup history;
--   it completely ignores everything except
--   token type (abstraction, variable or application)
data TermTop = TTV Var | TTA | TTL Var deriving (Show)

-- extractNormalFormFromTheTraversal:
--  works in two steps:
--    1. Cleanup the history (see function unpCleanup)
--       The cleaned up history is a depth-first traversal of the AST of the normal form
--    2. Build the term from the cleaned up history (see function buildTerm)
extractNormalFormFromTheTraversal :: H -> Term
extractNormalFormFromTheTraversal = buildTerm . unpCleanup

buildTerm :: [TermTop] -> Term
buildTerm = fst . buildTerm' where
  buildTerm' :: [TermTop] -> (Term,[TermTop])
  buildTerm' ((TTA):ts) =
    let (t1, ts1) = buildTerm' ts
        (t2, ts2) = buildTerm' ts1
    in (t1 :@@ t2, ts2)
  buildTerm' ((TTL x):ts) =
    let (e, ts') = buildTerm' ts
    in (x :>> e, ts')
  buildTerm' ((TTV x):ts) = ((:!!) x, ts)

-- Function unpCleanup by a given traversal returns a list of tokens (TermTop).
-- This list is a depth-first traversal of the AST of the normal form of the
-- input term.
-- Function unpCleanup wotks in 2 steps:
--   1. Compute a set of indexes to be excluded from
--      the traversal (see function cleanup')
--   2. Run function filtTraversal cleans up traversal with respect to the set
--      computed on the previous step
--      and transforms survived element into tokens (TermTop).
unpCleanup :: H -> [TermTop]
unpCleanup h = filtTraversal h where
  len = length h       -- traversal length
  s   = cleanup' len h -- a set of indexes to be excluded from the traversal
  filtTraversal :: H -> [TermTop]
  filtTraversal =
    snd . (foldl
      (\ (l,nh) it ->
         if Set.member l s
         then (l-1,nh)
         else (l-1,(toTermTop it l):nh)
        )
      (len,[]))

  -- Function cleanup' conputes a set of indexes to be excluded from the traversal
  -- Function cleanup' :: current traversal length ->
  --                      traversal ->
  --                      a set of indexes to be excluded from the traversal
cleanup' :: Int -> H -> Set.Set Int
cleanup' _   [] = Set.empty
-- Bound variable case
cleanup' l (it@(It (Bound i) _     bh _):hs) =
  -- Does the variable abstrcation form any prime redex?
  if elem (getBoundAndstInd i bh) hs'
  -- Bound variable had been substitued
  then Set.insert l hs'
  -- Bound variable hab not been substituted
  else hs'
  where hs' = cleanup' (l-1) hs
-- The abstraction doesn't form a prime redex
cleanup' l (   (It (Free  _) _    _ _ ):hs) = cleanup' (l-1) hs
cleanup' l (it@(It (Lam   _) Weak _ ch):hs) =
  Set.insert l $ Set.insert (length ch) hs'
  where hs' = cleanup' (l-1) hs
cleanup' l (_:hs) = cleanup' (l-1) hs

-- ============================
--     Auxiliary functions
-- ============================

-- getBoundAndstInd :: i -> h -> ind
-- Function getBoundAndstInd returns the index 'ind' of the abstraction
-- of bound variable with deBruijn index 'i' in history 'bh'
getBoundAndstInd :: Int -> BH -> Int
getBoundAndstInd _ [] = error "getBoundAndstInd: an incorrect traversal"
getBoundAndstInd 0 h@((It (Lam _) _ _  _):_) = length h
getBoundAndstInd i   ((It _       _ bh _):_) = getBoundAndstInd (i-1) bh

-- Function toTermTop by an Item and its index in the traversal
-- builds a correspondinf token TermTop
-- Note that in TermTop abstraction is not anonimous
--                      and there are no nameless variables
-- In order to provide unique names for bound variables
--   and avoid name conflicts we set a name of each bound variable
--   to be equal to its abstraction index inside the original traversal
toTermTop (It (App _ _) _ _  _) _ = TTA
toTermTop (It (Lam   _) _ _  _) l = TTL $ show l
toTermTop (It (Free  x) _ _  _) l = TTV x
toTermTop (It (Bound i) _ bh _) l = TTV $ show $ getBoundAndstInd i bh
