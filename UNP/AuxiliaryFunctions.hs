module AuxiliaryFunctions where

import qualified Data.Map.Strict as M
import           DataTypes

--- =================
---    Term -> Exp
--- =================

term2Exp :: Term -> Exp
term2Exp = term2Exp' [] 0 where
  term2Exp' :: [(Var, Int)] -> Int -> Term -> Exp
  term2Exp' binders level ((:!!) x) =
    case lookup x binders of
      Just i  -> Bound $ level - i
      Nothing -> Free x
  term2Exp' binders level (a :@@ b) =
    a' `App` b' where
    a' = term2Exp' binders level a
    b' = term2Exp' binders level b
  term2Exp' binders level (x :>> a) =
    Lam $ term2Exp' ((x,level'):binders) level' a where level' = level + 1

--- =================
---    Exp -> Term
--- =================

exp2Term :: Exp -> Term
exp2Term = snd . (exp2Term' nameGen []) where
  --- names -> bound names -> Exp -> (new names, Term)
  exp2Term' :: [Var] -> [Var] -> Exp -> ([Var], Term)
  exp2Term' ns     bs (Free  v) = (ns, (:!!) v)
  exp2Term' ns     bs (Bound i) = (ns, (:!!) $ head $ drop i bs)
  exp2Term' (n:ns) bs (Lam   a) = (ns', n :>> a') where
    (ns' , a') = exp2Term' ns (n:bs) a
  exp2Term' ns     bs (App a b) = (ns'', a' :@@ b') where
    (ns' , a') = exp2Term' ns  bs a
    (ns'', b') = exp2Term' ns' bs b
  -- nameGen generates an infinite sequence of unique names
  nameGen :: [Var]
  nameGen = [[i] | i <- ['a' .. 'z']] ++ [i : show j | i <- ['a' .. 'z'], j <- [1..]]

-- ========================
--     Alpha-equvalence
-- ========================

-- Functions areExpsEqUpToFV and areTermsEqUpToFV return
--   "Just" a renaming of free variables in case arguments are alpha-equivalent up to
--     free variables renaming
--   and return "Nothing" otherwise

type NameMap = M.Map Var Var

areExpsEqUpToFV :: Exp -> Exp -> Maybe NameMap
areExpsEqUpToFV = areExpsEqUpToFV' M.empty where
  areExpsEqUpToFV' :: NameMap -> Exp -> Exp -> Maybe NameMap
  areExpsEqUpToFV' m (Free  x) (Free  y)
    | m M.!? x == Just y  = Just m
    | m M.!? x == Nothing = Just $ M.insert x y m
    | otherwise         = Nothing
  areExpsEqUpToFV' m (Bound i) (Bound j)
    | i == j    = Just m
    | otherwise = Nothing
  areExpsEqUpToFV' m (Lam a  ) (Lam b  ) = areExpsEqUpToFV' m a b
  areExpsEqUpToFV' m (App a b) (App c d) =
    (>>=) (areExpsEqUpToFV' m a c) (\x -> areExpsEqUpToFV' x b d)
  areExpsEqUpToFV' _ _ _ = Nothing

areTermsEqUpToFV :: Term -> Term -> Maybe NameMap
areTermsEqUpToFV a b = areExpsEqUpToFV (term2Exp a) (term2Exp b)

-- Functions areExpsAlphaEq and areTermsAlphaEq returns True iff
--   arguments are alpha-equivalent
areExpsAlphaEq  :: Exp  -> Exp  -> Bool
areExpsAlphaEq  a b = case areExpsEqUpToFV  a b of
  Just m  -> M.null $ M.filterWithKey (/=) m
  Nothing -> False
areTermsAlphaEq :: Term -> Term -> Bool
areTermsAlphaEq a b = case areTermsEqUpToFV a b of
  Just m  -> M.null $ M.filterWithKey (/=) m
  Nothing -> False
