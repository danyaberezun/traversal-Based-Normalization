-- ============================================================================
-- ============================================================================
--    Traversal-Based Normalization algorithm for Untyped Lambda-Calculus
--    as described in section 3.5 of PhD-thesis
--    Function unp :: Expression -> Traversal
-- ============================================================================
-- ============================================================================

module UNP (unp) where

import Debug.Trace
import DataTypes
import UNPDataTypes
import Prelude hiding (lookup)

-- ======================================
--   Run the traversal generator
-- ======================================

unp :: Exp -> H
unp e = eval e alpha bh ch h where
  alpha = Strong
  bh    = []
  ch    = []
  h     = [It e alpha bh ch]

-- ======================================= 
--   EVALUATION OF EXPRESSIONS 
-- =======================================

eval :: Exp -> Flag -> BH -> CH -> H -> H
eval e@(Free  x) _      _  ch h = apk e ch h
eval e@(Lam   a) Weak   _  ch h = apk e ch h 
eval   (Lam   a) Strong _  ch h = eval a Strong h  ch ((It a Strong h  ch):h)
eval   (App a b) _      bh ch h = eval a Weak   bh h  ((It a Weak   bh h ):h)
eval   (Bound i) f      bh ch h = lookup i f bh ch h

-- ====================================
--     BINDER HISTORY: find variable 
-- ====================================

lookup :: Int -> Flag -> BH -> CH -> H -> H
lookup 0 alpha ((It _ Weak _ ch'):h') ch h =
 case ch' of 
  (It apn _ bh _):_ -> evoperand (It apn alpha bh ch) h
  _                 -> case ch of
    []                    -> h
    (It ap _ bh'' ch''):_ -> evoperand (It ap Strong bh'' ch'') h
lookup 0 _     ((It _ Strong _   ch'):h') ch h = apk (Bound 1) ch h 
lookup i alpha ((It _ _      bh' _  ):_ ) ch h = lookup (i-1) alpha bh' ch h

-- =========================
--   APPLY CONTROL HISTORY 
-- =========================

apk :: Exp -> CH -> H -> H
apk _       []                     h = h
apk (Lam a) ((It _     f bh ch):_) h = eval a f h ch ((It a f h ch):h)
apk _       ((It alpha _ bh ch):_) h = evoperand (It alpha Strong bh ch) h

-- ========================================================================
--  "The Trick" : Find operand of dynamic application, and make it static  
-- ========================================================================

evoperand :: Item -> H -> H
evoperand (It (App _ b) f bh ch) h = eval b f bh ch ((It b f bh ch):h)
evoperand (It e         _ _  _ )  _ =
  error ("Function evoperand: ERROR: expected an application; given: "
         ++ topExp2String e)
