module UNPDataTypes where

import DataTypes
import Data.List

-- ==========================================
--   New DataTypes: a traversal History "H"
-- ==========================================

type H    = [Item]  -- Item is a history element (aka token)
type CH   = H       -- Control history (realises continuation)
type BH   = H       -- Binder  history (realises environment)
data Flag =         -- Flag in Item
  Weak | Strong deriving (Eq, Ord)
data Item = It Exp Flag BH CH deriving(Ord)

-- =================================
--   Input and output format stuff
-- =================================

topExp2String :: Exp -> String
topExp2String (App  {}) = "App"
topExp2String (Lam   e) = "Lam "
topExp2String (Free  x) = "Free " ++ x
topExp2String (Bound i) = "Bound " ++ show i

numstr :: Int -> String
numstr n = if n<10 then [['0'..'9']!!n] 
                   else (numstr (div n 10)) ++ (numstr (mod n 10))

instance Eq Item where
  (It e1 _ bh1 ch1) == (It e2 _ bh2 ch2) = e1 == e2 && bh1 == bh2 && ch1 == ch2

-- ==========
--   Show
-- ==========
instance Show Flag where
  show Weak   = "Weak"
  show Strong = "Strong"

instance Show Item where
  show (It e alpha bh h) = doLen (topExp2String e) 10 ++ " | "
    ++ doLen (show alpha      ) 6 ++ " | "
    ++ doLen (show (length bh)) 5 ++ " | "
    ++ doLen (show (length h )) 5
  showsPrec _ it s = "Item " ++ show it ++ s
  showList l = showString . snd .
    (foldl (\(i,acc) x -> (i-1, doLen (show i) 5 ++ show x ++ "\n" ++ acc))
           (length l, ""))
    $ l

doLen s l
  | l <= len  = s
  | otherwise = s ++ [a | a <- " ", j <- [1..(l - len)]]
  where len = length s
