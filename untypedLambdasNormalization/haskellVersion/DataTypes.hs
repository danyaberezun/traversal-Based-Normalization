module DataTypes where

import Data.List

-- untyped simple lambda expression
data UntypedLambda = ULVar String String
  | ULApp String UntypedLambda UntypedLambda
  | ULAbs String String UntypedLambda
  deriving (Eq, Ord)
instance Show UntypedLambda where
  --show (ULVar _ v)                   = v
  --show (ULApp _ e1@(ULAbs _ _ _) e2) = "(" ++ show e1 ++ ")" ++ show e2
  --show (ULApp _ e (ULVar _ v))       = show e ++ v
  --show (ULApp _ e1 e2)               = show e1 ++ "(" ++ show e2 ++ ")"
  --show (ULAbs _ v e)                 = "$\\lambda$" ++ v ++ " . " ++ show e
  show (ULVar _ v)                   = v
  show (ULApp i e1 e2)               = "$@_{" ++ i ++ "}$"
  show (ULAbs _ v e)                 = "$\\lambda$" ++ v

data ULambda = UVar String
  | UApp ULambda ULambda
  | UAbs String ULambda
instance Show ULambda where
  show (UVar v)                = v
  show (UApp e1@(UAbs _ _) e2) = "(" ++ show e1 ++ ")" ++ show e2
  show (UApp e (UVar v))       = show e ++ v
  show (UApp e1 e2)            = show e1 ++ "(" ++ show e2 ++ ")"
  show (UAbs v e)              = "\\" ++ v ++ " . " ++ show e

-- term (is the end of sub-traversal, (history pointer, (pointer to last unfinished application, (lambda associate pointer, binder pointer)))
data UnfinishedPointer = CAP Int | LUP Int | PAUSE Int deriving (Show, Eq)
data BinderPointer     = BIP Int | LCP Int | RCP Int | DCP Int deriving (Show, Eq)
newtype Traversal = Tr [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))] deriving (Eq)
instance Show Traversal where
  show (Tr tr) = show' tr' 1 where
    tr' = reverse tr
    lenn = 20
    show' [] _ = ""
    show' (x:xs) i =
      -- change 350 for something greater if program goes to infinite loop
       --up2 i ++ ". " ++ show1 x 350 ++ "\n" ++ show' xs ((+) i 1)
      up2 i ++ ". " ++ show1 x lenn ++ "\n\\\\" ++ show' xs ((+) i 1)
      where
        up2h (CAP   i) = "\\ \\ CAP\\ \\ " ++ up2 i
        up2h (LUP   i) = "\\ \\ LUP\\ \\ " ++ up2 i
        up2h (PAUSE i) = "\\ PAUSE\\ " ++ up2 i
        up2u (BIP   i) = "\\ \\ BIP\\ \\ " ++ up2 i
        up2u (LCP   i) = "\\ \\ LCP\\ \\ " ++ up2 i
        up2u (RCP   i) = "\\ \\ RCP\\ \\ " ++ up2 i
        up2u (DCP   i) = "\\ \\ DCP\\ \\ " ++ up2 i
        up2 i
          | i < 10     = "\\ \\ " ++ show i
          | i < 100    = "\\ " ++ show i
          | otherwise = show i
        upb True  = "True "
        upb False = "False"
        show1 (t, (b, (hp, un))) l =
          let
            st = show t
            lt = (-) l (length st)
          in st ++ "\\hspace*{\\fill}" ++ spac lt ++ upb b ++ " " ++ up2h hp ++ " " ++ up2u un
        spac 0  = ""
        spac ltt = " " ++ (spac ((-) ltt 1))

up2int :: UnfinishedPointer -> Int
up2int (LUP i) = i
up2int (CAP i) = i
up2int (PAUSE i) = i
bp2int :: BinderPointer -> Int
bp2int (BIP i) = i
bp2int (LCP i) = i
bp2int (RCP i) = i
bp2int (DCP i) = i