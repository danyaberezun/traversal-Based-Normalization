module DataTypes where

import Data.List

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
data UnfinishedPointer = CAP Int | LUP Int deriving (Show, Eq)
data BinderPointer     = BIP Int | LCP Int | RCP Int | DCP Int deriving (Show, Eq)
newtype Traversal = Tr [(UntypedLambda, (Bool, (UnfinishedPointer, BinderPointer)))] deriving (Eq)
instance Show Traversal where
  show (Tr tr) = show' (reverse tr) 1 where
    show' [] _ = ""
    show' (x:xs) i =
      -- change 350 for something greater if program goes to infinite loop
      -- up2 i ++ ". " ++ show1 x 350 ++ "\n" ++ show' xs ((+) i 1)
      up2 i ++ ". " ++ show1 x 70 ++ "\n" ++ show' xs ((+) i 1)
      where
        up2h (CAP i) = "_CAP_"++ up2 i
        up2h (LUP i) = "_LUP_"++ up2 i
        up2u (BIP i) = "_BIP_"++ up2 i
        up2u (LCP i) = "_LCP_"++ up2 i
        up2u (RCP i) = "_RCP_"++ up2 i
        up2u (DCP i) = "_DCP_"++ up2 i
        up2 i
          | i < 10    = "_" ++ show i
          | otherwise = show i
        upb True  = "True_"
        upb False = "False"
        show1 (t, (b, (hp, un))) l =
          let
            st = show t
            lt = (-) l (length st)
          in st ++ spac lt ++ upb b ++ "_" ++ up2h hp ++ "_" ++ up2u un
        spac 0  = ""
        spac ltt = "_" ++ (spac ((-) ltt 1))

up2int :: UnfinishedPointer -> Int
up2int (LUP i) = i
up2int (CAP i) = i
bp2int :: BinderPointer -> Int
bp2int (BIP i) = i
bp2int (LCP i) = i
bp2int (RCP i) = i
bp2int (DCP i) = i