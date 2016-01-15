module DataTypes where
import Data.List
import qualified Data.Map as Map

--=========================================================================
--  file contains data types that is used on all stages of this algorithm
--=========================================================================

-- environment for type-inference
type Environment = Map.Map UntypedLambda SimpleType

-- untyped simple lambda expression
data UntypedLambda = ULVar String
  | ULApp UntypedLambda UntypedLambda
  | ULAbs String UntypedLambda
  deriving (Eq, Ord)
instance Show UntypedLambda where
  show (ULVar v)                 = v
  show (ULApp e1@(ULAbs _ _) e2) = "(" ++ show e1 ++ ")" ++ show e2
  show (ULApp e (ULVar v))       = show e ++ v
  show (ULApp e1 e2)             = show e1 ++ "(" ++ show e2 ++ ")"
  show (ULAbs v e)               = "\\" ++ v ++ " . " ++ show e

-- type of simple types
data SimpleType = AtomType
  | TyVar String
  | Arrow SimpleType SimpleType
  deriving (Eq, Ord)
instance Show SimpleType where
  show AtomType                   = "o"
  show (TyVar name)               = name
  show (Arrow AtomType        t2) = "o -> " ++ show t2
  show (Arrow (TyVar name) t2)    = name ++ " -> " ++ show t2
  show (Arrow t1           t2)    = "(" ++ show t1 ++ ") -> " ++ show t2

type Var     = String
-- types a la Church
data ChType  = O | P ChType ChType deriving (Eq)
instance Show ChType where
  show O                 = "o"
  show (P t1@(P _ _) t2) = "(" ++ show t1 ++ ")->" ++ show t2
  show (P O t2)          = "o->" ++ show t2
-- typed variables
type AnnVar  = (Var, ChType)
type AnnVars = [AnnVar]
-- typed LamChlbda expressions a la Church
data ChL     = LamChl  AnnVars ChL  | App  ChL  ChL    | V  Var deriving (Eq)
-- typed LamChlbda expressions a la Church with long application
data ChL2    = LamChl2 AnnVars ChL2 | App2 ChL2 [ChL2] | V2 Var deriving (Eq)
instance Show ChL where
  show (LamChl vs t)  = "\\" ++ show' vs ++ " . " ++ show t where
    show' []          = ""
    show' ((v, t):vs) = v ++ " : " ++ show t ++ " " ++ show' vs
  show (App t1 t2)    = "(" ++ show t1 ++ " @ " ++ show t2 ++ ")"
  show (V n)          = n
instance Show ChL2 where
  show (LamChl2 vs t) = "\\" ++ show' vs ++ " . " ++ show t where
    show' []          = ""
    show' ((v, t):vs) = v ++ " : " ++ show t ++ " " ++ show' vs
  show (App2 t1 t2)   = "(" ++ show t1 ++ " @ " ++ show'' t2 ++ ")" where
    show'' []         = ""
    show'' (t:ts)     = "(" ++ show t ++ ")" ++ show'' ts
  show (V2 n)         = n 

-- grammar for eta-long form
type Vars   = [Var]
data B      = At As | CB Var As deriving (Eq)
instance Show B where
  show (At as)   = fst $ mapAccumL (\acc a -> (acc ++ "(" ++ show a ++ ")", a)) "@ " as
  show (CB v as) = fst $ mapAccumL (\acc a -> (acc ++ "(" ++ show a ++ ")", a)) (v ++ " ") as
  show _ = "Show B error"
data A      = Lam Vars B deriving (Eq)
instance Show A where
  show (Lam vs b) = (fst $ mapAccumL (\acc v -> (acc ++ " " ++ v, v)) "\\" vs) ++ " . " ++ show b
  show _ = "Show A error"
type As     = [A]
-- eta-long form
data LNF    = Root A deriving Show