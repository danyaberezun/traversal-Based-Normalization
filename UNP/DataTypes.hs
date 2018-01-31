module DataTypes where
import Debug.Trace

type Var = String 

data Exp   = 
      V Var           -- bound variable in input expression
    | FREE Var        -- free variable
    | Bound Var Int   -- bound variable plus deBruijn tag
    | App Int Exp Exp -- application
    | Lam Var Exp     -- abstraction
    | Bugexp 
  deriving (Eq)
  --deriving (Eq, Show)

