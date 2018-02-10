module DataTypes where

type Var = String

--- ================================
---    Input expression data type  
--- ================================

infixl 8 :@@
infixr 7 :>>
data Term =
    (:!!)    Var  -- variable
  | Term :@@ Term -- application
  | Var  :>> Term -- abstraction
  deriving (Eq, Read)

instance Show Term where
  show (x  :>> e ) = "\\ " ++ x ++ " . " ++ show e
  show ((:!!)  x ) = x
  show (e1 :@@ e2) = abr (show e1) ++ " @ " ++ bbr (show e2) where
    abr = case e1 of
      (:>>) {}  -> (\s -> "(" ++ s ++ ")")
      otherwise -> id
    bbr = case e2 of
      (:@@) {}  -> (\s -> "(" ++ s ++ ")")
      otherwise -> id

--- ===============================================
---    Expression data type (for internal usage)
--- ===============================================

--- Locally-nameless lambda-calculus representation
data Exp =
    Free  Var     -- free variable
  | Bound Int     -- bound variables (deBruijn notation)
  | App   Exp Exp -- application (numbers are generated automatically)
  | Lam   Exp     -- anonymous abstraction
  deriving (Eq, Ord)

instance Show Exp where
  show (Lam   e) = "\\. " ++ show e
  show (Bound i) = show i
  show (Free  x) = x
  show (App a b) = abr (show a) ++ " @ " ++ bbr (show b) where
    abr = case a of
      Lam {}    -> (\s -> "(" ++ s ++ ")")
      otherwise -> (\s -> "(" ++ s ++ ")") -- id
    bbr = case b of
      App {}    -> (\s -> "(" ++ s ++ ")")
      otherwise -> (\s -> "(" ++ s ++ ")") -- id
