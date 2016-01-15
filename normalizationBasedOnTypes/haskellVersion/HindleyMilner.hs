module HindleyMilner (typeTerm, simpleTypeToChType) where

--================================================================
--  file contains an algorithm W
--  Main function : typeTerm
--    typeTerm :: Environment -> String -> ChL
--      where Environment contains information about free variable
--        String is a simple lambda expression
--      produces a Chl (typed a la Church lambda expression)
--===============================================================

import qualified Data.Map as Map
import Data.Maybe
import Data.Char
import Text.ParserCombinators.Parsec
import DataTypes

-- exprression to be type infered -> a list of free type names
-- -> current type envinronment
-- -> (new type envinronment, new free type names list) or an error messenge
inferType :: UntypedLambda -> [String] -> Environment -> Either String (Environment, [String])
inferType e@(ULVar n) t@(tv:tvs) env = case Map.lookup e env of
  -- add new type variable
  Nothing -> return (Map.insert e (TyVar tv) env, tvs)
  -- veriable alredy exists in the environment
  Just _  -> return (env, t)
inferType e@(ULAbs n e1) (tv:tvs) env = case Map.lookup (ULVar n) env of
  -- variable n is not used before
  Nothing -> do
    -- infer type of the abstraction body
    (env', tvs') <- inferType e1 tvs env
    -- get the type is just infered
    let Just tp' = Map.lookup e1 env'
    -- lookup for the type of variable n in new envinronment
    case Map.lookup (ULVar n) env' of
      Nothing -> do
        let env'' = Map.insert (ULVar n) (TyVar tv) env'
        return (Map.insert e (Arrow (TyVar tv) tp') env'', tvs')
      Just tp -> return (Map.insert e (Arrow tp tp') env', tvs')
  -- variable n is already used ---> error
  Just tp -> fail ("ERROR: Duplicate bound variable \"" ++ n ++ "\" in lambda-abstraction.")
inferType e@(ULApp e1 e2) t@(tv:tvs) env = do
    -- infer type of the argument
    (env', tvs') <- inferType e2 tvs env
    let Just tp' = Map.lookup e2 env'
    -- case on the syntax form of expression e1
    case e1 of
      ULVar _ -> case Map.lookup e1 env' of
        -- unbound variable ---> e has type tv; e1 has type tv' -> tv where tv is a new type variable
        Nothing -> do return (Map.insert e (TyVar tv) (Map.insert e1 (Arrow tp' (TyVar tv)) env'), tvs')
        -- bound variable with type tp ---> unify types and return the right hand side of unified arrow type
        Just tp -> do
            env'' <- unifyTypes (Arrow tp' (TyVar tv), tp) env'
            let Just (Arrow tp'' tp''') = Map.lookup e1 env''
            return (Map.insert e tp''' env'', tvs')
      ULAbs _ _ -> do
        -- infer type of e1
        (env'', tvs'') <- inferType e1 tvs' env'
        let Just (Arrow tp1 tp2) = Map.lookup e1 env''
        -- check that types of abstraction and argument are compatible
        if areTypesCompatible tp1 tp'
          then do
            -- types are compatible ---> unify them
            env''' <- unifyTypes (tp1, tp') env''
            let Just (Arrow tp1' tp2') = Map.lookup e1 env'''
            return (Map.insert e tp2' env''', tvs'')
          -- types are not compatible --> error
          else fail ("ERROR: Can't apply \"" ++ show e1 ++ "\" to \"" ++ show e2 ++ "\". Incopatible types.")
      ULApp _ _ -> do
        -- infer type of e1
        (env'', tvs'') <- inferType e1 tvs' env'
        let Just tp = Map.lookup e1 env''
        -- unify types
        env''' <- unifyTypes (tp, Arrow tp' (TyVar tv)) env''
        let Just (Arrow tp'' tp''') = Map.lookup e1 env'''
        -- return the right hand side of unified arrow type
        return (Map.insert e tp''' env''', tvs'')

-- (T1, T2) are types to be unified
-- -> current envinrinment
-- -> new envinronment or an error messenge
unifyTypes :: (SimpleType, SimpleType) -> Environment -> Either String Environment
unifyTypes (AtomType, AtomType) env         = return env
unifyTypes (TyVar n, t) env                 = return $ Map.map (substituteTyVar n t) env
unifyTypes (t, TyVar n) env                 = return $ Map.map (substituteTyVar n t) env
unifyTypes (Arrow t1 t2, Arrow t1' t2') env = do
  env' <- unifyTypes (t1, t1') env
  unifyTypes (t2, t2') env'
unifyTypes (t1, t2) env = fail $ "ERROR: Can't unify type (" ++ show t1 ++ ") with (" ++ show t2 ++ ")."

-- returns True if the first type can be unified with the second one
areTypesCompatible :: SimpleType -> SimpleType -> Bool
areTypesCompatible AtomType       _              = True
areTypesCompatible TyVar{}        _              = True
areTypesCompatible (Arrow t1 t2) (Arrow t1' t2') = areTypesCompatible t1 t1' && areTypesCompatible t2 t2'
areTypesCompatible _             _               = False

-- types substitution
-- String (a type name that will be replaced by type)
-- -> Type (a type to be substituted insted of the type name variable)
-- -> Type (a type where to provide substitution)
-- -> Type (the result)
substituteTyVar :: String -> SimpleType -> SimpleType -> SimpleType
substituteTyVar _ _ AtomType = AtomType
substituteTyVar n t (TyVar n')
  | n' == n   = t
  | otherwise = TyVar n'
substituteTyVar n t (Arrow t1 t2) = Arrow (substituteTyVar n t t1) (substituteTyVar n t t2)

-- parsing
identifier  = do
  c  <- letter
  cs <- many (alphaNum <|> char '_')
  return (c:cs)
parseExpr = try parseApp <|> parseExpr'
parseExpr' = parseAbs <|> parseVar <|> between (char '(') (char ')') parseExpr
parseVar = do
  name <- identifier
  return $ ULVar name
parseApp = do
  t1 <- parseExpr'
  char '@'
  t2 <- parseExpr'
  return $ ULApp t1 t2
parseAbs = do
  char '\\'
  name <- identifier
  char '.'
  expr <- parseExpr
  return $ ULAbs name expr

-- generate names for types
generateNames :: [String]
generateNames = [a : if n == 0 then "" else show n | n <- [0..], a <- ['\945'..'\968']]

typeTerm :: Environment -> String -> ChL
typeTerm env0 = annotateTerm . typeTerm' where
  annotateTerm :: (UntypedLambda, Map.Map UntypedLambda ChType) -> ChL
  annotateTerm ((ULVar n), env) = case Map.lookup (ULVar n) env of
    Nothing -> error "error during typeing 1"
    Just _  -> (V n)
  annotateTerm ((ULAbs n e1), env) = case Map.lookup (ULVar n) env of
    Nothing -> error "error during typeing 2"
    Just tp -> LamChl [(n, tp)] (annotateTerm (e1, env))
  annotateTerm ((ULApp e1 e2), env) =
    (App (annotateTerm (e1, env)) (annotateTerm (e2, env)))
  typeTerm' :: String -> (UntypedLambda, Map.Map UntypedLambda ChType)
  typeTerm' s = case parse parseExpr "" (filter (not . isSpace) s) of
    Left  msg  -> error $ show msg
    Right term -> case inferType term generateNames env0 of
      Left msg       -> error msg
      Right (env, _) -> (term, Map.map (simpleTypeToChType) env)
simpleTypeToChType :: SimpleType -> ChType
simpleTypeToChType (AtomType   ) = O
simpleTypeToChType (TyVar _    ) = O
simpleTypeToChType (Arrow t1 t2) = P (simpleTypeToChType t1) (simpleTypeToChType t2)