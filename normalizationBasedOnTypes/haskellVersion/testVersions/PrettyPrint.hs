instance Show Type where
    showsPrec _ x = shows (prType x)
prType             ::  Type -> PP.Doc
prType (TVar n)    =   PP.text n
prType TInt        =   PP.text "Int"
prType TBool       =   PP.text "Bool"
prType (TFun t s)  =   prParenType t PP.<+> PP.text "->" PP.<+> prType s
prParenType     ::  Type -> PP.Doc
prParenType  t  =   case t of
                      TFun _ _  -> PP.parens (prType t)
                      _         -> prType t
instance Show Exp where
    showsPrec _ x = shows (prExp x)
prExp                  ::  Exp -> PP.Doc
prExp (EVar name)      =   PP.text name
prExp (ELit lit)       =   prLit lit
prExp (ELet x b body)  =   PP.text "let" PP.<+> 
                           PP.text x PP.<+> PP.text "=" PP.<+>
                           prExp b PP.<+> PP.text "in" PP.$$
                           PP.nest 2 (prExp body)
prExp (EApp e1 e2)     =   prExp e1 PP.<+> prParenExp e2
prExp (EAbs n e)       =   PP.char '\\' PP.<> PP.text n PP.<+>
                           PP.text "->" PP.<+>
                           prExp e
                                                                   
prParenExp    ::  Exp -> PP.Doc
prParenExp t  =   case t of
                    ELet _ _ _  -> PP.parens (prExp t)
                    EApp _ _    -> PP.parens (prExp t)
                    EAbs _ _    -> PP.parens (prExp t)
                    _           -> prExp t
instance Show Lit where
    showsPrec _ x = shows (prLit x)
prLit            ::  Lit -> PP.Doc
prLit (LInt i)   =   PP.integer i
prLit (LBool b)  =   if b then PP.text "True" else PP.text "False"
instance Show Scheme where
    showsPrec _ x = shows (prScheme x)
prScheme                  ::  Scheme -> PP.Doc
prScheme (Scheme vars t)  =   PP.text "All" PP.<+>
                              PP.hcat 
                                (PP.punctuate PP.comma (map PP.text vars))
                              PP.<> PP.text "." PP.<+> prType t

test' :: Exp -> IO ()
test' e =
    do (res, _) <- runTI (bu Set.empty e)
       case res of
         Left err -> putStrLn $ "error: " ++ err
         Right t  -> putStrLn $ show e ++ " :: " ++ show t
data Constraint = CEquivalent Type Type
                | CExplicitInstance Type Scheme
                | CImplicitInstance Type (Set.Set String) Type
instance Show Constraint where
    showsPrec _ x = shows (prConstraint x)
prConstraint :: Constraint -> PP.Doc
prConstraint (CEquivalent t1 t2) = PP.hsep [prType t1, PP.text "=", prType t2]
prConstraint (CExplicitInstance t s) =
    PP.hsep [prType t, PP.text "<~", prScheme s]
prConstraint (CImplicitInstance t1 m t2) =
    PP.hsep [prType t1, 
             PP.text "<=" PP.<> 
               PP.parens (PP.hcat (PP.punctuate PP.comma (map PP.text (Set.toList m)))), 
             prType t2]
type Assum = [(String, Type)]
type CSet = [Constraint]
bu :: Set.Set String -> Exp -> TI (Assum, CSet, Type)
bu m (EVar n) = do b <- newTyVar "b"
                   return ([(n, b)], [], b)
bu m (ELit (LInt _)) = do b <- newTyVar "b"
                          return ([], [CEquivalent b TInt], b)
bu m (ELit (LBool _)) = do b <- newTyVar "b"
                           return ([], [CEquivalent b TBool], b)
bu m (EApp e1 e2) =
    do (a1, c1, t1) <- bu m e1
       (a2, c2, t2) <- bu m e2
       b <- newTyVar "b"
       return (a1 ++ a2, c1 ++ c2 ++ [CEquivalent t1 (TFun t2 b)],
               b)
bu m (EAbs x body) =
    do b@(TVar vn) <- newTyVar "b"
       (a, c, t) <- bu (vn `Set.insert` m) body
       return (a `removeAssum` x, c ++ [CEquivalent t' b | (x', t') <- a,
                                        x == x'], TFun b t)
bu m (ELet x e1 e2) =
    do (a1, c1, t1) <- bu m e1
       (a2, c2, t2) <- bu (x `Set.delete` m) e2
       return (a1 ++ removeAssum a2 x,
               c1 ++ c2 ++ [CImplicitInstance t' m t1 |
                            (x', t') <- a2, x' == x], t2)
removeAssum [] _ = []
removeAssum ((n', _) : as) n | n == n' = removeAssum as n
removeAssum (a:as) n = a : removeAssum as n