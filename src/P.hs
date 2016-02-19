--------------------------------------------------------------------------------
-- Compiler for the STG Language                                              --
-- By Michael B. Gale (michael.gale@cl.cam.ac.uk)                             --
--------------------------------------------------------------------------------

module P where

--------------------------------------------------------------------------------

import Pretty
import Var
import Token
import Lexer
import AST
import Types

--------------------------------------------------------------------------------

newtype P a = MkP { runParser :: AlexState -> Either String a }

--------------------------------------------------------------------------------

instance Functor P where
    fmap f (MkP m) = MkP $ fmap f . m

instance Applicative P where
    pure x = MkP (\s -> Right x)

    (MkP f) <*> (MkP x) = MkP $ \s -> case f s of
        Left err -> Left err
        Right f' -> case x s of
            Left err -> Left err
            Right x' -> Right (f' x')

instance Monad P where
    (MkP m) >>= f = MkP $ \s -> case m s of
        Left err -> Left err
        Right r  -> let (MkP m') = f r in m' s

--------------------------------------------------------------------------------

mkParseState :: String -> AlexState
mkParseState xs = AlexState {
    alex_pos = AlexPn 0 1 1,
    alex_inp = xs,
    alex_chr = '\n',
    alex_bytes = [],
    alex_scd = 0
}

parseFile :: FilePath -> P a -> IO (Either String a)
parseFile fp p = do
    xs <- readFile fp
    return $ runParser p (mkParseState xs)

-- | `parseError tkn' raises a parser error as a result of encountering `tkn'.
parseError :: TokenP -> P a
parseError (tkn, pos) = MkP $ \s -> Left $ render $
    pp pos <+> text "Parse error: unexpected" <+> pp tkn

--------------------------------------------------------------------------------

toPosn :: AlexPosn -> Posn
toPosn (AlexPn a l c) = FilePosn l c

mkVar :: TokenP -> P Var
mkVar (TVar var, pos) = return $ Var var (toPosn pos)

mkTyBind :: AlexPosn -> TokenP -> [Var] -> [AlgCtr] -> P TyBind
mkTyBind pos (TCtr ctr, _) ps ctrs = return $ MkTyBind ctr ps ctrs (toPosn pos)

mkAlgCtr :: TokenP -> [Type] -> P AlgCtr
mkAlgCtr (TCtr ctr, pos) ps = return $ MkAlgCtr ctr ps (toPosn pos)

mkBind :: Var -> LambdaForm -> P Bind
mkBind v@(Var var pos) lf = return $ MkBind v lf pos

mkLambdaForm :: [Var] -> UpdateFlag -> [Var] -> Expr -> P LambdaForm
mkLambdaForm fvs uf vs expr = return $ MkLambdaForm fvs uf vs expr

mkLetE :: AlexPosn -> [Bind] -> Expr -> P Expr
mkLetE pos bs expr = return $ LetE bs expr (toPosn pos)

mkLetRecE :: AlexPosn -> [Bind] -> Expr -> P Expr
mkLetRecE pos bs expr = return $ LetRecE bs expr (toPosn pos)

mkCaseE :: AlexPosn -> Expr -> Alts -> P Expr
mkCaseE pos expr alts = return $ CaseE expr alts (toPosn pos)

mkAppE :: Var -> [Atom] -> P Expr
mkAppE v@(Var var pos) as = return $ AppE v as pos

mkCtrE :: TokenP -> [Atom] -> P Expr
mkCtrE (TCtr ctr, pos) as = return $ CtrE ctr as (toPosn pos)

mkOpE :: TokenP -> [Atom] -> P Expr
mkOpE (TPrimOp op, pos) as = return $ OpE op as (toPosn pos)

mkLitE :: TokenP -> P Expr
mkLitE (TPrimInt val, pos) = return $ LitE val (toPosn pos)

mkAlgAlt :: TokenP -> [Var] -> Expr -> P AlgAlt
mkAlgAlt (TCtr ctr, pos) vs expr = return $ AAlt ctr vs expr (toPosn pos)

mkPrimAlt :: TokenP -> Expr -> P PrimAlt
mkPrimAlt (TPrimInt val, pos) expr = return $ PAlt val expr (toPosn pos)

mkDefaultVar :: Var -> Expr -> P DefaultAlt
mkDefaultVar v@(Var var pos) expr = return $ DefaultVar v expr pos

mkDefault :: AlexPosn -> Expr -> P DefaultAlt
mkDefault pos expr = return $ Default expr (toPosn pos)

mkVarAtom :: Var -> P Atom
mkVarAtom v@(Var var pos) = return $ VarAtom v pos

mkInt :: TokenP -> P Atom
mkInt (TPrimInt val, pos) = return $ LitAtom val (toPosn pos)

-------------------------------------------------------------------------------
-- Getting lists of free values found in the AST

-- gets expression FVs
getExprFVs :: Expr -> [Var] -> [Var]
getExprFVs (LetE binds expr _)    bvs = 
    let bvs' =  (map bindName binds) `union` bvs in
        getBindFVs binds bvs `union` getExprFVs expr bvs'
getExprFVs (LetRecE binds expr _) bvs = 
    let bvs' =  (map bindName binds) `union` bvs in
        getBindFVs binds bvs' `union` getExprFVs expr bvs'
getExprFVs (CaseE expr alts _)    bvs = getAltFVs alts bvs `union` getExprFVs expr bvs
getExprFVs (AppE fun atoms _)     bvs = if elem fun bvs 
                                        then getAtomsFVs atoms bvs
                                        else fun : (getAtomsFVs atoms bvs)
getExprFVs (CtrE _ atoms _)       bvs = getAtomsFVs atoms bvs
getExprFVs (OpE _ atoms _)        bvs = getAtomsFVs atoms bvs
getExprFVs (LitE _ _)             bvs = []

-- Binds
getBindFVs :: [Bind] -> [Var] -> [Var]
getBindFVs ((MkBind v lf _) : bs) bvs = getLamFVs lf (v : bvs)

-- Lambdas
getLamFVs :: LambdaForm -> [Var] -> [Var]
getLamFVs (MkLambdaForm _ _ xs expr) bvs = getExprFVs expr (xs `union` bvs)

-- Gets FVs from atoms (compare to bound, add
getAtomsFVs :: [Atom] -> [Var] -> [Var]
getAtomsFVs ((VarAtom v _) : as) bvs = if elem v bvs 
                                       then getAtomsFVs as bvs
                                       else v : (getAtomsFVs as bvs)
getAtomsFVs ((LitAtom _ _) : as) bvs = getAtomsFVs as bvs
getAtomsFVs [] bvs = []


-- Alts
getAltFVs :: Alts -> [Var] -> [Var]
getAltFVs (AlgAlts alts dalt) bvs  = getAlgAltFVs alts bvs `union` 
                                     getDAltFVs dalt bvs
getAltFVs (PrimAlts alts dalt) bvs = getPrimAltFVs alts bvs `union` 
                                     getDAltFVs dalt bvs
-- Alg Alts
getAlgAltFVs :: [AlgAlt] -> [Var] -> [Var]
getAlgAltFVs (AAlt _ vs expr _ : alts) bvs = getExprFVs expr (bvs`union` vs) 
    `union` getAlgAltFVs alts bvs
getAlgAltFVs [] bvs = []

-- Prim Alts
getPrimAltFVs :: [PrimAlt] -> [Var] -> [Var]
getPrimAltFVs ((PAlt _ expr _) : alts) bvs = getExprFVs expr bvs `union` 
    getPrimAltFVs alts bvs
getPrimAltFVs [] bvs = []

-- Default Alts
getDAltFVs :: DefaultAlt -> [Var] -> [Var]
getDAltFVs (Default expr _) bvs = getExprFVs expr bvs
getDAltFVs (DefaultVar v expr _) bvs = getExprFVs expr (v : bvs)


------------------------------------------------------------------------------
-- Free value checks

-- Check the whole program for correct free values
checkProgFVs :: Prog -> Bool
checkProgFVs (MkProg binds) = foldl (&&) True (map (\b -> checkBindFVs b gs) binds)
    where gs = map bindName binds

-- Check bindings
checkBindFVs :: Bind -> [Var] -> Bool
checkBindFVs (MkBind v lf _) bvs = if trace (show v ++ show bvs) True then checkLamFVs lf bvs else False

-- Check lambda free variables by calculating the free variables from the
-- AST and comparing against those specified in the lambda form.
checkLamFVs :: LambdaForm -> [Var] -> Bool
checkLamFVs (MkLambdaForm vs _ xs expr) bvs  = 
        trace (show vs ++ show (getExprFVs expr (bvs `union` xs))) True &&
        S.fromList (getExprFVs expr (bvs `union` xs)) == S.fromList vs &&
        checkExprFVs expr bvs

-- Check expressions to recursively look for more bound lambdas
checkExprFVs :: Expr -> [Var] -> Bool
checkExprFVs (LetE binds expr _) bvs = checkExprFVs expr bvs && 
    foldl (&&) True (map (\b -> checkBindFVs b bvs) binds)
checkExprFVs (LetRecE binds expr _) bvs = checkExprFVs expr bvs && 
    foldl (&&) True (map (\b -> checkBindFVs b (bvs ++ (map bindName binds))) binds)
checkExprFVs (CaseE _ _ _) _ = True
checkExprFVs (AppE _ _ _) _ = True
checkExprFVs (CtrE _ _ _) _ = True
checkExprFVs (OpE _ _ _) _ = True
checkExprFVs (LitE _ _) _ = True
