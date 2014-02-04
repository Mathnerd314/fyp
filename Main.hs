{-# LANGUAGE Arrows, DoRec, EmptyDataDecls, FlexibleInstances, FunctionalDependencies, GeneralizedNewtypeDeriving, MultiParamTypeClasses, NoMonomorphismRestriction, TypeFamilies, TypeSynonymInstances #-}
-- module Compiler where

import Control.Arrow
import Control.Arrow ((&&&))
import Control.Arrow ((&&&),(***))
import Control.Arrow ((***),second)
import Control.Monad
import Control.Monad.Cont
import Control.Monad.Error
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.RWS.Lazy
import Control.Monad.ST
import Control.Monad.State
import Control.Monad.State.Lazy
import Control.Monad.Trans
import Control.Monad.Writer
import Data.Array
import Data.Bits
import Data.Char
import Data.Either
import Data.Function
import Data.Int
import Data.IORef
import Data.List
import Data.Map ((!))
import Data.Maybe
import Data.Monoid
import Data.Ord
import Data.STRef
import Data.Unique
import Data.Word
import Debug.Trace
import Distribution.Simple
import Foreign.StablePtr -- oh god
import qualified Control.Monad.State.Lazy as STM
import qualified Data.IntMap as IM
import qualified Data.IntMap as M
import qualified Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import System.Mem.Weak
import Text.PrettyPrint

type CompilerM = STM.StateT [Value] (ListT Scoping)

instance LLVMWriter CompilerM where
    writelist xs = lift $ lift $ writelist xs




codegenM :: Scoping [([Value], b)] -> CompilerM b
codegenM c = do
  st <- get
  write $ LLVMLabel st
  out <- lift $ lift $  c
  (s, x) <- lift (liftList out)
  put s
  return x

stmtgen c = codegenM $ do
  val <- c
  l <- lift $ freshLabel
  write $ LLVMBranch l
  return [([l],val)]

dethread :: CompilerM a -> Scoping a
-- FIXME coalesceM
dethread c = do
  beforelbl <- lift $ freshLabel
  write $ LLVMBranch beforelbl
  [(ret, afterlbl)] <- runAllListT (STM.runStateT (c) [beforelbl])
  write $ LLVMLabel afterlbl
  return ret

dethreadFunc :: (Value -> CompilerM Value) -> (Value -> Scoping Value)
dethreadFunc f = \arg -> dethread $ 
  do retV <- varNewM 
     coalesceM $ do
       ret <- f arg
       varSetM retV ret
     varGetM retV

instance LanguageMonad CompilerM () Value Value where
    condM b = codegenM $ do
             tpart <- lift $ freshLabel
             fpart <- lift $ freshLabel
             write $ LLVMInsn OpBranch Nothing [b,tpart,fpart]
             return [([tpart], True), ([fpart], False)]

{-
    primBinOpM op e1 e2 = stmtgen $ lift $ expgen objectT' (getop op) [e1,e2]
        where
          getop OpPlus = OpAdd
          getop OpEq = OpCmpEq
          getop OpNeq = OpCmpNe
-}
    primBinOpM OpPlus e1 e2 = stmtgen $ lift $ expgen objectT' OpCall [rtIntAdd, e1, e2]

--    litIntM i = return (Value (TBaseType "i32") (show i))
    litIntM i = stmtgen $ lift $ expgen objectT' OpCall [rtIntNew, (Value (TBaseType "i32") (show i))]

    voidValue = return (Value objectT' "null")

    varNewM = stmtgen $ varNew
    varGetM v = stmtgen $ varGet v
    varSetM v val = stmtgen $ varSet v val

    letrec fns = stmtgen $ corecLambda 
                 (\x -> dethread $ liftM (map dethreadFunc) $ fns x)

    structNewM fs = stmtgen $ lift $ structNew fs
    structGetM s f = stmtgen $ lift $ structGet s f
    structSetM s f x = stmtgen $ lift $ structSet s f x

    lambdaM fn = stmtgen $ lambda (dethreadFunc fn)
    applyM f v = stmtgen $ apply f v

    typeNew = return ()
    typeConstrain _ = return ()

runCompiler x = generateCode (dethread x)

{-

data Type = TyUnknown | TyInt | TyBool | TyInvalid deriving (Eq,Show)
instance Monoid Type where
    TyUnknown `mappend` x = x
    x `mappend` TyUnknown = x
    TyInt `mappend` TyInt = TyInt
    TyBool `mappend` TyBool = TyBool
    _ `mappend` _ = TyInvalid

    mempty = TyUnknown

newtype CombiningMap k a = CombiningMap {getMap :: M.Map k a} deriving Show
instance (Ord k, Monoid a) => Monoid (CombiningMap k a) where
    x `mappend` y = CombiningMap $ (M.unionWith mappend `on` getMap) x y
    mempty = CombiningMap $ M.empty

type TypeChecker = StateArrow (CombiningMap Var Type) (MultiArrow (Kleisli (RWS () [String] ())))

checkType :: Eq a => a -> TypeChecker a ()
checkType t' = ArrTrans.lift $ liftC $ Kleisli $ \t -> 
               tell $ if t == t' then [] else ["type error"]

instance ArrowInterpreter TypeChecker Type where
    cond = checkType TyBool >>> proc _ -> ArrTrans.lift distribute -< [True,False]
    primBinOp op = checkType (fst $ types op) >>> arr (const $ snd $ types op)
        where
          types OpPlus = ((TyInt, TyInt), TyInt)
          types OpEq = ((TyInt, TyInt), TyBool)
          types OpNeq = ((TyInt, TyInt), TyBool)
    litInt _ = arr (const TyInt)

    varGet v = fetch >>> arr (\s -> fromJust $ M.lookup v (getMap s))
    varSet v = proc e -> do
                 s <- fetch -< () 
                 store -< CombiningMap $ M.insert v e (getMap s)

runTypeChecker :: TypeChecker () () -> ([((), CombiningMap Var Type)], (), [String])
runTypeChecker p = runRWS (runKleisli (runCoalesced (runState p)) [((), mempty)]) () ()

-}{-# LANGUAGE NoMonomorphismRestriction #-}
-- module Driver where

compile p = putStrLn $ runCompiler $ (lambdaM (const $ (runEval' (SymbolTable M.empty M.empty M.empty) $ parseProgram (runLexer p)) >> voidValue)) >> return ()

interpret p = runInterpreter ((runEval' (SymbolTable M.empty (M.fromList [(Def "print",Wrap printFunc)]) M.empty) $ parseProgram $ runLexer p) >> voidValue)

infertype p = do
  Ungen (UngenVar _ t) <- (flip runReaderT undefined $ runConstraintGen $ liftM unWrap $ runEval' (SymbolTable M.empty M.empty M.empty) $ parseExp (runLexer p))
  showTypeGraph t
  putStrLn ""
  TypeScheme [] t <- optimiseTypeScheme $ TypeScheme [] t
  showTypeGraph t
  putStrLn ""
  ut <- toUserType t
  print ut

inferprog p = do
  genID <- newUnique
  (flip runReaderT (GeneralisationLevel{generalisationID=GeneralisationID genID, importedVars=error "can't import var"}) $ runConstraintGen $ (runEval' (SymbolTable M.empty M.empty M.empty) $ parseProgram (runLexer p)) >> voidValue)

{-
testCoRec = letrec $ \fns -> do
              let f = fns !! 0
                  g = fns !! 1
              f' <- lambdaM $ \arg -> do
                      b <- condM arg
                      if b then applyM g arg else arg
              g' <- lambdaM $ \arg -> do
                      b <- condM arg
                      if b then arg else applyM g arg
              undefined-}{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, GeneralizedNewtypeDeriving, FlexibleInstances #-}
-- module Interpreter where

data Val = ValBool Bool | ValInt Int | ValVoid | ValFunc (Val -> Interpreter Val) | ValStruct (M.Map FieldName Var)
type Var = IORef Val
    

newtype Interpreter a = Interpreter (IO a) deriving (Monad,MonadFix)
instance MonadCoalesce Interpreter where
    coalesceLeft = id
instance MonadIterate Interpreter where
    fixiterM f x = do
      y <- f x
      case y of
        Left l -> return l
        Right r -> fixiterM f r

instance LanguageMonad Interpreter () Var Val where

    condM (ValBool b) = return b

    litIntM i = return (ValInt i)
    litBool b = return (ValBool b)
    primBinOpM OpPlus (ValInt i1) (ValInt i2) =return$ ValInt $ i1 + i2
    primBinOpM OpEq (ValInt i1) (ValInt i2) =return$ ValBool $ i1 == i2
    primBinOpM OpNeq (ValInt i1) (ValInt i2) =return$ ValBool $ i1 /= i2

    varSetM v e = Interpreter $ writeIORef v e
    varNewM = Interpreter $ newIORef (error "uninitialised variable")
    varGetM v = Interpreter $ readIORef v

    voidValue = return ValVoid

    lambdaM f = return $ ValFunc f
    applyM (ValFunc f) v = f v
    
    letrec fns = mfix (fns >=> mapM lambdaM)

    structNewM fs = do
      vars <- mapM (const varNewM) fs
      return $ ValStruct $ M.fromList $ zip fs vars
    structSetM (ValStruct s) f e = Interpreter $ writeIORef (s ! f) e
    structGetM (ValStruct s) f = Interpreter $ readIORef (s ! f)

    typeConstrain _ = return ()
    typeNew = return ()

showVal (ValBool b) = return $ show b
showVal (ValInt i) = return $ show i
showVal (ValFunc f) = return $ "<function>"
showVal (ValVoid) = return $ "<void>"
showVal (ValStruct s) = do
  let (ks,vs') = unzip $ M.toList s
  vs <- mapM (showVal <=< readIORef) vs'
  return $ "{" ++ intercalate ", " [k ++ " = " ++ v |
                                    (k,v) <- zip ks vs] ++ "}"

runInterpreter (Interpreter x) = showVal =<< x
printFunc = ValFunc $ \v -> Interpreter $ do
  putStrLn =<< showVal v
  return $ ValVoid

-- module LLVMGen where

type LLVMCode = [LLVMInsn] 

data Type = TBaseType String | TPtr Type | TStruct [Type] | TArray Int Type | TFunc Type [Type] deriving (Show,Eq,Ord)

voidT = TBaseType "void"
labelT = TBaseType "label"

[litInt32,litInt16,litInt8] = [\i -> Value (TBaseType $ "i" ++ show (t::Int)) (show (i::Int)) | t <- [32,16,8]]

mkConstStruct :: [Value] -> Value
mkConstStruct vs = Value (TStruct $ map vType vs) ("{" ++ commaSep vParam vs ++ "}")
mkConstArr :: [Value] -> Value
mkConstArr vs | length (group $ map vType vs) == 1 =
  Value (TArray (length vs) (vType $ head vs)) ("[" ++ commaSep vParam vs ++ "]")

mkConstPtrCast :: Type -> Value -> Value
mkConstPtrCast t@(TPtr _) v@(Value (TPtr _) _) = 
  Value t ("bitcast(" +-+ vParam v +-+ "to" +-+ showType t++")")
data Value = Value Type String deriving (Show,Eq,Ord)

showType (TBaseType t) = t
showType (TPtr t) = showType t ++ "*"
showType (TStruct ts) = "{" ++ commaSep showType ts ++ "}"
showType (TArray i t) = "[" ++ show i ++ " x " ++ showType t ++ "]"
showType (TFunc ret args) = showType ret +-+ "(" ++ commaSep showType args ++ ")"

vType (Value t s) = t
vReg (Value t s) = s
vParam (Value t s) = showType t +-+ if t == labelT then "%"++s else s

data OpCode = OpCall | OpAdd | OpCmpEq | OpCmpNe | OpLoad | OpStore | OpBranch | OpRet | OpGEP | OpPtrCast  deriving (Eq,Enum,Show)
opName op = case op of
              OpCall -> "call"
              OpAdd -> "add"
              OpCmpEq -> "icmp eq"
              OpCmpNe -> "icmp ne"
              OpLoad -> "load"
              OpStore -> "store"
              OpBranch -> "br"
              OpRet -> "ret"
              OpGEP -> "getelementptr inbounds"
              OpPtrCast -> "bitcast"

data LLVMInsn = LLVMLabel [Value] | LLVMBranch Value | LLVMInsn OpCode (Maybe Value) [Value] deriving Show

writeLLVMLabels :: [Value] -> String
writeLLVMLabels (l:rest) = concat [vReg from ++ ":\n" ++ "br" +-+ vParam to ++ ";\n"
                                   | (to, from) <- reverse $ zip (l:rest) rest]
                           ++
                           vReg l ++ ":\n"

writeLLVM :: [LLVMInsn] -> String
writeLLVM [] = ""
writeLLVM (LLVMBranch l':LLVMLabel ls:rest) 
    | l' `elem` ls = case (ls \\ [l']) of
                       [] -> writeLLVM rest
                       ls' -> writeLLVM [LLVMBranch (head ls')]
                              ++ 
                              writeLLVMLabels ls'
                              ++
                              writeLLVM rest

writeLLVM (x:rest) = s ++ writeLLVM rest
                     where
                       s = case x of
                             LLVMLabel l -> writeLLVMLabels l
                             LLVMBranch l -> "br" +-+ vParam l ++ ";\n"
                             LLVMInsn _ _ _ -> writeInsn x ++ ";\n"

commaSep f x = intercalate ", " $ map f x

a +-+ b = a ++ " " ++ b

writeInsn (LLVMInsn op res args) = 
    let (prefix,resT) = case res of
                          Just (Value resT resV) -> (resV ++ " = ", resT)
                          Nothing -> ("", TBaseType "void")
    in prefix ++ 
      case op of 
        OpCall -> 
            let (target:params) = args
            in "call" +-+ showType resT +-+ vReg target ++
                   "(" ++ commaSep vParam params ++ ")"
        OpPtrCast ->
            let [source] = args
            in "bitcast" +-+ vParam source +-+ "to" +-+ showType resT

        _ | op `elem` [OpBranch,OpStore,OpGEP] ->
            opName op +-+ commaSep vParam args

        _ ->
            opName op +-+ 
            showType (if null args then voidT else vType $ head args) +-+
            commaSep vReg args

writeFunc name rettype params code = "define" +-+ showType rettype +-+ vReg name ++ "(" ++ commaSep vParam params ++ "){\n" ++ writeLLVM code ++ "}\n"

-- module Language where

traceM s = trace ("trace: " ++ s) $ return ()

data ControlFlowJump (m :: * -> *) t v e= LoopBreak | LoopContinue | FuncReturn e 
instance Error (ControlFlowJump m t v e) where
    noMsg = undefined
    strMsg = undefined

type FieldName = String

data BinOp = OpPlus | OpEq | OpNeq deriving Show

class MonadIterate m => LanguageMonad m t v e | m -> t v e where
    condM :: e -> m Bool
    primBinOpM :: BinOp -> e -> e -> m e

    litIntM :: Int -> m e
    litBool :: Bool -> m e
    voidValue :: m e

    varNewM :: m v
    varSetM :: v -> e -> m ()
    varGetM :: v -> m e

    letrec :: ([e] -> m [e -> m e]) -> m [e]

    lambdaM :: (e -> m e) -> m e
    applyM :: e -> e -> m e

    structNewM :: [FieldName] -> m e
    structSetM :: e -> FieldName -> e -> m ()
    structGetM :: e -> FieldName -> m e

    typeNew :: m t 
    typeConstrain :: Constraint t -> m ()

newtype Var = Var String deriving (Ord,Eq)
instance Show Var where
    show (Var v) = "$" ++ v
newtype TyVar = TyVar String deriving (Ord,Eq,Show)
newtype Def = Def String deriving (Ord,Eq,Show)

data SymbolTable (m :: * -> *) t v e = SymbolTable {symVar :: M.Map Var v,
                                        symVal :: M.Map Def e,
                                        symType :: M.Map TyVar t}

-- SymbolTable must be a Monoid for Eval to be a LanguageMonoid
-- We "combine" multiple symbol tables by choosing the first
-- This reflects the fact that the variables in scope at a
-- point do not depend on the path taken to reach that point.
instance Monoid (SymbolTable m t v e) where
    mempty = error "mempty not defined for symbol tables"
    s1 `mappend` _ = s1

newtype EvalT t v e m a = Eval (ErrorT (ControlFlowJump m t v e) (StateT (SymbolTable m t v e) m) a) deriving (Monad,MonadIterate,MonadCoalesce)

type Eval t v e m = EvalT (Wrap t) (Wrap v) (Wrap e) m

instance MonadTrans (EvalT t v e) where
    lift = Eval . lift . lift
instance Monad m => MonadError (ControlFlowJump m t v e) (EvalT t v e m) where
    throwError e = Eval $ throwError e
    catchError (Eval x) handler = Eval $ x `catchError` ((\(Eval x) -> x) . handler)

newtype Wrap a = Wrap {unWrap :: a}

instance (LanguageMonad m t v e) => LanguageMonad 
    (EvalT (Wrap t) (Wrap v) (Wrap e) m) 
    (Wrap t) (Wrap v) (Wrap e) 
        where

    condM (Wrap e) = lift $ condM e

    primBinOpM op (Wrap a) (Wrap b) = liftM Wrap $ lift $ primBinOpM op a b

    litIntM i = liftM Wrap $ lift $ litIntM i
    litBool b = liftM Wrap $ lift $ litBool b
    voidValue = liftM Wrap $ lift $ voidValue
    varNewM = liftM Wrap $ lift $ varNewM
    varSetM (Wrap v) (Wrap x) = lift $ varSetM v x
    varGetM (Wrap v) = liftM Wrap $ lift $ varGetM v

    letrec = undefined
      

    lambdaM f = do
      symt <- getSymbolTable
      liftM Wrap $ lift $ lambdaM (\x -> runEval' symt $ liftM unWrap $ f $ Wrap $ x)

    applyM (Wrap f) (Wrap x) = liftM Wrap $ lift $ applyM f x

    structNewM fs = liftM Wrap $ lift $ structNewM fs
    structSetM (Wrap s) f (Wrap x) = lift $ structSetM s f x
    structGetM (Wrap s) f = liftM Wrap $ lift $ structGetM s f

    typeNew = liftM Wrap $ lift $ typeNew
    typeConstrain cn = lift $ typeConstrain $ fmap unWrap cn

getSymbolTable = Eval $ lift get

--runEval :: LanguageMonad m t v e => SymbolTable m t v e -> Eval (Wrap t) (Wrap v) (Wrap e) m a -> m (Either (ControlFlowJump m (Wra) a)
runEval symt (Eval x)= do
  (a,s) <- runStateT (runErrorT x) symt
  return a

--runEval' :: LanguageMonad m => SymbolTable m -> Eval m a -> m a
runEval' symt x = do
  r <- runEval symt x
  case r of
    Left e -> error "misplaced control flow"
    Right f -> return f

--runEvalWithSyms :: LanguageMonad m => SymbolTable m -> Eval m a -> m (a, SymbolTable m)
runEvalWithSyms symt (Eval x) = do
  (a,s) <- runStateT (runErrorT x) symt
  case a of
    Left e -> error "misplaced control flow"
    Right f -> return (f,s)

--evalUntilRet :: LanguageMonad m => Eval m () -> Eval m (LVal m)
evalUntilRet (Eval f) = Eval $ lift $ do
  a <- runErrorT f
  case a of
    Left (FuncReturn f) -> return f
    Left _ -> error "misplaced break/continue"
    Right a -> liftM Wrap $ lift voidValue

--noJumps :: LanguageMonad m => Eval m a -> Eval m a
noJumps x = x `catchError` (error "misplaced control flow")

--doWhile :: LanguageMonad m => Eval m (LVal m) -> Eval m () -> Eval m ()
doWhile exp blk = do
  symt <- getSymbolTable
  lift $ loop $ do
    l <- runEval symt $ do
      e <- noJumps exp
      c <- condM e
      case c of
        True -> liftM Right $ blk
        False -> return $ Left ()
    return $ case l of
      Left (LoopBreak) -> Left ()     -- "break"
      Left (LoopContinue) -> Right () -- "continue"
-- FIXME return inside a while
      Right (Left _) -> Left ()       -- loop exited normally
      Right (Right _) -> Right ()     -- loop is looping

doIf :: LanguageMonad m t v e => Eval t v e m (Wrap e) -> Eval t v e m () -> Eval t v e m () -> Eval t v e m ()
doIf exp t f = do
  e <- noJumps exp
  b <- condM e
  if b then t else f

--subscope :: LanguageMonad m => Eval m a -> Eval m a
subscope (Eval f) = Eval $ do
  oldtable <- lift get
  ans <- f
  lift $ put oldtable
  return ans

symVarInsert v v' (SymbolTable vs ds ts) = 
  SymbolTable (M.insert v v' vs) ds ts
symVarLookup v (SymbolTable vs ds ts) =
  M.lookup v vs

symDefInsert d d' (SymbolTable vs ds ts) = 
  SymbolTable vs (M.insert d d' ds) ts
symDefLookup d (SymbolTable vs ds ts) =
  M.lookup d ds

symTyInsert t t' (SymbolTable vs ds ts) = 
  SymbolTable vs ds (M.insert t t' ts)
symTyLookup t (SymbolTable vs ds ts) =
  M.lookup t ts

scopeNew' create symadd var = do
  v <- create
  Eval $ lift $ modify (symadd var v)
  return v

scopeGet' symlookup var = Eval $ do
  lift $ gets (maybe (error $ "not in scope: " ++ show var) id . symlookup var)

scopeVarNew = scopeNew' varNewM symVarInsert
scopeTyNew = scopeNew' typeNew symTyInsert
scopeDefNew d d' = Eval $ lift $ modify $ symDefInsert d d'
scopeVar = scopeGet' symVarLookup
scopeType = scopeGet' symTyLookup
scopeDef = scopeGet' symDefLookup

scopeLookup :: 
    LanguageMonad m t v e =>
    String ->
    Eval t v e m (Wrap e)
scopeLookup name = do
  symt <- getSymbolTable
  let v = symVarLookup (Var name) symt
  let d = symDefLookup (Def name) symt
  if (isJust d) then return (fromJust d) else varGetM (fromJust v)

  

data TermDecl m t v e = TermDecl String (m ()) (Maybe (m e))
data BasicBlockDecl m t v e = DeclVar (TermDecl m t v e)
                            | DeclDef (TermDecl m t v e)
                            | NoDecl (m ())
                            | DeclDefFun Def (e -> m e)

-- zip' is lazy in its second argument
-- which must be of exactly the same length as the first
zip' (x:xs) = \ ~(y:ys) -> (x,y):(zip' xs ys)
zip' [] = \ ~[] -> []

corecFuncs :: 
    LanguageMonad m t v e =>
    [(Def, Wrap e -> Eval t v e m (Wrap e))] ->
    Eval t v e m ()
corecFuncs fndefs = do
  symt <- getSymbolTable
  let names = map fst fndefs
      bodies = map snd fndefs
  fns <- liftM (map Wrap) $ lift $ 
         letrec $ \fns -> runEval' symt $ do
           forM_ (zip' names fns) $ \(name,f) -> do
             scopeDefNew name (Wrap f)
           symt' <- getSymbolTable
           return [\x -> liftM unWrap $ runEval' symt' (body (Wrap x)) |
                   body <- bodies]
  forM_ (zip names fns) $ \(name,f) -> do
    scopeDefNew name f

evalBasicBlockDecls ::
    LanguageMonad m t v e =>
    [BasicBlockDecl (Eval t v e m) (Wrap t) (Wrap v) (Wrap e)] ->
    Eval t v e m ()

evalBasicBlockDecls bs = do
  let chunks = groupBy ((==) `on` isCorec) bs
  forM_ chunks $ \chunk -> do
    if all isCorec chunk
      then corecFuncs [(name,func) |
                       DeclDefFun name func <- chunk]
      else forM_ chunk rundecl
    where
      isCorec (DeclVar _) = False
      isCorec (DeclDef _) = False
      isCorec (NoDecl _) = False
      isCorec (DeclDefFun _ _) = True

      rundecl (DeclVar (TermDecl name ty val)) = do
        v <- scopeVarNew (Var name)
        when (isJust val) $ do
          val' <- fromJust val
          varSetM v val'

      rundecl (DeclDef (TermDecl name ty val)) = do
        val' <- fromJust $ val
        scopeDefNew (Def name) val'
      rundecl (NoDecl action) = action

data Stmt a b = ControlFlow a | BasicStmt [b]

isBasicStmt (ControlFlow _) = False
isBasicStmt (BasicStmt _) = True

evalStmts stmts = 
    let blocks = groupBy ((==) `on` isBasicStmt) stmts
    in forM_ blocks $ \block -> do
      if all isBasicStmt block
        then evalBasicBlockDecls $ concat [ss | (BasicStmt ss) <- block]
        else sequence_ [s | (ControlFlow s) <- block]
      
{-
evalClassDecl superclasses decls = do
  let methods = 
-}

--testCoRec :: LanguageMonad m => m [LVal m]
testCoRec = letrec $ \fns -> do
              let f = fns !! 0
                  g = fns !! 1
              let f' = \arg -> do
                         applyM g arg 
              let g' = \arg ->  do
                         applyM f arg
              return [f', g']
-- module Lattice where

data Variance = Pos -- Covariant, or a lower bound type
              | Neg -- Contravariant, or an upper bound type
                deriving (Eq, Ord, Enum)

flipByVariance Pos = id
flipByVariance Neg = \(a,b) -> (b,a)

opVariance = (`mappend`Neg)

instance Monoid Variance where
    mempty = Pos
    Pos `mappend` Pos = Pos
    Pos `mappend` Neg = Neg
    Neg `mappend` Pos = Neg
    Neg `mappend` Neg = Pos

instance Show Variance where
    show Pos = "+"
    show Neg = "-"

-- A lattice whose elements are of type t
class Eq t => Lattice t where
    -- The GLB and LUB functions
    -- merge Pos a b = LUB(a,b)
    -- merge Neg a b = GLB(a,b)
    merge :: Variance -> t -> t -> t

    -- The partial order (defined in terms of merge)
    (<:=) :: t -> t -> Bool
    -- could equally be defined as merge Pos a b == b
    a <:= b = merge Neg a b == a
    
    -- cmp Pos is <=, cmp Neg is >=
    cmp :: Variance -> t -> t -> Bool
    cmp Pos a b = a <:= b
    cmp Neg a b = b <:= a

    -- extremum Pos == TOP
    -- extremum Neg == BOT
    extremum :: Variance -> t

mergeIdentity v = extremum (v `mappend` Neg)
mergeZero v = extremum v
mergeFailure v = mergeZero v

-- The powerset of a finite set forms a lattice
-- Since we don't know what exactly the finite set is,
-- we can't provide a sane implementation for "top"
instance Ord t => Lattice (S.Set t) where
    merge Pos a b = a `S.union` b
    merge Neg a b = a `S.intersection` b
    extremum Neg = S.empty
    extremum Pos = error "Top element of set lattice is not known"

data PosT
data NegT

class VarianceT t where
    variance :: t -> Variance
instance VarianceT PosT where variance = const Pos
instance VarianceT NegT where variance = const Neg
class (VarianceT v1, VarianceT v2) => OpVariance v1 v2 | v1 -> v2, v2 -> v1 where
instance OpVariance PosT NegT
instance OpVariance NegT PosT

-- module ListT where

 

-- The version in Data.Either is not lazy enough
-- at least in oldish GHC versions
partitionEithers :: [Either a b] -> ([a],[b])
partitionEithers = foldr (either left right) ([],[])
 where
  left  a ~(l, r) = (a:l, r)
  right a ~(l, r) = (l, a:r)

 
newtype ListT m a = ListT { runListT :: m (Maybe (a, ListT m a)) }
 
foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT c n (ListT m) = maybe n (\(x,l) -> c x (foldListT c n l)) =<< m
 
-- In ListT from Control.Monad this one is the data constructor ListT, so sadly, this code can't be a drop-in replacement.
liftList :: Monad m => [a] -> ListT m a
liftList [] = ListT $ return Nothing
liftList (x:xs) = ListT . return $ Just (x, liftList xs)

{-

doList :: Monad m => [Either (m a) (m ())] -> ListT m a
doList [] = mzero
doList ((Left act):rest) = ListT $ do
  x <- act
  return $ Just (x, doList rest)
doList ((Right act):rest) = lift act >> doList rest

newtype YieldT w m a = YieldT { runYieldT :: }

produce :: Monad m => YieldT w m a -> ListT m w
yield :: Monad m => w -> YieldT w m ()

-}

instance Functor m => Functor (ListT m) where
  fmap f (ListT m) = ListT $ fmap (fmap $ f *** fmap f) m where
 
instance (Monad m) => Monad (ListT m) where
  return x = ListT . return $ Just (x, mzero)
  m >>= f = ListT $ 
    foldListT (\x l -> runListT $ f x `mplus` ListT l) (return Nothing) m
 
instance MonadTrans ListT where
  lift = ListT . liftM (\x -> Just (x, mzero))
 
instance Monad m => MonadPlus (ListT m) where
  mzero = ListT $ return Nothing
  ListT m1 `mplus` ListT m2 = ListT $ 
    maybe m2 (return . Just . second (`mplus` ListT m2)) =<< m1

runAllListT :: Monad m => ListT m a -> m [a]
runAllListT = foldListT (\x y -> do {y' <- y; return (x:y')}) (return [])

instance Monad m => MonadCoalesce (ListT m) where
    coalesceLeft f = do
      ans <- lift (runAllListT f)
      let (l,r) = partitionEithers ans
      return (Left (mconcat l)) `mplus` (liftList $ map Right r)

instance (MonadFix m) => MonadIterate (ListT m) where
    fixiterM f = \init -> do
      ~(output,_) <- lift $ mfix $ \ ~(output, input) -> do
                (final, cont) <- liftM partitionEithers $ runAllListT $ f input
                return (final, mconcat (init:cont))
      liftList output

--loop' f = re

{-
 
-- These things typecheck, but I haven't made sure what they do is sensible.
instance (MonadIO m, Functor m) => MonadIO (ListT m) where
  liftIO = lift . liftIO
 
instance (MonadReader s m, Functor m) => MonadReader s (ListT m) where
  ask     = lift ask
  local f = ListT . local f . runListT
 
instance (MonadState s m, Functor m) => MonadState s (ListT m) where
  get = lift get
  put = lift . put
 
instance MonadCont m => MonadCont (ListT m) where
  callCC f = ListT $
    callCC $ \c -> runListT . f $ \a ->
      ListT . c $ Just (a, ListT $ return Nothing)
 
instance (MonadError e m) => MonadError e (ListT m) where
  throwError = lift . throwError
  -- I can't really decide between those two possible implementations.
  -- The first one is more like the IO monad works, the second one catches
  -- all possible errors in the list.
--  ListT m `catchError` h = ListT $ m `catchError` \e -> runListT (h e)
  (m :: ListT m a) `catchError` h = deepCatch m where
    deepCatch :: ListT m a -> ListT m a
    deepCatch (ListT xs) = ListT $ liftM (fmap $ second deepCatch) xs 
      `catchError` \e -> runListT (h e)

-}{-# LANGUAGE MultiParamTypeClasses #-}
-- module MonadCoalesce where

class Monad m => MonadCoalesce m where
    coalesceLeft :: Monoid a => m (Either a b) -> m (Either a b)

coalesceM :: (MonadCoalesce m, Monoid a) => m a -> m a
coalesceM = liftM (either id undefined) . coalesceLeft . liftM Left

instance (MonadCoalesce m, Monoid s) => MonadCoalesce (StateT s m) where
    coalesceLeft f = StateT $ \s -> 
                       liftM pullState $ coalesceLeft $ liftM pushState $ runStateT f s
        where
          pushState (Left x, s) = Left (x,s)
          pushState (Right x, s) = Right (x,s)
          pullState (Left (x,s)) = (Left x, s)
          pullState (Right (x,s)) = (Right x, s)

instance (MonadCoalesce m) => MonadCoalesce (ReaderT r m) where
    coalesceLeft f = ReaderT $ (coalesceLeft . runReaderT f)

instance MonadCoalesce Identity where
    coalesceLeft = id

instance (Error e, MonadCoalesce m) => MonadCoalesce (ErrorT e m) where
    coalesceLeft f = ErrorT $ liftM swapE $ coalesceLeft $ liftM swapE $ runErrorT f
        where
          swapE :: Either x (Either y z) -> Either y (Either x z)
          swapE = either (Right . Left) (either Left (Right . Right))
-- module MonadIterate where

class MonadCoalesce m => MonadIterate m where
    fixiterM :: Monoid a => (a -> m (Either b a)) -> a -> m b

loop f = fixiterM (const f) ()

instance (MonadIterate m, Monoid s)  => MonadIterate (StateT s m) where
    fixiterM fn init = StateT (\initst ->
                           fixiterM ( \ ~(x, s) -> liftM pullEither (runStateT (fn x) s)) 
                           (init,initst))
        where
          pullEither ~(e, s) = either (\l -> Left (l,s)) (\r -> Right (r,s)) e

instance (MonadIterate m) => MonadIterate (ReaderT r m) where
    fixiterM fn init = ReaderT $ \r -> fixiterM (\x -> runReaderT (fn x) r) init

instance (MonadIterate m, Error e) => MonadIterate (ErrorT e m) where
    fixiterM fn init = ErrorT $ fixiterM (\x -> liftM packError $ runErrorT $ fn x) init
        where
          packError :: Either e (Either b a) -> Either (Either e b) a
          packError = either (Left . Left) (either (Left . Right) Right)

instance MonadIterate Identity where
    fixiterM f x = do
      y <- f x
      case y of
        Left l -> return l
        Right r -> fixiterM f r
-- module ObjectTypes where

type FieldName = String

type FieldSet = S.Set FieldName

data StructType = StructType FieldSet
data NomType = NomType {nomName :: String,
                        nomParents :: [NomType],
                        nomFields :: FieldSet}

instance Eq NomType where
    (==) = (==) `on` nomName
instance Ord NomType where
    compare = compare `on` nomName
instance Show NomType where
    show = nomName

-- Should probably implement C3 or somesuch...
allParents n = 
    let n' = nub (n ++ (n >>= nomParents))
    in if n' == n then n else allParents n'

data ObjType = ObjType (S.Set NomType) (S.Set FieldName) | BottomObj deriving (Eq,Ord)

-- an upper set of nominative types can be represented by its set of minimal elements
-- i.e. a type, represented by the set of supertypes, can equally be represented
-- by the most derived type(s)
-- this form is mostly used for displaying types to the user.
mostDerived :: S.Set NomType -> S.Set NomType
mostDerived s =
    let parents = S.fromList $ concatMap nomParents (S.toList s)
    in s `S.difference` parents

fromNomType n = 
    let noms = S.fromList $ allParents [n]
    in ObjType noms (fromJust $ allNomFields noms)
fromStructType s = ObjType (S.empty) s

instance Show ObjType where
    show BottomObj = "_|_"
    show (ObjType noms fields) = 
        let d = S.toAscList (S.map show $ mostDerived noms)
            (Just nomfields) = allNomFields noms
            f = [if x `S.member` nomfields then x else "*" ++ x | x <- S.toAscList fields]
            j = intercalate
            nomtypes = " & " `j` d
            fieldlist = ", " `j` f
        in nomtypes ++ if null fieldlist then "" else "{" ++ fieldlist ++ "}"

allNomFields noms =
    let allfields = sort [(f,n) | n <- S.toList noms, f <- S.toList $ nomFields n]
        fieldsources = groupBy ((==) `on` fst) allfields
        valid = all (==1) $ map length fieldsources
    in if valid then Just (S.fromList $ map fst allfields) else Nothing

{-
wrong!

validObjType (ObjType noms fields) = 
    noms == S.fromList (allParents (S.toList noms)) && 
    S.unions (map nomFields $ S.toList noms) `S.isSubsetOf` fields
-}

nomTypes (ObjType n _) = n
objTypeFields (ObjType _ f) = S.toAscList f

instance Lattice ObjType where
    extremum Pos = ObjType (S.empty) (S.empty)
    extremum Neg = BottomObj

    merge v a b = case [a,b] \\ [BottomObj] of
                    [x] -> if v == Pos then x else BottomObj
                    [ObjType noms1 fields1, ObjType noms2 fields2] ->
                        let newnom = merge v' noms1 noms2
                            newfields = merge v' fields1 fields2
                        in case allNomFields newnom of
                             Nothing -> BottomObj
                             Just _ -> ObjType newnom newfields
                            where
                              v' = opVariance v
                            

nt a b c = fromNomType $ NomType a (concatMap (S.toList . mostDerived . (\(ObjType n f) -> n)) b) (S.fromList c)
hairy = nt "Hairy" [] ["growHair"]
student = nt "Student" [hairy] ["study","wobble"]
animal = nt "Animal" [] ["eat", "sleep"]
dog = nt "Dog" [animal,hairy] ["bark"]
labrador = nt "Labrador" [dog] []
fish = nt "Fish" [animal] ["wobble"]

data Label = LabelArg | LabelRet | LabelField String Variance deriving (Eq,Ord,Show)
labelVariance LabelArg = Neg
labelVariance LabelRet = Pos
labelVariance (LabelField _ v) = v

data Constructor = CnTop | CnBot | CnVoid | CnFunc | CnObj ObjType deriving (Eq,Ord,Show)
instance Lattice Constructor where
    extremum Pos = CnTop
    extremum Neg = CnBot
    
    merge v CnTop CnTop = CnTop
    merge v CnBot CnBot = CnBot
    merge v CnVoid CnVoid = CnVoid
    merge v CnFunc CnFunc = CnFunc
    merge v (CnObj o1) (CnObj o2) = CnObj (merge v o1 o2)
    merge v c1 c2 | c1 == mergeIdentity v = c2
                  | c2 == mergeIdentity v = c1
                  | otherwise = mergeFailure v

constLabels CnTop = []
constLabels CnBot = []
constLabels CnVoid = []
constLabels CnFunc = [LabelArg, LabelRet]
constLabels (CnObj o) = concat [[LabelField s Neg, LabelField s Pos] | 
                                s <- objTypeFields o]

constLabelDirs = map labelVariance . constLabels
constCommonLabels c1 c2 =
    -- PERF (sorted lists/merge)
    unzip3 [(i1,i2,l) | (i1,l) <- en c1, (i2, l') <- en c2, l == l']
    where
      en c = zip [0..] (constLabels c)

data Constructed a = CN {cnConstructor :: Constructor,
                         cnFields :: [a]}
                     deriving (Eq,Ord)
instance Functor Constructed where
    fmap f (CN c xs) = CN c $ fmap f xs
instance Show a => Show (Constructed a) where
--    show (CN (Constructor "=>" _) [a,b]) = show a ++ " -> " ++ show b
    show (CN CnTop []) = "any"
    show (CN CnBot []) = "none"
    show (CN CnVoid []) = "void"
    show (CN CnFunc [arg,ret]) = "(" ++ show arg ++ " => " ++ show ret ++ ")"
    show (CN (CnObj xs) fs) = show xs ++ show fs

mkCN c ts | length ts == length (constLabels c) = CN c ts

getC "any" [] = mkCN CnTop []
getC "none" [] = mkCN CnBot []
getC "=>" [a,b] = mkCN CnFunc [a,b]
--FIXME
getC "bool" [] = mkCN CnTop []
getC "void" [] = mkCN CnVoid []
getC s _ = error $ "unknown type constructor " ++ s

getCFields fs vs = mkCN (CnObj (fromStructType $ S.fromList fs)) vs
getCField f (vn,vp) = mkCN (CnObj (fromStructType $ S.singleton f)) [vn,vp]

--mkC n ts = Const $ getC n ts


-- module Scoping where

type LLVMFunc = String

type Var = Value

newtype ScopingT m a = Scoping (RWST 
                                 (S.Set Var)  -- Variables closed over from upper scopes
                                 [LLVMFunc]   -- Functions defined
                                 (S.Set Var)  -- Variables used and defined in current function
                                 m a  -- Structs monad provides structure primitives
                                ) deriving (Monad,MonadTrans,MonadFix)
type Scoping = ScopingT (StructGen)
instance LLVMWriter m => LLVMWriter (ScopingT m) where
    writelist xs = Scoping (lift (writelist xs))

functionT = TFunc objectT' [objectT', objectT']
functionT' = TPtr functionT

runSubScope (Scoping x) inscope = do
  ((r, used, newfuncs), code) <- lift $ collectCode (runRWST x inscope S.empty)
  tell newfuncs
  return (r,code,used)

varMark v = modify $ S.insert v

varNew = Scoping $ do
  v <- lift $ structNew ["$"]
  varMark v
  return v

varGet v = Scoping $ do
  varMark v
  lift $ structGet v "$"

varSet v val = Scoping $ do
  varMark v
  lift $ structSet v "$" val

-- genFuncBody generates a new global LLVM function
-- but does not insert any code into the current function
genFuncBody fn = Scoping $ do
  -- Find the set of variables being closed over
  parentvars <- ask
  currentvars <- get
  let inscope = parentvars `S.union` currentvars
      param = Value objectT' "%$param"
  (ret, code, varsused) <- runSubScope (fn param) inscope
  let closedVars = S.toList $ varsused `S.intersection` inscope
      closed = closedVars 
               `zip` 
               ["$closure$"++show i | i <- [0..]]

  -- Mark each of the variables closed over as "used"
  forM closedVars varMark

  -- Generate the LLVM function (the code), which takes an extra parameter
  -- holding the closed environment
  let currentClosure = Value objectT' "%$closure"
  (_, fullcode) <- lift $ collectCode $ do
    forM_ closed $ \(var,field) -> do
      -- FIXME: can structGetIndex directly with some hackery
      ptr <- structIndex currentClosure field
      write $ LLVMInsn OpLoad (Just var) [ptr]
    writelist code
    write $ LLVMInsn OpRet Nothing [ret]
  funcname <- lift $ freshGlobal functionT -- better names?
  tell [writeFunc funcname objectT' [currentClosure, param] fullcode]
  return (funcname, closed)

genClosureHead funcname closed = Scoping $ lift $ do
  -- Generate the closure: a structure containing a function pointer and
  -- a partial environment
  closure <- structNew ("$code$":map snd closed)
  structSet closure "$code$" (mkConstPtrCast objectT' funcname)
  return closure

genClosureFields closure closed = Scoping $ lift $ do
  forM_ closed $ \(var, field) -> do
    structSet closure field var
  return closure

lambda fn = do
  (funcname, closed) <- genFuncBody fn
  closure <- genClosureHead funcname closed
  genClosureFields closure closed

--FIXME buggy as all hell
corecLambda :: ([Value] -> Scoping [Value -> Scoping Value]) -> Scoping [Value]
corecLambda fngen = do
  closures <- lift $ freshInfVar objectT'
  funcs <- fngen closures
  closed <- forM (zip funcs closures) $ \(f,cl) -> do
    (funcname, closed) <- genFuncBody f
    cl' <- genClosureHead funcname closed
    lift $ objRename cl cl'
    return (cl, closed)
  forM closed $ \(cl,closed) -> do
    genClosureFields cl closed

apply closure val = Scoping $ lift $ do
  rawfunction <- structGet closure "$code$"
  funcptr <- expgen functionT' OpPtrCast [rawfunction]
  expgen objectT' OpCall [funcptr, closure, val]

generateCode :: Scoping () -> String
generateCode (Scoping p) = let (((), _, funcs), st, code) = runRWS (runRWST p S.empty S.empty) () (StructGenState 0 M.empty M.empty)
                     in intercalate "\n\n" $ (map pInternedName $ M.toList $ internedNames' st) ++
                                             (map (pStructType $ internedNames' st)
                                                      (M.toList $ structs' st)) ++
                                             (funcs)
    where
      pInternedName (name, Value fieldnameT' sym) =
        let n = litInt32 $ length sym
            hash = litInt32 $ 23
            -- FIXME escaping
            str = Value (TArray (length name) (TBaseType "i8")) ("c"++show name)
            comment = "; Interned \"" ++ name ++ "\"\n"
        in comment ++ sym ++ " = constant " ++ vParam (mkConstStruct [n,hash,str])

      pStructType interns (fields', Value typetableT' sym) =
        let fields = S.toAscList fields'
            hdr = mkConstStruct [litInt8 0, litInt8 0, litInt16 $ length fields]
            perclass = Value (TPtr (TArray 0 objectT)) "null"
            entries = mkConstArr [mkConstStruct [mkConstPtrCast fieldnameT'
                                                     (fromJust $ M.lookup f interns), 
                                                 litInt16 i] 
                                  | (f,i) <- zip fields [0..]]
            comment = "; Structure table for {" ++ intercalate ", " fields ++ "}\n"
        in comment ++ sym ++ " = constant " ++ vParam (mkConstStruct [hdr,perclass,entries])

main = defaultMain
-- module Solver where

data Var = Var { varDir :: Variance,
                 varID :: Unique,
                 varVarBounds :: IORef (M.Map Unique (Weak Var)),
                 varConstBound :: IORef (SmallTerm Var) }

instance Eq Var where (==) = (==) `on` varID
instance Ord Var where compare = compare `on` varID
instance Show Var where
    show v = "$" ++ show (hashUnique (varID v)) ++ show (varDir v)

varNewUnconstrained dir = do
  id <- newUnique
  varBounds <- newIORef (M.empty)
  varConstBound <- newIORef (identitySmallTerm dir)
  return $ Var dir id varBounds varConstBound

varGetVarBounds v = do
  bounds <- readIORef $ varVarBounds v
  vars <- forM (M.toList bounds) (deRefWeak . snd)
  -- FIXME: remove gc-ed vars from bounds?
  return $ map fromJust $ filter isJust vars

varNewCloned' v = do
  id <- newUnique
  varBounds <- readIORef (varVarBounds v)
  constBound <- readIORef (varConstBound v)
  varBoundsR <- newIORef varBounds
  constBoundR <- newIORef constBound
  return $ Var (varDir v) id varBoundsR constBoundR

varSetVarBounds' v vs = do
  refs <- forM vs (\x -> mkWeakPtr x Nothing)
  let bndmap = M.fromList $ zip (map varID vs) refs
  writeIORef (varVarBounds v) bndmap

varAddVarBound (vneg, vpos) 
    | varDir vneg == Neg && varDir vpos == Pos = do
  varAddVarBound' vneg vpos
  varAddVarBound' vpos vneg
      where
        varAddVarBound' v b = do
          ref <- mkWeakPtr b Nothing
          modifyIORef (varVarBounds v) $ M.insert (varID b) ref

varDelVarBound (vneg, vpos) = do
  True <- varCheckVarBound vneg vpos
  del vneg vpos
  del vpos vneg
      where
        del v1 v2 = modifyIORef (varVarBounds v1) $
                    M.delete (varID v2)

varCheckVarBound v b | varDir v == Neg && varDir b == Pos = do
  bounds <- readIORef $ varVarBounds v
  return $ M.member (varID b) bounds

varGetConstBound v = readIORef $ varConstBound v
varSetConstBound v = writeIORef $ varConstBound v

--varConstrainConstBound :: v* -> T* -> IO ()
varConstrainConstBound v bnd = do
  oldbnd <- varGetConstBound v
  let newbnd = mergeSmallTerm (varDir v) oldbnd bnd
  varSetConstBound v newbnd

varNewPair = do
  vpos <- varNewUnconstrained Pos
  vneg <- varNewUnconstrained Neg
  varAddVarBound (vneg, vpos) -- vneg <= vpos
  return (vneg, vpos)

varNewConst dir bound = do
  v <- varNewUnconstrained dir
  varSetConstBound v bound
  return v

--FIXME verify
decomposeSmallConstraint :: (SmallTerm Var, SmallTerm Var) -> Maybe [(Var,Var)]
decomposeSmallConstraint (t1, t2) = -- t1 <= t2
  let (ctor, ts) = mergeConstructed Pos t1 t2
      valid = ctor == cnConstructor t2
      mkConstraint (dir, Just v1, Just v2) =
          [flipByVariance dir (v1', v2') |
           v1' <- v1, v2' <- v2]
      mkConstraint _ = []
  in if valid then Just $ ts >>= mkConstraint else Nothing

incrClose' :: (SmallTerm Var, SmallTerm Var) -> IO ()
incrClose' cn =
  putStrLn ("close:" ++ show (fst cn) ++ "<:" ++ show (snd cn)) >>
  --FIXME error messages
  let (Just cns) = decomposeSmallConstraint cn
  in sequence_ [incrClose (SConstraintVarVar a b) |
                (a,b) <- cns]
{-
  let (ctor, ts) = mergeConstructed Pos t1 t2
  let valid = ctor == cnConstructor t2
  when (not valid) (putStrLn "ohshit") -- FIXME
  forM_ ts $ \(dir, v1, v2) -> do
    when (isJust v1 && isJust v2) $ do
      let vpairs = [(v1', v2') | 
                    v1' <- fromJust v1, v2' <- fromJust v2]
      forM_ (map (flipByVariance dir) vpairs) $ \(a,b) -> 
          incrClose $ SConstraintVarVar a b
-}

incrClose :: SmallConstraint Var -> IO ()
-- incrClose :: (T+ <= T-) -> IO ()

-- FIXME termination
incrClose (SConstraintVarVar vpos vneg) 
    | varDir vpos == Pos && varDir vneg == Neg = do
-- wtf  present <- varCheckVarBound vpos vneg
-- when (not present) $ do
    putStrLn $ "close:" ++ show vpos ++ "<:" ++ show vneg
    posbnd <- varGetVarBounds vpos
    negbnd <- varGetVarBounds vneg
    sequence [varAddVarBound (vn, vp) | vn <- posbnd, vp <- negbnd]
    vposbnd <- varGetConstBound vpos
    vnegbnd <- varGetConstBound vneg
    forM negbnd $ \vp -> do
      -- vpos <= vp
      varConstrainConstBound vp vposbnd
    forM posbnd $ \vn -> do
      -- vn <= vneg
      varConstrainConstBound vn vnegbnd
  
    incrClose' (vposbnd, vnegbnd)
  

incrClose (SConstraintVarBound dir var bound) = do
  varbnd <- varGetVarBounds var

  forM varbnd $ \v -> do
    varConstrainConstBound v bound
  cbnd <- varGetConstBound var

  incrClose' $ flipByVariance dir (cbnd, bound)

-- Type schemes for generalised terms (e.g. top-level functions)
data TypeScheme = TypeScheme [Var] Var

validTypeSchemeDirs (TypeScheme vs v) = 
    all ((==Neg).varDir) vs && varDir v == Pos

-- Create a renamed copy of a type scheme
-- Used when a generalised term is referred to
instantiateTypeScheme :: TypeScheme -> IO TypeScheme
instantiateTypeScheme sch@(TypeScheme vs v) | validTypeSchemeDirs sch = do
  vars <- reachableVariables (v:vs)
  vars' <- mapM varNewCloned' vars
  putStrLn $ show vars ++ " ~~> " ++ show vars'
  applySubsitution (M.fromList $ zip vars vars') vars' sch

-- Variables which are part of a type scheme must not be aliased
-- outside the scheme. All constraints on type scheme variables
-- must already have been applied by the time the scheme is
-- optimised.
optimiseTypeScheme :: TypeScheme -> IO TypeScheme
optimiseTypeScheme sch@(TypeScheme vs v) | validTypeSchemeDirs sch = do
  vars <- reachableVariables (v:vs)
  canonise vars
  -- canonise can add more variables, so we
  -- recalculate the reachable set (this could
  -- be done faster, but this is simpler)
  vars <- reachableVariables (v:vs)
  sub <- minimise vars
  applySubsitution sub vars sch
--  return sch

-- must be given a complete set of root variables
-- also performs a complete garbage collection on the graph
reachableVariables :: [Var] -> IO [Var]
reachableVariables roots = do
  seen <- newIORef M.empty
  let visit v = do
        modifyIORef seen $ M.insert (varID v) v
        vs <- liftM (concat . cnFields) $ varGetConstBound v
        forM_ vs $ \v' -> do
          s <- readIORef seen
          when (not $ M.member (varID v') s) (visit v')
{-        vs <- varGetVarBounds v
        forM_ vs $ \v' -> do
          s <- readIORef seen
          when (not $ M.member (varID v') s) (visit v')-}
  mapM_ visit roots
  found <- readIORef seen
  -- Garbage collection: only those variables reachable
  -- via decomposing constructed bounds are kept.
  -- variables only reachable as var-var bounds are dropped.
  forM_ (M.toList found) $ \(vid,v) -> do
    modifyIORef (varVarBounds v) (`M.intersection` found)
  return $ M.elems found

-- for debugging: version of reachableVariables that performs
-- no GC. May only see a part of the type graph if not given
-- a complete set of roots.
reachableVariables' :: [Var] -> IO [Var]
reachableVariables' roots = do
  seen <- newIORef M.empty
  let visit v = do
        modifyIORef seen $ M.insert (varID v) v
        vs <- liftM (concat . cnFields) $ varGetConstBound v
        forM_ vs $ \v' -> do
          s <- readIORef seen
          when (not $ M.member (varID v') s) (visit v')
        vs <- varGetVarBounds v
        forM_ vs $ \v' -> do
          s <- readIORef seen
          when (not $ M.member (varID v') s) (visit v')
  mapM_ visit roots
  found <- readIORef seen
  return $ M.elems found

-- perform a variable renaming on a type scheme
-- does not change the shape of the constructed bounds
applySubsitution sub vars (TypeScheme vs v) = do
  let subvar v = do
        vbounds <- varGetVarBounds v
        let vbounds' = sortednub (map (sub!) vbounds)
        varSetVarBounds' v vbounds'
        cbound <- varGetConstBound v
        varSetConstBound v (fmap (map (sub!)) cbound)
  mapM_ subvar vars
  return $ TypeScheme (map (sub!) vs) (sub ! v)

-- Pick an arbitrary element from a list, whose elements
-- must all be the same.
-- equivalent to "head", with some extra asserts
same [] = error "same: empty list"
same xs | all (==(head xs)) xs = head xs
        | otherwise = error "same: elements differ"

-- canonise takes the set of reachable variables of a type scheme
canonise :: [Var] -> IO ()
canonise vars = do
  newvarsR <- newIORef M.empty
  initialisedR <- newIORef M.empty
  -- newvars represents the variables to be inserted
  -- initialised represents the set of inserted variables 
  -- that have been given correct bounds. Computing the
  -- bounds of a variable may require introducing yet more
  -- variables, so we keep iterating until newvars is empty
  let subst [] = error "wtf how did you get an empty set"
      subst [v] = return [v] -- already canonical
      subst vs' = do
        let vs = S.fromList vs'
        newvars <- readIORef newvarsR
        initialised <- readIORef initialisedR
        let varmap = newvars `M.union` initialised
        if (M.member vs varmap) 
          then return [varmap ! vs]
          else do
            let dir = same (map varDir vs')
            newv <- varNewUnconstrained dir
            modifyIORef newvarsR (M.insert vs newv)
            return [newv]
      clean v = do
        bound <- varGetConstBound v
        newfields <- mapM subst (cnFields bound)
        varSetConstBound v (bound {cnFields = newfields})
      initBounds (vars,newv) = do
        let variance = same (map varDir $ S.toList vars)
        forM_ (S.toList vars) $ \v -> do
          bnd <- varGetConstBound v
          varConstrainConstBound newv bnd
          varbnds <- varGetVarBounds v
          forM_ varbnds $ \v' -> do
            varAddVarBound $ flipByVariance (opVariance variance) (newv, v')
        modifyIORef newvarsR (M.delete vars)
        modifyIORef initialisedR (M.insert vars newv)
        clean newv
      recVarAdd = do
        newvars <- readIORef newvarsR
        initialised <- readIORef initialisedR
        if newvars == M.empty
          then return ()
          else do
            forM_ (M.toList newvars) initBounds
            recVarAdd
  forM_ vars clean
  recVarAdd

partFinder :: Ord a => [[a]] -> a -> Int
partFinder p = 
    let getp = M.fromList [(v,i) |
                           (i,vs) <- zip [0..] p, 
                           v <- vs]
    in (getp!)

fromSingleton [x] = x
fromSingleton _ = error "Not a singleton list"

minimise :: [Var] -> IO (M.Map Var Var)

minimise vars = do
  boundsets <- liftM (M.fromList . zip vars) $
               mapM (liftM M.keysSet . 
                     readIORef . varVarBounds) vars
  cbounds <- liftM (M.fromList . zip vars) $
             mapM (liftM (fmap fromSingleton) . 
                   readIORef . varConstBound) vars
  let initPartition = groupOn (varDir &&& (cnConstructor . (cbounds!)) &&& (boundsets!)) vars
      recSplit p = let newp = splitPartition p 
                   in if newp == p then p else recSplit newp
      splitPartition :: [[Var]] -> [[Var]]
      splitPartition p = 
        let part = partFinder p
        in concat $ map (groupOn (map part . cnFields . (cbounds!))) p
      bestPartition = recSplit initPartition
  -- Now we have the coarsest valid partition
  -- We can optimise the type scheme by picking a 
  -- representative variable for each equiv. class
  -- and dropping the rest.
  let replacements = M.fromList [(v,head vs) |
                                 vs <- bestPartition,
                                 v <- vs]
  return replacements

allM :: Monad m => [a] -> (a -> m Bool) -> m Bool
allM xs f = foldM (\a b -> liftM (a &&) b) True (map f xs)

entailed :: (Var,Var) -> IO Bool
--entailed (var- <= var+)
entailed cn = do
  -- hist is the set of constraints that we have already
  -- proved, and those that we have decomposed and are
  -- trying to prove. We can assume all of these to already
  -- hold: if they're part of a decomposition assuming them
  -- leads to an inductive proof.
  hist <- newIORef S.empty
  let entailed' cn = do
        putStrLn ("?:" ++ show cn)
        hfound <- liftM (S.member cn) $ readIORef hist
        if hfound 
          then putStrLn ("hist:" ++ show cn) >> return True
          else do
            let (vn,vp) = cn
            vbound <- varCheckVarBound vn vp
            if vbound 
              then putStrLn ("tauto:"++show cn) >> return True
              else do
                modifyIORef hist (S.insert cn)
                vp' <- varGetConstBound vp
                vn' <- varGetConstBound vn
                decompose (vn',vp')
      decompose (tneg,tpos) = do
        let (ctor,ts) = mergeConstructed Pos tneg tpos
            valid = ctor == cnConstructor tpos
            decompConstraint (dir, Just a, Just b) = 
                [flipByVariance dir (fromSingleton a,
                                     fromSingleton b)]
            decompConstraint _ = []
            subcns = ts >>= decompConstraint
        if valid
          then allM subcns entailed'
          else return False
  entailed' cn

subsumes :: (Var,Var) -> IO Bool
-- subsumes (var+ <= rigid+)
-- subsumes (rigid- <= var-)
subsumes cn = do
  -- We keep track of the changes we make to the constraint
  -- graph so we can undo them later
  changes <- newIORef S.empty
  rigidVars <- newIORef S.empty
  let subsumes' (v1,v2) = do
        let variance = same [varDir v1, varDir v2]
            (var,rigid) = flipByVariance variance (v1,v2)
            newcns x = flipByVariance variance (x,rigid)
        modifyIORef rigidVars $ S.insert rigid
        varbounds <- varGetVarBounds var
        --FIXME check
        valid <- allM varbounds $ \v -> do
          isrigid <- liftM (S.member v) $ readIORef rigidVars
          let cns = newcns v
          if isrigid
            then entailed cns
            else do
              varAddVarBound cns
              modifyIORef changes $ S.insert cns
              return True
        v1b <- varGetConstBound v1
        v2b <- varGetConstBound v2
        if (not valid)
          then return False
          else let cns = decomposeSmallConstraint (v1b,v2b)
               in maybe (return False) (flip allM subsumes') cns
  ans <- subsumes' cn
  changes <- liftM S.toList $ readIORef changes
  forM changes varDelVarBound
  return ans
                

showTypeGraph :: Var -> IO ()
showTypeGraph v = do
  let showV v = do
        vbounds <- varGetVarBounds v
        bound <- varGetConstBound v
        let allbounds = intercalate "," $ map show vbounds ++ [show bound]
        let (s1,s2) = flipByVariance (varDir v) (allbounds, show v)
        putStrLn $ s1 ++ " <= " ++ s2
  vars <- reachableVariables' [v]
  forM_ vars showV
     
-- module SolverTest where

-- import DebugSemantics

-- type of "method(x) do return x end"
idFunc = do
  (vn,vp) <- varNewPair
  varNewConst Pos $ getC "=>" [[vn],[vp]]

twocrown = do { (an,ap) <- varNewPair; (bn,bp) <- varNewPair; f1 <- varNewConst Pos $ getC "=>" [[bn],[ap,bp]]; varNewConst Pos $ getC "=>" [[an],[f1]]; }

-- type of "if cond then id else id"
doubleID = do
  t1 <- idFunc -- noFunc Pos
  t2 <- idFunc
  (vn,vp) <- varNewPair
  incrClose (SConstraintVarVar t1 vn)
  incrClose (SConstraintVarVar t2 vn)
  return vp

extraVars v = do
  (vn,vp) <- varNewPair
  incrClose (SConstraintVarVar v vn)
  return vp

anyFunc d = do
  inp <- varNewConst (d `mappend` Neg) $ getC "Top" []
  outp <- varNewConst d $ getC "Bot" []
  varNewConst d $ getC "=>" [[inp],[outp]]

noFunc d = do
  inp <- varNewConst (opVariance d) $ getC "Bot" []
  outp <- varNewConst d $ getC "Top" []
  varNewConst d $ getC "=>" [[inp],[outp]]

coTypeOp v = do
  farg <- varNewConst (opVariance $ varDir v) $ getC "Bot" []
  varNewConst (varDir v) $ getC "=>" [[farg],[v]]

fixCoTypeOp d = do
  (ap,an) <- liftM (flipByVariance d) varNewPair
  fan <- coTypeOp an
  incrClose $ uncurry SConstraintVarVar (flipByVariance d (fan,ap))
  return an

entailmentTest = do
  b <- fixCoTypeOp Pos
  a <- noFunc Neg
  putStrLn $ "a: " ++ show a
  showTypeGraph a
  putStrLn $ "b: " ++ show b
  showTypeGraph b
  entailed (a,b)

subsumptionTest = do
  x <- noFunc Pos
  y <- anyFunc Pos
  putStrLn $ "x: " ++ show x
  showTypeGraph x
  putStrLn $ "y: " ++ show y
  showTypeGraph y
  subsumes (y,x)

testType runDebugSemantics' s = do
  let ut = fmap render $ fromSingleton $ runDebugSemantics' $ runEval' (SymbolTable M.empty M.empty M.empty) $ parseType $ runLexer $ s
  print ut
  t <- fromUserType Pos ut
  showTypeGraph t
  ut' <- toUserType t
  print ut'{-# LANGUAGE GeneralizedNewtypeDeriving, TypeSynonymInstances, FlexibleInstances #-}
-- module Structs where

type FieldName = String

type Field obj field = (obj -> field, field -> obj -> obj)

focus :: MonadState obj m => Field obj field -> State field a -> m a 
focus (getter,setter) mod = do
  st <- get
  let (a, st') = runState mod (getter st)
  put (setter st' st)
  return a

type StructGen = RWS () LLVMCode StructGenState

data StructGenState = StructGenState {
      freshCtr' :: Int,
      structs' :: M.Map (S.Set FieldName) Value,
      internedNames' :: M.Map String Value
}

freshCtr = (freshCtr', \x s -> s{freshCtr'=x})
structs = (structs', \x s -> s{structs'=x})
internedNames = (internedNames', \x s -> s{internedNames'=x})

typetableT = TBaseType "%typetable"
typetableT' = TPtr typetableT
typetableT'' = TPtr typetableT'
fieldnameT = TBaseType "%fieldname"
fieldnameT' = TPtr fieldnameT
objectT = TBaseType "%object"
objectT' = TPtr objectT
objectT'' = TPtr objectT'

--runtime functions
--rtSetField = Value (TBaseType "<func>") "@object_set_field"
--rtGetField = Value (TBaseType "<func>") "@object_get_field"
rtIndexType = Value (TBaseType "<func>") "@typetable_get_index"
rtGetType = Value (TBaseType "<func>") "@object_get_type"
rtAlloc = Value (TBaseType "<func>") "@gcalloc"

rtIntNew = Value (TBaseType "<func>") "@int_new"
rtIntAdd = Value (TBaseType "<func>") "@int_add"

fresh :: StructGen Int
fresh = focus freshCtr $ do
  modify (+1)
  get

internName s = focus internedNames $ do
  found <- gets $ M.lookup s
  if isJust found
    then return $ fromJust found
    else do
      let i32 = TBaseType "i32"
          i8 = TBaseType "i8"
          sz = length s
          g = Value (TPtr (TStruct [i32,i32,TArray sz i8])) ("@F."++s)
      modify $ M.insert s g
      return g

class Monad m => LLVMWriter m where
    writelist :: [LLVMInsn] -> m ()
    write :: LLVMInsn -> m ()
    write x = writelist [x]

instance LLVMWriter StructGen where
    writelist = tell

freshLabel = do
  n <- fresh
  return $ Value labelT ("L"++show n)

freshVar typ = do
  n <- fresh
  return $ Value typ ("%t"++show n)
freshGlobal typ = do
  n <- fresh
  return $ Value (TPtr typ) ("@g" ++ show n)

freshInfVar typ = do
  n <- fresh
  return $ [Value typ ("%t"++show n++"$"++show i) | i <- [0..]]

-- returns a typetable*
genStructTable :: S.Set FieldName -> StructGen Value
genStructTable fs = do
  found <- focus structs $ gets $ M.lookup fs
  forM (S.toList fs) internName
  case found of
    Just x -> return x
    Nothing -> do
      let i32 = TBaseType "i32"
          i16 = TBaseType "i16"
          i8 = TBaseType "i8"
          typ = TStruct [TStruct [i8,i8,i16], TPtr (TArray 0 objectT), TArray (S.size fs) (TStruct [fieldnameT', TBaseType "i16" ])]
      sname <- freshGlobal typ
      focus structs $ modify (M.insert fs sname)
      return sname

expgen typ op args = do
  e <- freshVar typ
  write $ LLVMInsn op (Just e) args
  return e

structTable s = do
  expgen typetableT' OpCall [rtGetType, s]
structGetIndex vtable field = do
  fieldstr <- internName field
  expgen (TBaseType "i16") OpCall [rtIndexType, vtable, mkConstPtrCast fieldnameT' fieldstr]

structGetPtr s idx = do
  expgen objectT'' OpGEP [s, i32 0, i32 1, idx]
          where
            i32 x = Value (TBaseType "i32") (show x)
structIndex s field = do
  vtable <- structTable s
  idx <- structGetIndex vtable field
  structGetPtr s idx

structNew fields = do
  sname <- genStructTable $ S.fromList fields
  obj <- expgen objectT' OpCall [rtAlloc, mkConstPtrCast typetableT' sname]
  ttptr <- expgen typetableT'' OpGEP [obj, Value (TBaseType "i32") "0", Value (TBaseType "i32") "0"]
  write $ LLVMInsn OpStore Nothing [mkConstPtrCast typetableT' sname, ttptr]
  return obj

structSet s field val = do
  ptr <- structIndex s field
  write $ LLVMInsn OpStore Nothing [val, ptr]

structGet s field = do
  ptr <- structIndex s field
  expgen objectT' OpLoad [ptr]

objRename newval obj = do
  write $ LLVMInsn OpGEP (Just newval) [obj, Value (TBaseType "i32") "0"]

collectCode :: StructGen a -> StructGen (a, LLVMCode)
collectCode f = censor (const mempty) (listen f)
-- module SymbolMap (Symbol(), makeSymbol, fromSymbol, hashSymbol,
--                  SymbolMap(), empty, singleton, delete, insert) where

-- A Symbol is a string with a precomputed hash code
data Symbol = Symbol !Int !String

hashSymbol (Symbol i s) = i

-- Equality and ordering check the hash code first before falling back to string compare
instance Eq Symbol where
    (Symbol i1 s1) == (Symbol i2 s2) = i1 == i2 && s1 == s2
instance Ord Symbol where
    (Symbol i1 s1) `compare` (Symbol i2 s2) = compare i1 i2 `mappend` compare s1 s2

instance Show Symbol where
    show (Symbol i s) = show s

-- Some messiness to convert a Word32 hash to a sensible Int 
-- regardless of the number of bits in an Int.
-- (at top level to ensure this is only calculated once)
wordToIntShift = head [i | i <- [0..], (toInteger (maxBound::Word32) `shiftR` i) <= toInteger (maxBound::Int)]

makeSymbol :: String -> Symbol
makeSymbol s = Symbol (toInt hash) s
    where
      -- Hash function based on the 32-bit FNV1a hash
      hash = foldl fnv_update fnv_offset $ map (fromIntegral . ord) s
      fnv_update h d = (h `xor` d) * fnv_prime
      fnv_offset = 2166136261 :: Word32
      fnv_prime = 16777619 :: Word32
      -- truncate the necessary number of bits to make the hash fit
      -- in an Int.
      toInt :: Word32 -> Int
      toInt i = (fromIntegral (i `shiftR` wordToIntShift))

fromSymbol :: Symbol -> String
fromSymbol (Symbol h s) = s

newtype SymbolMap a = SymbolMap (M.IntMap [(Symbol,a)]) 
    deriving Show -- FIXME: the default Show will be pretty ugly

-- Manipulation functions for assocation lists
-- Used as hash buckets to resolve collisions in the IntMap
lmustfind s m = case lfind s m of
                  Nothing -> error $"Symbol "++show s++" not found in map"
                  Just x -> x
lfind s m = Data.List.lookup s m
lput x@(s,v) [] = [(s,v)]
lput x@(s,v) (p1@(s',v'):xs) | s' == s = x:xs
                             | otherwise = p1:(lput x xs)
ldel' s [] = []
ldel' s (p1@(s',v'):xs) | s == s' = xs
                        | otherwise = p1:(ldel' s xs)
ldel s m = case (ldel' s m) of
             [] -> Nothing
             x -> Just x

lsingle s v = lput (s,v) []
ljoin xs1 xs2 = foldl (flip lput) xs2 xs1

-- Actual manipulation functions for SymbolMap
-- Only a few IntMap functions are wrapped at the moment, more will be added as needed.
empty = SymbolMap$ M.empty
singleton s v = SymbolMap$ M.singleton (hashSymbol s) (lsingle s v)
insert s v (SymbolMap m) = SymbolMap$ M.insertWith ljoin (hashSymbol s) (lsingle s v) m
delete s (SymbolMap m) = SymbolMap$ M.update (ldel s) (hashSymbol s) m
lookup s (SymbolMap m) = M.lookup (hashSymbol s) m >>= lfind s

-- module Type where

-- Partition a list into sets by function f s.t. x and y are in the same set
-- iff f x == f y
groupOn :: (Ord b) => (a -> b) -> [a] -> [[a]]
groupOn f = map (map snd) . 
            groupBy ((==) `on` fst) . 
            sortBy (comparing fst) . 
            map (f &&& id)

mergeIdentityC :: Variance -> Constructed v
mergeIdentityC Neg = CN (extremum Pos) []
mergeIdentityC Pos = CN (extremum Neg) []
mergeZeroC v = mergeIdentityC (Neg `mappend` v)

mergeConstructed :: Variance -> Constructed a -> Constructed a -> 
                    (Constructor, [(Variance, Maybe a, Maybe a)])
mergeConstructed v (CN c1 t1) (CN c2 t2) = 
    -- PERF (sorted lists/merge)
    let lbls1 = constLabels c1
        lbls2 = constLabels c2
        c' = merge v c1 c2
        lbls' = constLabels c'
        find l x t = do { i<- findIndex (==l) x; return$ t !! i; }
    in (c', [(labelVariance l, find l lbls1 t1, find l lbls2 t2) | l <- lbls'])

data GroundInstance = GroundInstance [Constructed Int] deriving (Show,Eq)

{-
--sample =GroundInstance$ let c a x = (Constructor a [], x) in [c "c" [1], c"a" [1,3], c"b"[4,5], c"c"[4], c"c"[6], c"c"[7], c"d"[7]]
sample =GroundInstance$ let c a x = (CN (Constructor a []) x) in [c"a" [2,3], c"c"[2], c"b"[4,5], c"c"[4], c"c"[6], c"c"[7], c"d"[7]]

fntoptop = GroundInstance $ [getC "=>" [2,3], getC "Top" [], getC "Top" []]
fnbotbot = GroundInstance $ [getC "=>" [2,3], getC "Bot" [], getC "Bot" []]
fn1 = GroundInstance $ [getC "=>" [2,3], getC "Bot" [], getC "=>" [4,5], getC "Top" [], getC "Top" []]
fn2 = GroundInstance $ [getC "=>" [3,2], getC "Top" [], getC "=>" [4,5], getC "Bot" [], getC "Bot" []]

f1 = GroundInstance$ [getC "=>" [1,2], getC "Bot" [], getC "Top" []]
f2 = GroundInstance$ [getC "=>" [2,3], getC "=>" [1,4], getC "Bot" [], getC "Top" []]

toDot (GroundInstance g) = 
    let edges = [(x,y,p) | (x,(CN _ succ)) <- zip [1..] g, (p,y) <- zip [1..] succ]
        nodes = [(c,x) | (x,(CN (Constructor c _) _)) <- zip [1..] g]
        n x = "n"++show x
        edgetxt = unlines$ [n x ++ " -> " ++ n y ++ "[label=" ++ show p++"]" | (x,y,p) <- edges]
        nodetxt = unlines$ [n x ++ "[label = \""++s++":"++show x++"\"]" | (s,x) <- nodes]
    in "digraph{\n"++nodetxt++edgetxt++"}\n"

minimiseGroundInstance (GroundInstance txtable) = 
    toGroundInstance (recSplit initPartition)
    where
      nstates = length txtable

      states = array (1, nstates) (zip [1..] txtable)

      getPartition :: [[Int]] -> Array Int Int
      getPartition parts = array (1, nstates) $ concat $
                           [[(state, partidx) | state <- partition] 
                                | (partidx, partition) <- zip [1..] parts]
      successors :: Int -> [Int]
      successors = cnFields . (states!)

      -- Initial (coarsest possible) partition
      initPartition = map (map fst) $ groupOn (cnConstructor . snd) $ zip [1..] txtable

      -- Keep splitting partitions until they stop changing
      recSplit p = 
          let newp = splitPartition p
          in if newp == p then p else recSplit newp

      -- Convert final partition into a minimal state-machine (term automaton)
      toGroundInstance parts = 
          let stateP p = (states ! (head (parts !! (p-1))))
              con = cnConstructor . stateP
              succS = cnFields . stateP
              partlist = getPartition parts
              succP = map (partlist!) . succS
              
              nparts = length parts
              partMachine = array (1,nparts) [(i,succP i) | i <- [1..nparts]]

              -- Find a relabeling of the reduced state machine (partMachine) to normal form
              -- i.e. with all states numbered in depth-first-search order from the root
              -- This has the side-effect of removing unreachable states, as they won't be
              -- assigned a label
              relabel :: Int -> IM.IntMap Int -> IM.IntMap Int
              relabel node mapped =
                  case (IM.lookup node mapped) of
                    Just x -> mapped -- this node has already been visited
                    Nothing -> -- visit this node
                        let succs = partMachine ! node
                            visitall = foldl (flip (.)) id $ map relabel succs
                            newmap = IM.insert node (IM.size mapped + 1) mapped
                        in visitall newmap

              -- We have to ensure that we start from the node in partMachine containing
              -- the original state 1
              relabelmap = relabel (partlist!1) IM.empty
              
              lookuplabel node = fromJust $ IM.lookup node relabelmap
                    
              relabeledMachine = array (1,IM.size relabelmap) [(lookuplabel i, (CN (con i) (map lookuplabel $ succP i))) | i <- [1..nparts], i `IM.member` relabelmap]

          in GroundInstance $ elems relabeledMachine
--            (parts, partMachine, relabelmap)
              

      splitPartition :: [[Int]] -> [[Int]]
      splitPartition parts =
          let partlist = getPartition parts
              -- to find the list of successor partitions of a state, find
              -- the partition of each successor state.
              succP :: Int -> [Int]
              succP = map (partlist!) . successors
          in concat $ map (groupOn succP) $ parts

      partition getP states = groupOn (getP . snd) states

groundInstSub (GroundInstance tx1') (GroundInstance tx2') = 
    let tx1 = array (1,length tx1') (zip [1..] tx1')
        tx2 = array (1,length tx2') (zip [1..] tx2')
        recsub v s1 s2 checked = 
            let already = (s1,s2) `S.member` checked
                hypothesis = (s1,s2) `S.insert` checked
                (ctor, ts) = mergeConstructed Pos (tx1!s1) (tx2!s2)
                validHead = groundRel (getGroundSig) v (cnConstructor (tx1!s1)) (cnConstructor (tx2!s2))
                validSub (Pos,Just a,Just b) = recsub (v`mappend`Pos) a b hypothesis
                validSub (Neg,Just a,Just b) = recsub (v`mappend`Neg) a b hypothesis
                validSub _ = True
            in already || (validHead && all validSub ts)
        in recsub Pos 1 1 S.empty

groundInstMerge mergedir (GroundInstance tx1') (GroundInstance tx2') = 
    let 

        -- Our newly constructed ground instance will have O(ntx1 * ntx2) states
        -- (most of which are unneeded, this number will be reduced by normalising)
        -- There are more efficient algorithms, but this is the simplest correct
        -- one and normalising will produce the right type anyway (albeit more slowly)

        -- We require that the two input types contain a top/bottom state. This need
        -- not be the case for arbitrary input types, so we always add such states.
        -- The redundant states will be removed by normalisation later.
            

        addedstates = map mergeIdentityC [Pos `mappend` mergedir, Neg `mappend` mergedir]
        tx1l = tx1' ++ addedstates
        tx2l = tx2' ++ addedstates

        dirToIdx v = fromEnum (v `mappend` mergedir)

        identState stateArr v = 
            let (1,len) = bounds stateArr
            in (len - 1) + dirToIdx v

        ntx1 = length tx1l
        ntx2 = length tx2l

        tx1 = array (1,ntx1) (zip [1..] tx1l)
        tx2 = array (1,ntx2) (zip [1..] tx2l)

        nnew = ntx1 * ntx2 * 2

        oldStateToNew v a b = 1 + (((a-1) * ntx2 + (b-1)) * 2 + dirToIdx v)

        mergeState :: Variance -> Int -> Int -> Constructed Int
        mergeState v a b =
            let (ctor,ts) = mergeConstructed v (tx1!a) (tx2!b)
                mergeSubterm (subv, ta, tb) = 
                    let v' = v `mappend` subv 
                    in oldStateToNew v' 
                           (maybe (identState tx1 v') id ta) 
                           (maybe (identState tx2 v') id tb)
            in (CN ctor $ map mergeSubterm ts)

        newstatelist = do
          a <- [1..ntx1]
          b <- [1..ntx2]
          v <- [Pos `mappend` mergedir, Neg `mappend` mergedir]
          return (v, a, b, mergeState v a b, mergeConstructed v (tx1!a) (tx2!b))
 
        finalans = GroundInstance $ map (\(a,b,c,x,y) -> x) newstatelist
        in finalans

--generateGroundInstance :: Ord v => M.Map v (SmallTerm v) -> v -> GroundInstance
generateGroundInstance vars root =
    let varlist = [root] ++ (filter (/= root) $ M.keys vars)
        varid = M.fromList $ zip varlist [1..]
        convert (CN c vs) = (CN c $ map (\[v] -> fromJust $ M.lookup v varid) vs)
    in GroundInstance $ [convert (fromJust (M.lookup v vars)) | v <- varlist]
--    in (vars,varlist,varid,[M.lookup v vars | v <- varlist])

-}
              
-- A type bound
-- A note on "deriving Eq":
--  Structural equality does not hold for general TypeTerms, for instance
--  Merge [Merge[t]] == Merge[t]. However, we make sure never to directly
--  construct a Merge type, rather we use "merge" to normalise the types
--  so that structural equality holds.
data TypeTerm v = Const (Constructed (TypeTerm v))
                | TVar v
                | Merge [TypeTerm v] -- in a Pos type, Merge is least-upper-bound
                  deriving (Eq,Ord)

instance Functor TypeTerm where
    fmap f (Const con) = Const $ fmap (fmap f) con
    fmap f (TVar v) = TVar $ f v
    fmap f (Merge ts) = Merge $ map (fmap f) ts

-- for debugging
instance Show a => Show (TypeTerm a) where
    show (Const cn) = show cn
{-        if not (any isAlpha name) && length ts == 2 then
            "(" ++ show (ts !! 0) ++ " " ++ name ++ " " ++ show (ts !! 1) ++ ")"
        else
            name ++ (concat $ map ((" "++) . show) ts)-}
    show (TVar v) = filter (/='"') (show v)
    show (Merge ts) = "{" ++ intercalate ", " (map show ts) ++ "}"

sortednub :: Ord a => [a] -> [a]
sortednub = map head . group . sort

merge' v xs =
    let flat = xs >>= flatten
        (varslong, consts) = partition sepVarConst flat
        const = if null consts then identity else foldl1 mergeConst consts 
        vars = sortednub varslong
        identity = Const $ mergeIdentityC v
        zero = Const $ mergeZeroC v
    in case (const, vars) of
         (_, []) -> const
         (c, _) | c == identity -> case vars of
                                     [] -> identity
                                     [x] -> x
                                     _ -> Merge vars
         (c, _) | c == zero -> zero
         _ -> Merge (const:vars)
        where
          flatten (Merge x) = x
          flatten x = [x]
          sepVarConst (TVar _) = True
          sepVarConst (Const _) = False
          mergeConst (Const t1) (Const t2) = 
              let (ctor, ts) = mergeConstructed v t1 t2
              in Const (CN ctor $ map mergeSubterm ts)
                 where
                   mergeSubterm (v', Nothing, Just y) = y
                   mergeSubterm (v', Just x, Nothing) = x
                   mergeSubterm (v', Nothing, Nothing) = Const $ mergeIdentityC (v `mappend` v')
                   mergeSubterm (v', Just x, Just y) = merge' (v `mappend` v') [x,y]

-- Type containment: a partial order on positive or negative type bounds
typeContained :: Ord v => Variance -> TypeTerm v -> TypeTerm v -> Bool
typeContained Pos a b = merge' Pos [a,b] == b
typeContained Neg a b = merge' Neg [a,b] == a

    
-- Constraints are of the form PosType <= NegType
data Constraint v = Constraint (TypeTerm v) (TypeTerm v) deriving (Eq,Ord)
instance Functor Constraint where
    fmap f (Constraint a b) = Constraint (fmap f a) (fmap f b)
instance Show v => Show (Constraint v) where
    show (Constraint a b) = show a ++ " <: " ++ show b

-- Elementary constraints are of the forms
--  Var <= Var, Var <= ConstructedTerm or ConstructedTerm <= Var
data ElementaryConstraint v = ConstraintVarVar v v
                            | ConstraintVarBound Variance v (TypeTerm v)
                              deriving Show

checkElementaryConstraint (Constraint a b) = 
    case (a,b) of
      (TVar v, Const _) -> Just $ ConstraintVarBound Neg v b
      (Const _, TVar v) -> Just $ ConstraintVarBound Pos v a
      (TVar v1, TVar v2) -> Just $ ConstraintVarVar v1 v2
      _ -> Nothing

-- Split a constraint into an equivalent set of elementary constraints
-- May fail, in which case the constraint is unsatisfiable
splitConstraint :: Constraint v -> Maybe [ElementaryConstraint v]
splitConstraint constraint@(Constraint a b) =
    case (checkElementaryConstraint constraint) of
      (Just e) -> Just [e]
      Nothing ->
          case (a,b) of
            -- Split Merge-constraints into individual constraints
            (Merge terms, _) -> splitConstraints $ map (`Constraint` b) terms
            (_, Merge terms) -> splitConstraints $ map (a `Constraint`) terms
            -- Here, we know there are no Merges or elementary constraints
            -- So, both sides must be constructed
            (Const t1@(CN c1 _), Const t2@(CN c2 _)) -> 
                -- Split a constraint between constructed terms into constraints
                -- between common type parameters according to their variances
                let (ctor, ts) = mergeConstructed Pos t1 t2
                    valid = ctor == c2
                    mkConstraint (Pos,Just a,Just b) = [Constraint a b]
                    mkConstraint (Neg,Just a,Just b) = [Constraint b a]
                    mkConstraint (_,_,_) = []
                in
                  if valid then
                      splitConstraints $ ts >>= mkConstraint
                  else
                      -- FIXME: "Nothing" is a particularly uninformative error
                      -- for an unsatisfiable constraint.
                      Nothing
    where
      splitConstraints :: [Constraint v] -> Maybe [ElementaryConstraint v]
      splitConstraints = fmap join . sequence . map splitConstraint
                  
                

-- Small terms are all of the form
-- Const c [Merge [TVar a,Tvar b,...], Merge [...], ...]
-- FIXME: should it be S.Set v rather than [v]?
type SmallTerm v = Constructed [v]

data SmallConstraint v = 
    -- v+ <= v-
    SConstraintVarVar v v

    -- SCVB Pos => v+ <= T-
    -- SCVB Neg => T+ <= v-
  | SConstraintVarBound Variance v (SmallTerm v)
    deriving Show

isCanonical :: SmallTerm v -> Bool
isCanonical (CN c args) = all singleton args
    where singleton = (==1) . length

mergeSmallTerm :: Variance -> SmallTerm v -> SmallTerm v -> SmallTerm v
mergeSmallTerm dir s1 s2 =
    let (ctor, ts) = mergeConstructed dir s1 s2
        merged = map (\(d,v1,v2) -> concat $ maybeToList =<< [v1,v2]) ts
    in (CN ctor merged)

identitySmallTerm :: Variance -> SmallTerm v
identitySmallTerm v = CN (mergeIdentity v) []

checkSmallConstraint :: ElementaryConstraint v -> SmallConstraint v
checkSmallConstraint (ConstraintVarVar v1 v2) = SConstraintVarVar v1 v2
checkSmallConstraint (ConstraintVarBound v var (Const (CN c ts))) = 
    SConstraintVarBound v var (CN c (map fromMergeVar ts))
        where
          fromMergeVar (Merge vs) = map fromVar vs
          fromMergeVar (TVar v) = [v]
          fromVar (TVar v) = v

fromSmallTerm v (CN c ms) = Const (CN c $ map (merge' v . map TVar) ms)
fromSmallConstraint (SConstraintVarVar v1 v2) = ConstraintVarVar v1 v2
fromSmallConstraint (SConstraintVarBound v var t) = 
    ConstraintVarBound v var (fromSmallTerm v t)


-- module TypeChecker where

type Constraints = ReaderT GeneralisationLevel IO
newtype ConstraintGen a = ConstraintGen (ListT Constraints a)
    deriving (Monad,MonadIterate,MonadCoalesce)

varNewPair :: Constraints (GVar, GVar)
varNewPair = do
  genID <- asks generalisationID
  (vn,vp) <- lift $ Solver.varNewPair
  return (Ungen $ UngenVar genID vn, Ungen $ UngenVar genID vp)
varNewConst d b = do
  genID <- asks generalisationID
  var <- lift $ Solver.varNewConst d b
  return $ Ungen $ UngenVar genID var
varNewUnconstrained d = lift $ Solver.varNewUnconstrained d
instantiateTypeScheme s = lift $ Solver.instantiateTypeScheme s
optimiseTypeScheme s = lift $ Solver.optimiseTypeScheme s
varConstrain a b = do
  a' <- getVar a
  b' <- getVar b
  lift $ Solver.incrClose (SConstraintVarVar a' b')

-- FIXME coalesceM
runConstraintGen (ConstraintGen f) = do
  rets <- runAllListT f
  (rn, rp) <- varNewPair
  forM rets $ \r -> varConstrain r rn
  return rp

cgen = ConstraintGen . lift

-- Each GeneralisationLevel represents a nested generalised construct
data GeneralisationLevel = GeneralisationLevel {
  generalisationID :: GeneralisationID,
  importedVars :: IORef (M.Map UngenVar (Var,Var))
}

newtype GeneralisationID = GeneralisationID Unique deriving (Eq,Ord)

data UngenVar = UngenVar GeneralisationID Var deriving (Eq,Ord)
instance Show UngenVar where show (UngenVar _ v) = show v

data GVar = Ungen UngenVar | Gen [UngenVar] TypeScheme

--getUngenVar :: UngenVar -> ConstraintGen Var
getUngenVar ugvar@(UngenVar gid var) = do
  currid <- asks generalisationID
  if currid == gid
    then return var
    else do
      imported <- asks importedVars
      importedMap <- lift $ readIORef imported
      case (M.lookup ugvar importedMap) of
        Just (vn,vp) -> return vp
        Nothing -> do
                   (vn,vp) <- lift $ Solver.varNewPair
                   lift $ writeIORef imported $ M.insert ugvar (vn,vp) importedMap
                   return vp

getVar :: GVar -> Constraints Var

-- Refer to an ungeneralised binding
getVar (Ungen unv) = getUngenVar unv

-- Instantiate a generalised binding
getVar (Gen closed scheme) = do
  TypeScheme closedV' ty' <- instantiateTypeScheme scheme
  lift $ do
    putStrLn "instatiation"
    print closedV'
    t <- toUserType ty'
    print t
  closedV <- mapM getUngenVar closed
  forM_ (zip closedV closedV') $ \(a,b) -> 
      lift $ Solver.incrClose $ SConstraintVarVar a b
  return ty'

generalise :: Constraints UngenVar -> Constraints GVar
generalise cn = do
  currstate <- ask
  imported <- lift $ newIORef M.empty
  genID <- lift $ newUnique
  let substate = GeneralisationLevel {
        generalisationID = GeneralisationID genID,
        importedVars = imported }
  UngenVar _ ty <- lift $ runReaderT cn substate
  (ugvars,vars) <- liftM (unzip . M.toList) $ lift $ readIORef imported
  sch <- optimiseTypeScheme (TypeScheme (map fst vars) ty)

  lift $ do
    let (TypeScheme vars ty) = sch
    putStrLn $ "Generalised closing over: " ++ show ugvars ++ show vars
    t <- toUserType ty
    print t

  return $ Gen ugvars sch

doLambda :: (GVar -> ConstraintGen GVar) -> Constraints UngenVar
doLambda f = do
  (argN, argP) <- varNewPair
  ret <- runConstraintGen $ f argP
  argN' <- getVar argN
  ret' <- getVar ret
  Ungen v <- varNewConst Pos (getC "=>" [[argN'],[ret']])
  return v
  

instance LanguageMonad ConstraintGen () (UngenVar,UngenVar) GVar where 

    condM e = ConstraintGen $ do
      bool <- lift $ varNewConst Neg (getC "bool" [])
      lift $ varConstrain e bool
      (return True `mplus` return False)

    lambdaM f = cgen $ liftM Ungen $ doLambda f

    applyM f arg = cgen $ do
      (retN, retP) <- varNewPair
      arg' <- getVar arg
      retN' <- getVar retN
      funcT <- varNewConst Neg (getC "=>" [[arg'],[retN']])
      varConstrain f funcT
      return retP

    litIntM i = cgen $ varNewConst Pos (getC "int" [])
    litBool i = cgen $ varNewConst Pos (getC "bool" [])
    voidValue = cgen $ varNewConst Pos (getC "void" [])

    varNewM = cgen $ do
      (Ungen vn, Ungen vp) <- varNewPair
      return (vn,vp)
    varSetM (vn, vp) e = cgen $ varConstrain e (Ungen vn)
    varGetM (vn, vp) = cgen $ return $ Ungen vp

    structNewM fs = cgen $ do
      vs <- liftM concat $ forM fs $ \_ -> do
              (vn,vp) <- lift Solver.varNewPair
              return [vn,vp]
      varNewConst Pos (getCFields fs (map (:[]) vs))

    structGetM s fname = cgen $ do
      (fn, fp) <- varNewPair
      unused <- varNewUnconstrained Pos
      fn' <- getVar fn
      s' <- varNewConst Neg (getCField fname ([unused], [fn']))
      varConstrain s s'
      return fp

    structSetM s fname v = cgen $ do
      unused <- varNewUnconstrained Neg
      v' <- getVar v
      s' <- varNewConst Neg (getCField fname ([v'], [unused]))
      varConstrain s s'

    -- FIXME generalisation needs to happen
    letrec fns = do
      fn <- cgen $ generalise $ do
        (vn,vp) <- varNewPair
        [[funcbody]] <- runAllListT $ (\(ConstraintGen x) -> x) $ fns [vp]
        ty <- doLambda funcbody
        varConstrain (Ungen ty) vn
        return ty
      return [fn]
      
-- module UserType where

data UserType t = UserType (TypeTerm t) [Constraint t]
instance Functor UserType where
    fmap f (UserType tt cns) = UserType (fmap f tt) (map (fmap f) cns)

type UniqMap = M.Map Var (Either Var (SmallTerm Var))

-- pTypeVar uniqs norec v -> (rec, tt)
-- where tt represents v and refers to variables in "rec" 
-- and expands no variables in "norec"
pTypeVar :: UniqMap -> S.Set Var -> Var ->
            IO (S.Set Var, TypeTerm Var)
pTypeVar uniq norec v | (v `S.member` norec) || 
                        not (v `M.member` uniq) = 
  return $ (S.singleton v, TVar v)
pTypeVar uniq norec v = do
  let uniqbnd = uniq ! v
  case uniqbnd of
    Left v -> return (S.singleton v, TVar v)
    Right con -> pConst uniq (S.insert v norec) con

pConst uniq norec con = do
  parts <- forM (cnFields con) $ \[v'] -> do
             pTypeVar uniq norec v'
  let (record, fields) = mconcat $ map (id *** (:[])) parts
  return (record, Const (CN (cnConstructor con) fields))
  

getUniq :: Var -> IO (Maybe (Either Var (SmallTerm Var)))
getUniq v = do
  vbounds <- varGetVarBounds v
  con <- varGetConstBound v
  print (v,vbounds,con)
  case (vbounds,con) of
    ([], con) -> return $ Just $ Right con
    --FIXME varpairs?
    ([v'], con) | con == identitySmallTerm (varDir v) -> return $ Just $ Left v'
    _ -> return $ Nothing

getVarConstraints :: IORef (S.Set Var) -> UniqMap -> Var -> IO [TypeTerm Var]
getVarConstraints recR uniq v = do
  vbounds <- liftM (map TVar) $ varGetVarBounds v
  con <- varGetConstBound v
  if con == identitySmallTerm (varDir v)
    then return vbounds
    else do
      (record,tt) <- pConst uniq (S.singleton v) con
      modifyIORef recR (S.union record)
      return (tt:vbounds)

pVarConstraints r u v = do
  cns <- getVarConstraints r u v
  let newcn x = uncurry Constraint $ 
                flipByVariance (varDir v) $
                (x,TVar v)
  return $ map newcn cns

-- Converts a (canonical) type to a user type
toUserType :: Var -> IO (UserType Var)
toUserType rootv = do
  vars <- reachableVariables' [rootv]
  toprint <- newIORef S.empty
  printed <- newIORef S.empty
  uniqs <- liftM (M.fromList . concat) $ 
             forM vars $ \v -> do
               u <- getUniq v
               return $ maybe [] (\x -> [(v,x)]) u
  (record, maintype) <- pTypeVar uniqs S.empty rootv
  modifyIORef toprint (S.union record)
  let allcns = do
        toprint' <- readIORef toprint
        printed' <- readIORef printed
        cns <- forM (S.toList (toprint' `S.difference` printed')) $
          pVarConstraints toprint uniqs
        modifyIORef printed (S.union toprint')
        print cns
        if null cns then return [] else liftM (concat cns++) allcns
  cns <- allcns
  -- FIXME: we can do better than sortednub
  return $ UserType maintype (sortednub cns)

fromUserType :: Ord t => Variance -> UserType t -> IO Var
fromUserType dir (UserType tt cns) = do
  varmapR <- newIORef M.empty
  ptrsR <- newIORef []
  let cvtType dir (TVar v) = do
        varmap <- readIORef varmapR
        vpair <- if M.member v varmap
                   then return (varmap ! v)
                   else do
                     newvpair <- varNewPair
                     ptr <- newStablePtr newvpair
                     modifyIORef ptrsR $ (ptr:)
                     modifyIORef varmapR $ M.insert v newvpair
                     return newvpair
        return $ fst $ flipByVariance (dir `mappend` Neg) vpair
      cvtType dir (Const con) = do
        parts <- sequence [cvtType (dir `mappend` d) t | 
                           (d,t) <- zip (constLabelDirs (cnConstructor con))
                                        (cnFields con)]
        varNewConst dir $ fmap (:[]) $ (CN (cnConstructor con) parts)
  maintype <- cvtType dir tt
  putStrLn "\n0"
  showTypeGraph maintype
  forM cns $ \(Constraint a b) -> do
    a' <- cvtType Pos a
    b' <- cvtType Neg b
    incrClose (SConstraintVarVar a' b')
  putStrLn "\n1"
  showTypeGraph maintype
  putStrLn ""
  ptrs <- readIORef ptrsR
  forM_ ptrs freeStablePtr
  return maintype

instance Show t => Show (UserType t) where
    show (UserType tt []) = show tt
    show (UserType tt cns) = show tt ++ " where " ++ intercalate ", " (map show cns)