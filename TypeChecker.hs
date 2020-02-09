module TypeChecker where

import qualified Data.Set as Set
import qualified Data.Map as Map

import AbsBlu
import ErrM


emptyScope = (Map.empty, Map.empty, Set.empty, False)

baseEnv :: Env
baseEnv = [ emptyScope ]

typeCheck :: Program -> Err ()
typeCheck p = checkProgram baseEnv p

checkProgram :: Env -> Program -> Err ()
checkProgram env (Prog constD varD funD) = do
  env <- checkConstDecls env constD
  env <- checkVarDecls env varD
  env <- checkFunDecls env funD
  return ()

checkList :: Env -> [a] -> (Env -> a -> Err Env)  -> Err Env
checkList env [] _ = return env
checkList env (x:xs) checkOne = do
  env <- checkOne env x
  env <- checkList env xs checkOne
  return env

checkConstDecls :: Env -> ConstDecls -> Err Env
checkConstDecls env ConstEmpty = return env
checkConstDecls env (ConstBlk cds) = checkList env cds checkConstDecl

checkConstDecl :: Env -> ConstDecl -> Err Env
checkConstDecl env (ConstD (l,c) pIdent@(PIdent (pos, name)) typ rExpr) = do
  rExprTyp <- checkRExprType env rExpr
  env' <- addVarToEnv env pIdent (ConstMod, typ)
  checkStmt env' (Assgn [(Var (l,c) pIdent)] Assign rExpr)
  rTyp <- checkRExprType env rExpr
  if typ |>= rTyp
    then return env'
    else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type mismatch. Expected type: " ++ prettyPrint typ ++ " but found " ++ prettyPrint rTyp ++ "."

checkVarDecls :: Env -> VarDecls -> Err Env
checkVarDecls env VarEmpty  = return env
checkVarDecls env (VarBlk vrs) = checkList env vrs checkVarDecl

checkVarDecl :: Env -> VarDecl -> Err Env
checkVarDecl env (VarD (l,c) pIdent@(PIdent (pos, name)) typ mInit) = do
  case mInit of
    NoInit -> addVarToEnv env pIdent (ValMod, typ)
    JustInit (l,c) rExpr -> do
      env' <- addVarToEnv env pIdent (ValMod, typ)
      checkStmt env' (Assgn [(Var (l,c) pIdent)] Assign rExpr)
      rTyp <- checkRExprType env rExpr
      if typ |>= rTyp
        then return env'
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type mismatch. Expected type: " ++ prettyPrint typ ++ " but found " ++ prettyPrint rTyp ++ "."

checkFunDecls :: Env -> FunDecls -> Err Env
checkFunDecls env FunBlkEmpty = return env
checkFunDecls env (FunBlk funcs) = checkList env funcs checkFunDecl

checkFunDecl :: Env -> FunDecl -> Err Env
checkFunDecl env (FunD (l,c) pIdent@(PIdent ((line,column), name)) mParsIn mParsOut fBody pId@(PIdent ((lin,col), n))) = do
  if name == n
    then
      case mParsIn of
        NoParamsIn -> checkFunDecl env (FunD (l,c) pIdent (JustParamsIn []) mParsOut fBody pId)
        JustParamsIn parsIn -> case mParsOut of
          NoParamsOut -> checkFunDecl env (FunD (l,c) pIdent mParsIn (JustParamsOut []) fBody pId)
          JustParamsOut parsOut -> do
            let inTyps = (map pInToType parsIn)
            let outTyps = (map pOutToType parsOut)
            env <- addFunToEnv env pIdent (map pInToType parsIn) (map pOutToType parsOut)
            let env' = emptyScope : env
            env' <- addParamInToEnv env' parsIn
            env' <- addParamOutToEnv env' parsOut
            checkFunBody env' fBody
              where
                pInToType (ParamIn _ _ _ t) = t
                pOutToType (ParamOut _ _ t) = t

                addParamInToEnv :: Env -> [ParamIn] -> Err Env
                addParamInToEnv env [] = return env
                addParamInToEnv env ((ParamIn pos modal pIdent typ):ps) = do
                  env' <- addVarToEnv env pIdent (modal,typ)
                  addParamInToEnv env' ps

                addParamOutToEnv :: Env -> [ParamOut] -> Err Env
                addParamOutToEnv env [] = return env
                addParamOutToEnv env ((ParamOut pos pIdent typ):ps) = do
                  env' <- addVarToEnv env pIdent (ValMod, typ)
                  addParamOutToEnv env' ps
    else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : Function is closed with erroneous name. Expected name \"" ++ prettyPrint pIdent ++ "\", but found name \"" ++ prettyPrint pId ++ "\"."

checkFunBody :: Env -> FBody -> Err Env
checkFunBody env body@(FunBody constDecls varDecls funDecls stmts) = do
  env <- checkConstDecls env constDecls
  env <- checkVarDecls env varDecls
  env <- checkFunDecls env funDecls
  env <- checkStmts env stmts
  return env

checkStmts :: Env -> [Stmt] -> Err Env
checkStmts env [] = return env
checkStmts env stmts = do
  env <- firstPass env stmts
  secondPass env stmts

firstPass :: Env -> [Stmt] -> Err Env
firstPass env [] = return env
firstPass env (stm:stmts) = do
  case stm of
    Label l -> do
      env <- addLabelToEnv env l
      firstPass env stmts
    _ -> firstPass env stmts

secondPass:: Env -> [Stmt] -> Err Env
secondPass env [] = return env
secondPass env stmts = checkList env stmts checkStmt

checkStmt :: Env -> Stmt -> Err Env
checkStmt env stmt = do
  case stmt of
    StmFCall fCall -> do
      checkFunCallType env fCall
      return env
    Break pBreak@(PBreak ((l,c),name)) -> do
      if insideLoop env
        then return env
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid \"break\" operator. This operator is valid only inside a loop."
    Continue pContinue@(PContinue ((l,c),name)) -> do
      if insideLoop env
        then return env
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid \"continue\" operator. This operator is valid only inside a loop."
    GoTo pIdent@(PIdent ((l,c),name)) -> do
      lookUpLabel env pIdent --TODO controllare
      return env
        --else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid \"goto\" operation. Found undeclared label: \"" ++ show name ++ "\"."
    Label l -> return env
    While rExpr stmts -> do
      typ <- checkRExprType env rExpr
      case typ of
        TBasic TBool -> do
          let local = (Map.empty, Map.empty, Set.empty, True)
          let env' = local:env
          checkStmts env' stmts
          return env
        _ -> do
          let (l,c) = getRExprPos rExpr
          fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid type on \"while\" expression. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found: " ++ prettyPrint typ ++ "."
    DoWhile stmts rExpr -> do
      typ <- checkRExprType env rExpr
      case typ of
        TBasic TBool -> do
          let local = (Map.empty, Map.empty, Set.empty, True)
          let env' = local:env
          checkStmts env' stmts
          return env
        _ -> do
          let (l,c) = getRExprPos rExpr
          fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid type on \"do...while\" expression. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found: " ++ prettyPrint typ ++ "."
    For ini@(ForAssgn le' o' re') rExpr inc@(ForAssgn le'' o'' re'') stmts -> do
      checkStmt env (Assgn [le'] o' re')
      typ <- checkRExprType env rExpr
      case typ of
        TBasic TBool -> do
          checkStmt env (Assgn [le''] o'' re'')
          let local = (Map.empty, Map.empty, Set.empty, True)
          let env' = local:env
          checkStmts env' stmts
          return env
        _ -> do
          let (l,c) = getRExprPos rExpr
          fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid type on \"for\" expression. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found: " ++ prettyPrint typ ++ "."
    If rExpr stmts mElseIf mElse -> do
      typ <- checkRExprType env rExpr
      case typ of
        TBasic TBool -> do
          checkStmts env stmts
          case mElseIf of
            NoElseIf -> do
              case mElse of
                NoElse -> return env
                Else stmts -> checkStmts env stmts
            ElseIf rExpr stmts mElseIf -> do
              checkStmt env (If rExpr stmts mElseIf mElse)
              case mElse of
                NoElse -> return env
                Else stmts -> checkStmts env stmts
        _ -> do
          let (l,c) = getRExprPos rExpr
          fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid type on \"if\" expression. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found: " ++ prettyPrint typ ++ "."
    Assgn [] o re -> fail $ "Error at line " ++ "unknown" ++ " column " ++ "unknown" ++ ": at assignment, there are no l-exprs to assign to. The error arises from code:\n" ++ prettyPrint (Assgn [] o re) ++ "\n"
    Assgn lExprs assOp rExpr@(RexprCall (rL,rC) fc@(UserDefFCall pIdent rExprs)) -> do
      let (lL,lC) = getLExprPos (head lExprs)
      if assOp == Assign
        then do
          mapM (checkLExprType env) lExprs
          outTyps <- checkFunCallType env fc
          if length lExprs == length outTyps
            then do
              leTyps <- mapM (checkLExprType env) lExprs
              if all (== True) (zipWith (|>=) leTyps outTyps)
                then
                  return env
                else
                  fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : at assignment, the variable types of the l-exprs and those of called function output do no match."
            else
              fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : at assignment, number of l-exprs and number of function output parameters differ."
        else
          fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ ": cannot perform an operator-assignment with multiple l-exprs."
    Assgn _ _ rExpr@(RexprCall (l,c) fc@(WIntCall pIdent rExprs)) ->
      fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : writeInt cannot be used as assignment r-expr."
    Assgn _ _ rExpr@(RexprCall (l,c) fc@(WFloatCall pIdent rExprs)) ->
      fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : writeFloat cannot be used as assignment r-expr."
    Assgn _ _ rExpr@(RexprCall (l,c) fc@(WCharCall pIdent rExprs)) ->
      fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : writeChar cannot be used as assignment r-expr."
    Assgn _ _ rExpr@(RexprCall (l,c) fc@(WStringCall pIdent rExprs)) ->
      fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : writeString cannot be used as assignment r-expr."
    Assgn [lExpr] assOp rExpr -> do
      lTyp <- checkLExprType env lExpr
      rTyp <- checkRExprType env rExpr
      let (lL,lC) = getLExprPos lExpr
      case assOp of
        Assign -> if lTyp |>= rTyp
                    then return env
                    else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint lTyp ++ " but found " ++ prettyPrint rTyp ++ "."
        AssignMul -> if (TBasic TReal) |>= lTyp
                       then if lTyp |>= rTyp
                         then return env
                         else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint lTyp ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TReal) ++ " but found " ++ prettyPrint lTyp ++ "."
        AssignAdd -> if (TBasic TReal) |>= lTyp
                       then if lTyp |>= rTyp
                         then return env
                         else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint lTyp ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TReal) ++ " but found " ++ prettyPrint lTyp ++ "."
        AssignDiv -> if (TBasic TReal) |>= lTyp
                       then if lTyp |>= rTyp
                         then return env
                         else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint lTyp ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TReal) ++ " but found " ++ prettyPrint lTyp ++ "."
        AssignSub -> if (TBasic TReal) |>= lTyp
                       then if lTyp |>= rTyp
                         then return env
                         else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint lTyp ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TReal) ++ " but found " ++ prettyPrint lTyp ++ "."
        AssignPow -> if (TBasic TReal) |>= lTyp
                       then if lTyp |>= rTyp
                         then return env
                         else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint lTyp ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TReal) ++ " but found " ++ prettyPrint lTyp ++ "."
        AssignAnd -> if (TBasic TBool) |>= lTyp
                       then if (TBasic TBool) |>= rTyp
                            then return env
                            else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found " ++ prettyPrint lTyp ++ "."
        AssignOr -> if (TBasic TBool) |>= lTyp
                       then if (TBasic TBool) |>= rTyp
                            then return env
                            else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found " ++ prettyPrint rTyp ++ "."
                       else fail $ "Error at line " ++ show lL ++ " column " ++ show lC ++ " : type mismatch in assignment. Expected type: " ++ prettyPrint (TBasic TBool) ++ " but found " ++ prettyPrint lTyp ++ "."
    Assgn lExprs _ _ -> do
      let (l,c) = getLExprPos (head lExprs)
      fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : cannot assign one r-value to more than one l-expr."


getRExprPos :: RExpr -> (Int,Int)
getRExprPos (Or pos _ _) = pos
getRExprPos (And pos _ _) = pos
getRExprPos (Eq pos _ _) = pos
getRExprPos (NEq pos _ _) = pos
getRExprPos (Lt pos _ _) = pos
getRExprPos (LEq pos _ _) = pos
getRExprPos (Gt pos _ _) = pos
getRExprPos (GEq pos _ _) = pos
getRExprPos (Add pos _ _) = pos
getRExprPos (Sub pos _ _) = pos
getRExprPos (Mul pos _ _) = pos
getRExprPos (Div pos _ _) = pos
getRExprPos (Mod pos _ _) = pos
getRExprPos (RexprCall pos _) = pos
getRExprPos (ArrayElems rExprs) = searchPos rExprs
  where
    searchPos [] = (-1,-1) -- undefined
    searchPos (r:rs) = do
      let pos = getRExprPos r
      if pos /= (-1,-1)
        then pos
        else searchPos rs
--getRExprPos (ArrayElems rExprs) = (-1,-1) -- cannot answers this
getRExprPos (AddrOf pos _) = pos
getRExprPos (Not pos _) = pos
getRExprPos (UnMin pos _) = pos
getRExprPos (UnPlus pos _) = pos
getRExprPos (Lexpr pos _) = pos
getRExprPos (Integer pos _) =pos
getRExprPos (Real pos _) = pos
getRExprPos (Char pos _) = pos
getRExprPos (String pos _) = pos
getRExprPos (Bool pos _) = pos

getLExprPos :: LExpr -> (Int,Int)
getLExprPos (Deref pos _) = pos
getLExprPos (ElemAt pos _ _) = pos
getLExprPos (Var pos _) = pos

checkRExprType :: Env -> RExpr -> Err Type
checkRExprType env rExpr = do
  case rExpr of
    Or (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      case typ1 of
        TBasic TBool -> do
          typ2 <- checkRExprType env rExpr2
          case typ2 of
            TBasic TBool -> return $ TBasic TBool
            _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in second operand of bool operation. Expected type " ++ prettyPrint TBool ++ " but found " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in first operand of bool operation. Expected type " ++ prettyPrint TBool ++ " but found " ++ prettyPrint typ1 ++ "."
    And (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      case typ1 of
        TBasic TBool -> do
          typ2 <- checkRExprType env rExpr2
          case typ2 of
            TBasic TBool -> return $ TBasic TBool
            _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in second operand of bool operation. Expected type " ++ prettyPrint TBool ++ " but found " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in first operand of bool operation. Expected type " ++ prettyPrint TBool ++ " but found " ++ prettyPrint typ1 ++ "."
    Eq (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case tMax typ1 typ2 of
        Just _ -> return $ TBasic TBool
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in relation operation \"=\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    NEq (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case tMax typ1 typ2 of
        Just _ -> return $ TBasic TBool
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in relational operation \"<>\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Lt (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case tMax typ1 typ2 of
        Just _ -> return $ TBasic TBool
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in relational operation \"<\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    LEq (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case tMax typ1 typ2 of
        Just _ -> return $ TBasic TBool
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in relational operation \"<=\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Gt (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case tMax typ1 typ2 of
        Just _ -> return $ TBasic TBool
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in relational operation \">\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    GEq (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case tMax typ1 typ2 of
        Just _ -> return $ TBasic TBool
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in relational operation \">=\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Add (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case (tMax typ1 typ2) of
        Just t -> if (t |<= (TBasic TReal))
          then return t
          else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"+\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"+\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Sub (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case (tMax typ1 typ2) of
        Just t -> if (t |<= (TBasic TReal))
          then return t
          else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"-\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"-\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Mul (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case (tMax typ1 typ2) of
        Just t -> if (t |<= (TBasic TReal))
          then return t
          else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"*\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"*\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Div (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case (tMax typ1 typ2) of
        Just t -> if (t |<= (TBasic TReal))
          then return t
          else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"/\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"/\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    Mod (l,c) rExpr1 rExpr2 -> do
      typ1 <- checkRExprType env rExpr1
      typ2 <- checkRExprType env rExpr2
      case (tMax typ1 typ2) of
        Just t -> if (t |<= (TBasic TInt))
          then return t
          else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"%\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in binary arithmetic operation \"%\". Cannot perform such operation on two expressions of types: " ++ prettyPrint typ1 ++ " and " ++ prettyPrint typ2 ++ "."
    RexprCall (l,c) fCall -> do
      typs <- checkFunCallType env fCall
      if (length typs) == 1
        then return (head typs)
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : only functions which have exactly  one output parameter can be used as r-exprs"
    ArrayElems rExprs -> do
      lTyps <- mapM (checkRExprType env) rExprs
      let maxTyp = tMaxL lTyps
      case maxTyp of
        Just t -> return (TArr t ArrNoSize)
        Nothing -> fail $ "Error in an array declaration. Used types:\n" ++ show lTyps ++ "\n are not compatible in the array:\"" ++ show (take 50 (prettyPrint (ArrayElems rExprs)) ++ "...")
    AddrOf (l,c) lExpr -> do
      typ <- checkLExprType env lExpr
      return (TPt typ)
    Not (l,c) rExpr -> do
      typ <- checkRExprType env rExpr
      case typ of
        TBasic TBool -> return typ
        _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in bool operation \"!\". Cannot perform such operation on expression of type: " ++ prettyPrint typ ++ "."
    UnMin (l,c) rExpr -> do
      typ <- checkRExprType env rExpr
      if (typ |<= (TBasic TReal))
        then return typ
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in unary arithmetic operation \"-\". Cannot perform such operation on expression of type: " ++ prettyPrint typ ++ "."
    UnPlus (l,c) rExpr -> do
      typ <- checkRExprType env rExpr
      if (typ |<= (TBasic TReal))
        then return typ
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : type error in unary arithmetic operation \"-\". Cannot perform such operation on expression of type: " ++ prettyPrint typ ++ "."
    Lexpr (l,c) lExpr -> do
      checkLExprType env lExpr
    Integer pos pInteger -> do
      return $ TBasic TInt
    Real pos pReal -> do
      return $ TBasic TReal
    Char pos pChar -> do
      return $ TBasic TChar
    String pos pString -> do
      return $ TBasic TString
    Bool pos pBool -> do
      return $ TBasic TBool


checkFunCallType :: Env -> FunCall -> Err [Type]
checkFunCallType env fCall =
  case fCall of
    UserDefFCall pIdent@(PIdent ((l,c),s)) rExprs -> do
      sig <- lookUpFun env pIdent
      let inPars = fst sig
      let outPars = snd sig
      if (length inPars /= length rExprs)
        then fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : cannot match number of arguments in a call for function" ++ prettyPrint fCall ++ "."
        else do
          check <- checkParams inPars rExprs 1
          return outPars
            where
              checkParams :: [Type] -> [RExpr] -> Int -> Err ()
              checkParams [] [] _ = return ()
              checkParams (t:ts) (re:res) nPar = do
                reTyp <- checkRExprType env re
                if (t |>= reTyp)
                  then checkParams ts res (nPar+1)
                  else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : cannot match parameter number " ++ show nPar ++ " in a call for function " ++ prettyPrint fCall ++ "."
    WIntCall pWriteInt@(PWriteInt ((l,c),name)) rExpr -> do
      rTyp <- checkRExprType env rExpr
      if rTyp |<= (TBasic TInt)
        then return []
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid function call of \"" ++ prettyPrint pWriteInt ++ ". Expected type: " ++ prettyPrint (TBasic TInt) ++ " but found: " ++ prettyPrint rTyp ++ "."
    WFloatCall pWriteFloat@(PWriteFloat ((l,c),name)) rExpr -> do
      rTyp <- checkRExprType env rExpr
      if rTyp |<= (TBasic TReal)
        then return []
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid function call of \"" ++ prettyPrint pWriteFloat ++ ". Expected type: " ++ prettyPrint (TBasic TReal) ++ " but found: " ++ prettyPrint rTyp ++ "."
    WCharCall pWriteChar@(PWriteChar ((l,c),name)) rExpr -> do
      rTyp <- checkRExprType env rExpr
      if rTyp |<= (TBasic TChar)
        then return []
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid function call of \"" ++ prettyPrint pWriteChar ++ ". Expected type: " ++ prettyPrint (TBasic TChar) ++ " but found: " ++ prettyPrint rTyp ++ "."
    WStringCall pWriteString@(PWriteString ((l,c),name)) rExpr -> do
      rTyp <- checkRExprType env rExpr
      if rTyp |<= (TBasic TString)
        then return []
        else fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : invalid function call of \"" ++ prettyPrint pWriteString ++ ". Expected type: " ++ prettyPrint (TBasic TString) ++ " but found: " ++ prettyPrint rTyp ++ "."
    RIntCall pReadInt -> return [TBasic TInt]
    RFloatCall pReadFloat -> return [TBasic TReal]
    RCharCall pReadChar -> return [TBasic TChar]
    RStringCall pReadString -> return [TBasic TString]

checkLExprType :: Env -> LExpr -> Err Type
checkLExprType env lExpr = do
  case lExpr of
    Deref (l,c) rExpr -> do
      rTyp <- checkRExprType env rExpr
      case rTyp of
        TPt t -> return t
        _ -> fail $ "Error at line "  ++ show l ++ " column " ++ show c ++ " : type error in dereference operation \"$\". Cannot perform such operation on expression of type: " ++ prettyPrint rTyp ++ "."
    ElemAt (l,c) lExpr rExpr -> do
      lTyp <- checkLExprType env lExpr
      case lTyp of
        TArr t _ -> do
          rTyp <- checkRExprType env rExpr
          if rTyp |<= (TBasic TInt)
            then return t
            else fail $  "Error at line "  ++ show l ++ " column " ++ show c ++ " : type error in indexing operation \"$\". Cannot index with expression of type: " ++ prettyPrint rTyp ++ "."
        _ -> fail $  "Error at line "  ++ show l ++ " column " ++ show c ++ " : type error in indexing operation \"$\". Cannot index an expression of type: " ++ prettyPrint lTyp ++ "."
    Var (l,c) pIdent -> do
      typ <- lookUpVar env pIdent
      return $ typ

type Env = [(VarSigs, FunSigs, LabelSigs, Bool)]
type VarSigs = Map.Map String  (Modality, Type)
type FunSigs = Map.Map String ([Type], [Type])
type LabelSigs = Set.Set String

insideLoop :: Env -> Bool
insideLoop env = isLoop (head env)
  where
    isLoop local@(_, _, _, loop) = loop

lookUpVar :: Env -> PIdent -> Err Type
lookUpVar [] pIdent@(PIdent ((l,c),name)) = fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : using undeclared variable \"" ++ show name ++  "\"."
lookUpVar (loc:ext) pIdent@(PIdent ((l,c),name)) = do
  case Map.lookup name (getVarSigs loc) of
    Nothing -> lookUpVar ext pIdent
    Just (m,t) -> return t

lookUpFun :: Env -> PIdent -> Err ([Type],[Type])
lookUpFun [] pIdent@(PIdent ((l,c),name)) = fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : using undeclared function \"" ++ show name ++  "\"."
lookUpFun (loc:ext) pIdent@(PIdent ((l,c),name)) = do
  case Map.lookup name (getFunSigs loc) of
    Nothing -> lookUpFun ext pIdent
    Just sig -> return sig

lookUpLabel :: Env -> PIdent -> Err ()
lookUpLabel [] pIdent@(PIdent ((l,c),name)) = fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : using undeclared label " ++ show name ++  "."
lookUpLabel (loc:ext) pIdent@(PIdent ((l,c),name)) = do
  if Set.member name (getLabelSigs loc)
    then return ()
    else lookUpLabel ext pIdent

getVarSigs :: (VarSigs, FunSigs, LabelSigs, Bool) -> VarSigs
getVarSigs (v, _, _, _) = v

getFunSigs :: (VarSigs, FunSigs, LabelSigs, Bool) -> FunSigs
getFunSigs (_, f, _, _) = f

getLabelSigs :: (VarSigs, FunSigs, LabelSigs, Bool) -> LabelSigs
getLabelSigs (_, _, l, _) = l

getBool :: (VarSigs, FunSigs, LabelSigs, Bool) -> Bool
getBool (_, _, _, b) = b

addVarToEnv :: Env -> PIdent -> (Modality, Type) -> Err Env
addVarToEnv env pIdent@(PIdent ((l,c),name)) typ@(m, t) = do
  let localEnv = head env
  case Map.lookup name (getVarSigs localEnv) of
    Nothing -> do
      let env' = (Map.insert name typ (getVarSigs localEnv), getFunSigs localEnv, getLabelSigs localEnv, getBool localEnv ) : (tail env)
      return env'
    Just _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : variable or constant named \"" ++ prettyPrint pIdent ++ "\" already declared."

addFunToEnv :: Env -> PIdent -> [Type] -> [Type] -> Err Env
addFunToEnv env pIdent@(PIdent ((l,c), name)) inTyps outTyps = do
  let localEnv = head env
  case Map.lookup name (getFunSigs localEnv) of
    Nothing -> do
      let env' = (getVarSigs localEnv, Map.insert name (inTyps, outTyps) (getFunSigs localEnv), getLabelSigs localEnv, getBool localEnv ) : (tail env)
      return env'
    Just _ -> fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : function named " ++ prettyPrint pIdent ++ " already declared."

addLabelToEnv :: Env -> PIdent -> Err Env
addLabelToEnv env pIdent@(PIdent ((l,c), name)) = do
  let localEnv = head env
  if Set.member name (getLabelSigs localEnv)
    then fail $ "Error at line " ++ show l ++ " column " ++ show c ++ " : label named " ++ show name ++ " already declared."
    else do
      let env' = (getVarSigs localEnv, getFunSigs localEnv, Set.insert name (getLabelSigs localEnv), getBool localEnv ) : (tail env)
      return env'

-- Hierarchy of basic types
data BasTypHie = BTHNode (Maybe BasicType) [BasTypHie]

allBasT :: BasTypHie
allBasT = BTHNode Nothing [BTHNode (Just TReal) [BTHNode (Just TInt) [BTHNode (Just TChar) []]], BTHNode (Just TBool) [], BTHNode (Just TString) []]

bthGet :: BasicType -> BasTypHie -> Maybe BasTypHie
bthGet bt n@(BTHNode (Just bt') _) | bt == bt' = Just n
bthGet bt (BTHNode _ cs) = bthLstGet bt cs
                           where bthLstGet bt [] = Nothing
                                 bthLstGet bt (n:ns) =
                                   case bthGet bt n of
                                     Just m  -> Just m
                                     Nothing -> bthLstGet bt ns


tMax :: Type -> Type -> Maybe Type
tMax t' t'' | t' |>= t'' = Just t'
            | t' |< t'' = Just t''
            | otherwise    = Nothing

tMaxL :: [Type] -> Maybe Type
tMaxL ts = foldr tMax' (Just TVoid) (map Just ts)
        where tMax' (Just t1) (Just t2) = tMax t1 t2
              tMax' _ _ = Nothing


(|=) :: Type -> Type -> Bool
(|=) = (==)
(|/=) :: Type -> Type -> Bool
(|/=) = (/=)
(|<) :: Type -> Type -> Bool
(|<) t' t'' = t'' |> t'
(|<=) :: Type -> Type -> Bool
(|<=) t' t'' = t'' |>= t'
(|>) :: Type -> Type -> Bool
(|>) t' t'' = (t' |/= t'') && (t' |>= t'')
(|>=) :: Type -> Type -> Bool
(|>=) (TBasic tb') (TBasic tb'') = case bthGet tb' allBasT of
                                     Just th' -> case bthGet tb'' th' of
                                                   Nothing -> False
                                                   Just _  -> True
(|>=) (TArr t' _) (TArr t'' _) = t' |>= t''
(|>=) (TPt t') (TPt t'') = t' |>= t''
(|>=) _ TVoid = True
(|>=) _ _ = False
