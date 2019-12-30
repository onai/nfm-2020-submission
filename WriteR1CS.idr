module WriteR1CS

import Data.List
import Examples.SExpr
import Examples.EnvironmentVF

%access export
%default partial
%access public export

data Expression : (expression : SExpr) -> Type where
    IsDigit  : Expression (MkDigit digit)
    IsPlus   : Expression (MkArithGate left right PLUS)
    IsSTREQ  : Expression (MkSTREQ left right)
    IsConcat : Expression (MkConcat left right)
    IsAppend : Expression (MkAppend item coll)

data VarOrDigit : (expression : SExpr) -> Type where
    IsADigit : VarOrDigit (MkDigit d)
    IsAVar   : VarOrDigit (MkVar name)

data R1CSOperator = PLUS | MINUS | DIGIT | ASGN | MUL

data DigitVarOrNil : Type where
    DigitLeaf : Integer -> DigitVarOrNil
    VarLeaf : Nat -> DigitVarOrNil
    NilLeaf : DigitVarOrNil

Show DigitVarOrNil where
    show (DigitLeaf x) = show x
    show (VarLeaf k) = "var" ++ show k
    show NilLeaf = "nil"

-- a = b + c is a type of R1CS assignment.
-- NoOp is just a NoOp - say you just drop a var or something
data R1CSStatement = Operation Nat R1CSOperator DigitVarOrNil DigitVarOrNil

data Variable : SExpr -> Type where
    IsVariable : (name : String) -> (Variable (MkVar name))

Show R1CSStatement where
    show (Operation varCnt PLUS stuffLeft stuffRight) = ("var" ++ (show (S varCnt))) ++ " <- " ++ "PLUS " ++ (show stuffLeft) ++ " " ++ (show stuffRight)
    show (Operation varCnt DIGIT stuffLeft stuffRight) = ("var" ++ (show (S varCnt))) ++ " <- " ++ "DIGIT " ++ (show stuffLeft) ++ " " ++ (show stuffRight)

data VariableLookup : SExpr -> List (String, Nat) -> Nat -> Type where
    VariableHere : (varName : String) ->
                   (varNo : Nat) ->
                   (remaining : List (String, Nat)) ->
                   VariableLookup (MkVar varName) ((varName, varNo) :: remaining) varNo

    VariableLater : (varName : String) ->
                    (curName : String) ->
                    (Not (curName = varName)) ->
                    (varNo : Nat) ->
                    (remaining : List (String, Nat)) ->
                    (remainingPrf : VariableLookup (MkVar varName) remaining theVarNo) ->
                    VariableLookup (MkVar varName) ((curName, varNo) :: remaining) theVarNo

cantLookupEmptyBindings : (name : String) -> (varNo : Nat ** VariableLookup (MkVar name) [] varNo) -> Void
cantLookupEmptyBindings name (varNo ** pf) with (pf)
    | (VariableHere _ _ _) impossible
    | (VariableLater _ _ _ _ _ _) impossible

-- neitherFirstNotRest : (varNo : Nat) -> (xs : List (String, Nat)) -> (contra : (varNo1 : Nat ** VariableLookup (MkVar name) xs varNo1) -> Void) -> (nameEqContra : (varName = name) -> Void) -> (varNo2 : Nat ** VariableLookup (MkVar name) ((varName, varNo) :: xs) varNo2) -> Void
-- neitherFirstNotRest varNo xs contra nameEqContra (varNo ** (VariableHere varName varNo xs)) = nameEqContra Refl
-- neitherFirstNotRest varNo xs contra nameEqContra (remainingVarNo ** (VariableLater name curName _ varNo xs remainingPrf)) = contra (remainingVarNo ** remainingPrf)

-- lookupVariable : (var : SExpr) -> (isVar : Variable var) -> (bindings : List (String, Nat)) -> Dec (varNo ** (VariableLookup var bindings varNo))
-- lookupVariable (MkVar name) (IsVariable name) [] = No (cantLookupEmptyBindings name)
-- lookupVariable (MkVar name) (IsVariable name) ((varName, varNo) :: xs) = case (decEq varName name) of
--     (Yes Refl) => Yes (varNo ** (VariableHere varName varNo xs))
--     (No nameEqContra) => case (lookupVariable (MkVar name) (IsVariable name) xs) of
--         (Yes (remainingVarNo ** remainingPrf)) => Yes (remainingVarNo ** (VariableLater name varName nameEqContra varNo xs remainingPrf))
--         (No contra) => No (neitherFirstNotRest varNo xs contra nameEqContra)

-- OperationSeq is a sequence of operations for an SExpr
--- startVarNo is the starting var # available for assignment
--- varBindings the existing set of bindings
--- sexprList is the global sexpressions list obtained from the parse
--- List R1CSStatement is the list of R1CS statements
--- nextVarNo is the next available Nat to assign
--- newBindings is a new set of bindings the SExpr writing phase believes the next SExpr needs to see
--- depth : the depth of an SExpr
data OperationSeq : (expression : SExpr) ->
                    (startVarNo : Nat) ->
                    (varBindings : List (String, Nat)) ->
                    (sexprList : SExprList) ->
                    (List R1CSStatement) ->
                    (nextVarNo : Nat) ->
                    (newBindings : List Nat) ->
                    (depth : Nat) -> Type where

    -- Assign to nextVar the specified Integer, and then continue
    WriteDigit : (startVarNo : Nat) ->
                 (digit : Integer) ->
                 (existingVarBindings : List (String, Nat)) ->
                 (sexprList : SExprList) ->
                 OperationSeq (MkDigit digit)
                              startVarNo
                              existingVarBindings
                              sexprList
                              ((Operation startVarNo
                                          DIGIT
                                          (DigitLeaf digit)
                                          NilLeaf) :: [])
                              (S startVarNo)
                              [] -- no new bindings
                              k  -- no expansion so no change in depth

    -- Execute left, Execute right, then collect their results in 2 vars
    -- Finally do a PLUS of these 2 vars and then return the next available counter
    WritePlus : (startVarNo : Nat) ->
                (existingVarBindings : List (String, Nat)) ->
                (sexprList : SExprList) ->
                (leftExpr : SExpr) ->
                (rightExpr : SExpr) ->
                (leftExprOperationSeq : OperationSeq leftExpr
                                                     startVarNo
                                                     existingVarBindings
                                                     sexprList
                                                     leftExprOperations
                                                     (S leftResultVarNo)
                                                     []
                                                     k) ->
                (rightExprOperationSeq : OperationSeq rightExpr
                                                      (S leftResultVarNo)
                                                      existingVarBindings
                                                      sexprList
                                                      rightExprOperations
                                                      (S rightResultVarNo)
                                                      []
                                                      k) ->
                OperationSeq (MkArithGate leftExpr rightExpr PLUS)
                             startVarNo
                             existingVarBindings
                             sexprList
                             (leftExprOperations ++ rightExprOperations ++ ((Operation (S rightResultVarNo)
                                                                                       PLUS
                                                                                       (VarLeaf leftResultVarNo)
                                                                                       (VarLeaf rightResultVarNo))
                                                                                       :: []))
                             (S (S rightResultVarNo))
                             []
                             k

    -- Execute left, Execute right, then collect their results in 2 vars
    -- Finally do a PLUS of these 2 vars and then return the next available counter
    WriteMinus : (startVarNo : Nat) ->
                 (existingVarBindings : List (String, Nat)) ->
                 (sexprList : SExprList) ->
                 (leftExpr : SExpr) ->
                 (rightExpr : SExpr) ->
                 (leftExprOperationSeq : OperationSeq leftExpr
                                                     startVarNo
                                                     existingVarBindings
                                                     sexprList
                                                     leftExprOperations
                                                     (S leftResultVarNo)
                                                     []
                                                     k) ->
                 (rightExprOperationSeq : OperationSeq rightExpr
                                                      (S leftResultVarNo)
                                                      existingVarBindings
                                                      sexprList
                                                      rightExprOperations
                                                      (S rightResultVarNo)
                                                      []
                                                      k) ->
                 OperationSeq (MkArithGate leftExpr rightExpr MINUS)
                              startVarNo
                              existingVarBindings
                              sexprList
                              (leftExprOperations ++ rightExprOperations ++ ((Operation (S rightResultVarNo)
                                                                                       MINUS
                                                                                       (VarLeaf leftResultVarNo)
                                                                                       (VarLeaf rightResultVarNo))
                                                                                       :: []))
                              (S (S rightResultVarNo))
                              []
                              k


    -- Execute left, Execute right, then collect their results in 2 vars
    -- Finally do a PLUS of these 2 vars and then return the next available counter
    WriteMul : (startVarNo : Nat) ->
               (existingVarBindings : List (String, Nat)) ->
               (sexprList : SExprList) ->
               (leftExpr : SExpr) ->
               (rightExpr : SExpr) ->
               (leftExprOperationSeq : OperationSeq leftExpr
                                                    startVarNo
                                                    existingVarBindings
                                                    sexprList
                                                    leftExprOperations
                                                    (S leftResultVarNo)
                                                    []
                                                    k) ->
               (rightExprOperationSeq : OperationSeq rightExpr
                                                     (S leftResultVarNo)
                                                     existingVarBindings
                                                     sexprList
                                                     rightExprOperations
                                                     (S rightResultVarNo)
                                                     []
                                                     k) ->
               OperationSeq (MkArithGate leftExpr rightExpr MUL)
                            startVarNo
                            existingVarBindings
                            sexprList
                            (leftExprOperations ++ rightExprOperations ++ ((Operation (S rightResultVarNo)
                                                                                      MUL
                                                                                      (VarLeaf leftResultVarNo)
                                                                                      (VarLeaf rightResultVarNo))
                                                                                      :: []))
                            (S (S rightResultVarNo))
                            []
                            k

    -- let consists of a binding var + associated SExpr. and then a body SExpr
    -- first execute the binding SExpr, store the result in a Var, insert this result Var
    -- into the environment and then execute the body
    WriteLet : (startVarNo : Nat) ->
               (bindingVarName : String) ->
               (bindingExpr : SExpr) ->
               (letBody : SExpr) ->
               (sexprList : SExprList) ->
               (bindingExprWritten : OperationSeq bindingExpr
                                                  startVarNo
                                                  existingVarBindings
                                                  sexprList
                                                  bindingExprOperations
                                                  (S bindingExprResultVarNo)
                                                  []
                                                  k) ->
               (letBodyWritten : OperationSeq letBody
                                              (S bindingExprResultVarNo)
                                              ((bindingVarName, bindingExprResultVarNo) :: existingVarBindings)
                                              sexprList
                                              letBodyOperations
                                              (S letBodyResultVarNo)
                                              []
                                              k) ->
               (OperationSeq (MkLet bindingVarName bindingExpr letBody)
                             startVarNo
                             existingVarBindings
                             sexprList
                             (bindingExprOperations ++ letBodyOperations)
                             (S letBodyResultVarNo)
                             []
                             k)

    -- run is just an invocation so hand off to that guy
    WriteRun : (startVarNo : Nat) ->
               (runInvocation : SExpr) ->
               (sexprList : SExprList) ->
               (invocationWritten : OperationSeq runInvocation
                                                 startVarNo
                                                 existingVarBindings
                                                 sexprList
                                                 invocationOpSeq
                                                 (S invocationResultVarNo)
                                                 []
                                                 k) ->
               OperationSeq (MkRun runInvocation)
                            startVarNo
                            existingVarBindings
                            sexprList
                            invocationOpSeq
                            (S invocationResultVarNo)
                            []
                            k

    -- var is just a string - needs to be replaced with a var no where this var is
    -- stored. lookup here in bindings or later. empty bindings not allowed
    WriteVarHere : (startVarNo : Nat) ->
                   (varName : String) ->
                   (sexprList : SExprList) ->
                   (curBindingVarNo : Nat) ->
                   (remainingBindings : List (String, Nat)) ->
                   (OperationSeq (MkVar varName)
                                 startVarNo
                                 ((varName, curBindingVarNo) :: remainingBindings)
                                 sexprList
                                 ((Operation startVarNo ASGN (VarLeaf curBindingVarNo) NilLeaf) :: [])
                                 (S startVarNo)
                                 []
                                 k)

    WriteVarLater : (startVarNo : Nat) ->
                    (varName : String) ->
                    (sexprList : SExprList) ->
                    (curBindingVarName : String) ->
                    (curBindingVarNo : Nat) ->
                    (remainingBindings : List (String, Nat)) ->
                    (varWrittenLater : (OperationSeq (MkVar varName)
                                                     startVarNo
                                                     remainingBindings
                                                     sexprList
                                                     varWrittenOperations
                                                     (S varWrittenResultVarNo)
                                                     []
                                                     k)) ->
                    (OperationSeq (MkVar varName)
                                  startVarNo
                                  ((curBindingVarName, curBindingVarNo) :: remainingBindings)
                                  sexprList
                                  varWrittenOperations
                                  (S varWrittenResultVarNo)
                                  []
                                  k)

    WriteListSExpr : (startVarNo : Nat) ->
                     (existingVarBindings : List (String, Nat)) ->
                     (sexprList : SExprList) ->
                     (curArg : SExpr) ->
                     (remainingArgs : List SExpr) ->
                     (curArgWritten : OperationSeq curArg
                                                   startVarNo
                                                   existingVarBindings
                                                   sexprList
                                                   curArgWrittenOperations
                                                   (S curArgResultNo)
                                                   []
                                                   k) ->
                     (remainingWritten : OperationSeq (MkListSExpr remainingArgs)
                                                      (S curArgResultNo)
                                                      existingVarBindings
                                                      sexprList
                                                      remainingWrittenOperations
                                                      (S remainingWrittenResultVarNo)
                                                      remainingBindings
                                                      k) ->
                     (OperationSeq (MkListSExpr (curArg :: remainingArgs))
                                   startVarNo
                                   existingVarBindings
                                   sexprList
                                   (curArgWrittenOperations ++ remainingWrittenOperations)
                                   (S remainingWrittenResultVarNo)
                                   ([curArgResultNo] ++ remainingBindings)
                                   k)

    WriteListSExprEmpty : (startVarNo : Nat) ->
                          (existingVarBindings : List (String, Nat)) ->
                          (sexprList : SExprList) ->
                          OperationSeq (MkListSExpr [])
                                       startVarNo
                                       existingVarBindings
                                       sexprList
                                       []
                                       startVarNo
                                       []
                                       k

    WriteInvocation : (startVarNo : Nat) ->
                      (existingVarBindings : List (String, Nat)) ->
                      (sexprList : SExprList) ->
                      (fnName : String) ->
                      (invocationArgs : List SExpr) ->
                      (defArgs : List String) ->
                      (defBody : SExpr) ->
                      (invDefPrf : (ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody)
                                                                    sexprList)) ->
                      (invocationArgsWritten : OperationSeq (MkListSExpr invocationArgs)
                                                            startVarNo
                                                            existingVarBindings
                                                            sexprList
                                                            invocationArgsWrittenOperations
                                                            (S invocationArgsFinalResultVarNo)
                                                            constructedArgBindings
                                                            k) ->
                      (invocationBodyWritten : OperationSeq defBody
                                                            (S invocationArgsFinalResultVarNo)
                                                            (zip defArgs constructedArgBindings)
                                                            sexprList
                                                            invocationBodyWrittenOperations
                                                            (S invocationBodyResultVarNo)
                                                            []
                                                            k) ->
                      OperationSeq (MkInvocation fnName (MkListSExpr invocationArgs))
                                   startVarNo
                                   existingVarBindings
                                   sexprList
                                   (invocationArgsWrittenOperations ++ invocationBodyWrittenOperations)
                                   (S invocationBodyResultVarNo)
                                   []
                                   (S k)

    WriteEq : (startVarNo : Nat) ->
              (existingVarBindings : List (String, Nat)) ->
              (sexprList : SExprList) ->
              (leftExpr : SExpr) ->
              (rightExpr : SExpr) ->
              (leftWritten : (OperationSeq leftExpr
                                           startVarNo
                                           existingVarBindings
                                           sexprList
                                           leftWrittenOperations
                                           (S leftResultVarNo)
                                           []
                                           k)) ->
              (rightWritten : (OperationSeq rightExpr
                                            (S leftResultVarNo)
                                            existingVarBindings
                                            sexprList
                                            rightWrittenOperations
                                            (S rightResultVarNo)
                                            []
                                            k)) ->
              (OperationSeq (MkArithGate leftExpr
                                         rightExpr
                                         EQ)
                            startVarNo
                            existingVarBindings
                            sexprList
                            (leftWrittenOperations ++ rightWrittenOperations ++
                                                      [(Operation (S rightResultVarNo) -- this is x - y
                                                                  MINUS
                                                                  (VarLeaf leftResultVarNo)
                                                                  (VarLeaf rightResultVarNo)),
                                                       (Operation (S (S (S rightResultVarNo))) -- this is cond
                                                                  MUL
                                                                  (VarLeaf (S (S rightResultVarNo))) -- this is tmp
                                                                  (VarLeaf (S rightResultVarNo))     -- this is x-y
                                                                  ),
                                                       (Operation (S rightResultVarNo)
                                                                  MUL
                                                                  (VarLeaf (S (S (S rightResultVarNo)))) -- cond
                                                                  (VarLeaf (S rightResultVarNo)) -- this is x-y
                                                                  )])
                            (S (S (S (S rightResultVarNo))))
                            []
                            k)

    WriteCond : (startVarNo : Nat) ->
                (existingVarBindings : List (String, Nat)) ->
                (sexprList : SExprList) ->
                (ifExpr : SExpr) ->
                (thenExpr : SExpr) ->
                (elseExpr : SExpr) ->
                (ifExprWritten : (OperationSeq ifExpr
                                               startVarNo
                                               existingVarBindings
                                               sexprList
                                               ifExprWrittenOps
                                               (S ifWrittenResultVarNo)
                                               []
                                               k)) ->
                (thenExprWritten : (OperationSeq thenExpr
                                                 (S ifWrittenResultVarNo)
                                                 existingVarBindings
                                                 sexprList
                                                 thenExprWrittenOps
                                                 (S thenExprWrittenVarNo)
                                                 []
                                                 k)) ->
                (elseExprWritten : (OperationSeq elseExpr
                                                 (S thenExprWrittenVarNo)
                                                 existingVarBindings
                                                 sexprList
                                                 elseExprWrittenOps
                                                 (S elseExprWrittenVarNo)
                                                 []
                                                 k)) ->
                (OperationSeq (MkCond ifExpr thenExpr elseExpr)
                              startVarNo
                              existingVarBindings
                              sexprList
                              (ifExprWrittenOps ++
                                thenExprWrittenOps ++
                                elseExprWrittenOps ++
                                [
                                    (Operation (S elseExprWrittenVarNo)
                                               MUL
                                               (VarLeaf ifWrittenResultVarNo)
                                               (VarLeaf elseExprWrittenVarNo)),
                                    (Operation (S (S elseExprWrittenVarNo))
                                               MINUS
                                               (DigitLeaf 1)
                                               (VarLeaf (ifWrittenResultVarNo))),
                                    (Operation (S (S (S elseExprWrittenVarNo)))
                                               MUL
                                               (VarLeaf (S (S elseExprWrittenVarNo)))
                                               (VarLeaf thenExprWrittenVarNo))
                                ])
                              (S (S (S (S elseExprWrittenVarNo))))
                              []
                              k)




sexprToOperationSeq : (curVar : Nat) ->
                      (sexpr: SExpr) ->
                      (sexprList : SExprList) ->
                      (exprBindings : List (String, Nat)) ->
                      Dec (nextVarNo ** operationSeq ** producedBindings ** OperationSeq sexpr curVar exprBindings sexprList operationSeq nextVarNo producedBindings depth)
sexprToOperationSeq curVar (MkDigit x) sexprList exprBindings = Yes ((S curVar) **
                                                                         ((Operation curVar
                                                                                     DIGIT
                                                                                     (DigitLeaf x)
                                                                                     NilLeaf) :: []) **
                                                                         [] **
                                                                         (WriteDigit curVar
                                                                                     x
                                                                                     exprBindings
                                                                                     sexprList))
sexprToOperationSeq curVar (MkDef x xs y) sexprList exprBindings = ?rhsDef
sexprToOperationSeq curVar (MkLet varName varVal letBody) sexprList exprBindings {depth} = case (sexprToOperationSeq curVar varVal sexprList exprBindings {depth}) of
    (Yes ((S bindingExprResultVarNo) ** bindingExprOperations ** [] ** bindingExprPrf)) => case (sexprToOperationSeq (S bindingExprResultVarNo) letBody sexprList ((varName, bindingExprResultVarNo) :: exprBindings) {depth}) of
        (Yes ((S letBodyResultVarNo) ** letBodyOperations ** [] ** letBodyPrf)) => Yes ((S letBodyResultVarNo) **
                                                                                        (bindingExprOperations ++ letBodyOperations) **
                                                                                        [] **
                                                                                        (WriteLet curVar
                                                                                                  varName
                                                                                                  varVal
                                                                                                  letBody
                                                                                                  sexprList
                                                                                                  bindingExprPrf
                                                                                                  letBodyPrf))
        (No letBodyContra) => No ?rhs_3
    (No bindingExprContra) => No ?rhs_2
sexprToOperationSeq curVar (MkCond ifExpr thenExpr elseExpr) sexprList exprBindings {depth} = ?sexprToOperationSeq_rhs_5
sexprToOperationSeq curVar (MkVar x) sexprList [] {depth = depth} = No ?empty
sexprToOperationSeq curVar (MkVar x) sexprList ((headName, headVarNo) :: remainingBindings) {depth = depth} = case (decEq x headName) of
    (Yes Refl) => Yes ((S curVar) **
                       [(Operation curVar ASGN (VarLeaf headVarNo) NilLeaf)] **
                       [] **
                       (WriteVarHere curVar
                                     headName
                                     sexprList
                                     headVarNo
                                     remainingBindings))
    (No headVarContra) => case (sexprToOperationSeq curVar (MkVar x) sexprList remainingBindings {depth}) of
        (Yes ((S varWrittenResultVarNo) ** varWrittenOperations ** [] ** remainingPrf)) => Yes ((S varWrittenResultVarNo) **
                                                                                                varWrittenOperations **
                                                                                                [] **
                                                                                                (WriteVarLater curVar
                                                                                                               x
                                                                                                               sexprList
                                                                                                               headName
                                                                                                               headVarNo
                                                                                                               remainingBindings
                                                                                                               remainingPrf))
        (No remainingContra) => ?rhs_5
sexprToOperationSeq curVar (MkArithGate left right EQ) sexprList exprBindings  {depth = depth}= ?eq_rhs
sexprToOperationSeq curVar (MkArithGate left right PLUS) sexprList exprBindings  {depth = depth}= case (sexprToOperationSeq curVar left sexprList exprBindings {depth}) of
    (Yes ((S leftResultVarNo) ** leftExprOperations ** [] ** leftPrf)) => case (sexprToOperationSeq (S leftResultVarNo) right sexprList exprBindings {depth}) of
        (Yes ((S rightResultVarNo) ** rightExprOperations ** [] ** rightPrf)) => Yes ((S (S rightResultVarNo)) **
                                                                                      (leftExprOperations ++
                                                                                       rightExprOperations ++
                                                                                       [(Operation (S rightResultVarNo) PLUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))]) **
                                                                                      [] **
                                                                                      (WritePlus curVar
                                                                                                 exprBindings
                                                                                                 sexprList
                                                                                                 left
                                                                                                 right
                                                                                                 leftPrf
                                                                                                 rightPrf))
        (No contra) => ?rhs_6
    (No contra) => ?rhs_4
sexprToOperationSeq curVar (MkArithGate left right MUL) sexprList exprBindings  {depth = depth}= case (sexprToOperationSeq curVar left sexprList exprBindings {depth}) of
    (Yes ((S leftResultVarNo) ** leftExprOperations ** [] ** leftPrf)) => case (sexprToOperationSeq (S leftResultVarNo) right sexprList exprBindings {depth}) of
        (Yes ((S rightResultVarNo) ** rightExprOperations ** [] ** rightPrf)) => Yes ((S (S rightResultVarNo)) **
                                                                                      (leftExprOperations ++
                                                                                       rightExprOperations ++
                                                                                       [(Operation (S rightResultVarNo) MUL (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))]) **
                                                                                      [] **
                                                                                      (WriteMul  curVar
                                                                                                 exprBindings
                                                                                                 sexprList
                                                                                                 left
                                                                                                 right
                                                                                                 leftPrf
                                                                                                 rightPrf))
sexprToOperationSeq curVar (MkArithGate left right MINUS) sexprList exprBindings  {depth = depth}= case (sexprToOperationSeq curVar left sexprList exprBindings {depth}) of
    (Yes ((S leftResultVarNo) ** leftExprOperations ** [] ** leftPrf)) => case (sexprToOperationSeq (S leftResultVarNo) right sexprList exprBindings {depth}) of
        (Yes ((S rightResultVarNo) ** rightExprOperations ** [] ** rightPrf)) => Yes ((S (S rightResultVarNo)) **
                                                                                      (leftExprOperations ++
                                                                                       rightExprOperations ++
                                                                                       [(Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))]) **
                                                                                      [] **
                                                                                      (WriteMinus curVar
                                                                                                 exprBindings
                                                                                                 sexprList
                                                                                                 left
                                                                                                 right
                                                                                                 leftPrf
                                                                                                 rightPrf))
sexprToOperationSeq curVar (MkArithGate left right GT) sexprList exprBindings  {depth = depth}= ?sexprToOperationSeq_rhs_6
sexprToOperationSeq curVar (MkArithGate left right LT) sexprList exprBindings  {depth = depth}= ?sexprToOperationSeq_rhs_14
sexprToOperationSeq curVar (MkArithGate left right GTE) sexprList exprBindings  {depth = depth}= ?sexprToOperationSeq_rhs_15
sexprToOperationSeq curVar (MkArithGate left right LTE) sexprList exprBindings  {depth = depth}= ?sexprToOperationSeq_rhs_16
sexprToOperationSeq curVar (MkSTREQ left right) sexprList exprBindings {depth} = ?sexprToOperationSeq_rhs_8
sexprToOperationSeq curVar (MkConcat left right) sexprList exprBindings {depth} = ?sexprToOperationSeq_rhs_9
sexprToOperationSeq curVar (MkAppend item coll) sexprList exprBindings {depth} = ?sexprToOperationSeq_rhs_10
sexprToOperationSeq curVar (MkInvocation fnName (MkListSExpr args)) sexprList exprBindings {depth=(S depth)} = case (canExtractDefinitionForInvocation fnName args IsInvocation sexprList) of
    (Yes (defBody ** defArgs ** invDefPrf)) => case (sexprToOperationSeq curVar (MkListSExpr args) sexprList exprBindings {depth}) of
        (Yes ((S sexprListVarNo) ** sexprWritten ** producedBindings ** argsPrf)) => case (sexprToOperationSeq (S sexprListVarNo) defBody sexprList (zip defArgs producedBindings) {depth}) of
            (Yes ((S invocationResultVarNo) ** invocationBodyWritten ** [] ** bdPrf)) => Yes ((S invocationResultVarNo) **
                                                                                              (sexprWritten ++ invocationBodyWritten) **
                                                                                              [] **
                                                                                              (WriteInvocation curVar
                                                                                                               exprBindings
                                                                                                               sexprList
                                                                                                               fnName
                                                                                                               args
                                                                                                               defArgs
                                                                                                               defBody
                                                                                                               invDefPrf
                                                                                                               argsPrf
                                                                                                               bdPrf))
            (No contra) => ?rhs_12
        (No contra) => ?rhs_9
    (No contra) => ?rhs_8
sexprToOperationSeq curVar (MkRun invocation) sexprList exprBindings {depth} = case (sexprToOperationSeq curVar invocation sexprList exprBindings {depth}) of
    (Yes ((S invocationResultVarNo) ** invocationOpSeq ** [] ** invPrf)) => Yes ((S invocationResultVarNo) **
                                                                                 invocationOpSeq **
                                                                                 [] **
                                                                                 (WriteRun curVar
                                                                                           invocation
                                                                                           sexprList
                                                                                           invPrf))
    (No contra) => ?rhs_7
sexprToOperationSeq curVar (MkListSExpr []) sexprList exprBindings {depth = depth} = Yes (curVar **
                                                                                          [] **
                                                                                          [] **
                                                                                          (WriteListSExprEmpty curVar
                                                                                                               exprBindings
                                                                                                               sexprList))
sexprToOperationSeq curVar (MkListSExpr (headExpr :: remainingExprs)) sexprList exprBindings {depth = depth} = case (sexprToOperationSeq curVar headExpr sexprList exprBindings {depth}) of
    (Yes ((S headExprResultVarNo) ** headExprOpSeq ** [] ** headExprPrf)) => case (sexprToOperationSeq (S headExprResultVarNo) (MkListSExpr remainingExprs) sexprList exprBindings {depth}) of
        (Yes ((S remainingExprsResultVarNo) ** remainingOpSeq ** produced ** remainingPrf)) => Yes ((S remainingExprsResultVarNo) **
                                                                                                    (headExprOpSeq ++ remainingOpSeq) **
                                                                                                    ([headExprResultVarNo] ++ produced) **
                                                                                                    (WriteListSExpr curVar
                                                                                                                    exprBindings
                                                                                                                    sexprList
                                                                                                                    headExpr
                                                                                                                    remainingExprs
                                                                                                                    headExprPrf
                                                                                                                    remainingPrf))
        (No contra) => ?rhs_11
    (No contra) => No ?rhs_10
