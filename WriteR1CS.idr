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
data R1CSStatement : Type where
    Operation : Nat -> R1CSOperator -> DigitVarOrNil -> DigitVarOrNil -> R1CSStatement

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

data Zipped :  List a -> List b -> List (a, b) -> Type where
    ZipEnd : Zipped [] [] []
    Zip : (x:a) -> (y:b) -> (remaining:Zipped xs ys zs) -> Zipped (x::xs) (y::ys) ((x,y)::zs)

unequalLists : (x : b) -> (xs : List b) -> (zs : List (a, b) ** Zipped [] (x :: xs) zs) -> Void
unequalLists x xs (zs ** ZipEnd) impossible
unequalLists x xs (zs ** Zip _ _ _) impossible

unequalLists' : (x : a) -> (xs : List a) -> (zs : List (a, b) ** Zipped (x :: xs) [] zs) -> Void
unequalLists' x xs (zs ** ZipEnd) impossible
unequalLists' x xs (zs ** Zip _ _ _) impossible

restNotZippable : (x : a) -> (xs : List a) -> (y : b) -> (ys : List b) -> (zipContra : (zs : List (a, b) ** Zipped xs ys zs) -> Void) -> (zs : List (a, b) ** Zipped (x :: xs) (y :: ys) zs) -> Void
restNotZippable x xs y ys zipContra ([] ** ZipEnd) impossible
restNotZippable x xs y ys zipContra ([] ** Zip _ _ _) impossible
restNotZippable x xs y ys zipContra ((t :: zs) ** zipElem) =
    case (zipElem) of
        (Zip x y remaining) => zipContra (zs ** remaining)


getZip : (xs :List a) -> (ys:List b) -> Dec (zs:(List (a,b)) ** Zipped xs ys zs)
getZip [] [] = Yes ([] ** ZipEnd)
getZip [] (x :: xs) = No (unequalLists x xs)
getZip (x :: xs) [] = No (unequalLists' x xs)
getZip (x :: xs) (y :: ys) with (getZip xs ys)
    | (Yes (zs ** zipped)) = Yes (((x,y)::zs) ** (Zip x y zipped))
    | (No zipContra) = No (restNotZippable x xs y ys zipContra)


isZipped_rhs_1 : Zipped [] [] (x :: xs) -> Void
isZipped_rhs_1 ZipEnd impossible
isZipped_rhs_1 (Zip _ _ _) impossible

isZipped_rhs_2 : Zipped [] (x :: xs) zs -> Void
isZipped_rhs_2 ZipEnd impossible
isZipped_rhs_2 (Zip _ _ _) impossible

isZipped_rhs_3 : Zipped (x :: xs) [] zs -> Void
isZipped_rhs_3 ZipEnd impossible
isZipped_rhs_3 (Zip _ _ _) impossible

isZipped_rhs_4 : Zipped (x :: xs) (y :: ys) [] -> Void
isZipped_rhs_4 ZipEnd impossible
isZipped_rhs_4 (Zip _ _ _) impossible

isZipped : (DecEq a, DecEq b) => (xs :List a) -> (ys:List b) -> (zs:List (a,b)) -> Dec (Zipped xs ys zs)
isZipped [] [] [] = Yes ZipEnd
isZipped [] [] (x :: xs) = No isZipped_rhs_1
isZipped [] (x :: xs) zs = No isZipped_rhs_2
isZipped (x :: xs) [] zs = No isZipped_rhs_3
isZipped (x :: xs) (y :: ys) [] = No isZipped_rhs_4
isZipped (x :: xs) (y :: ys) (z :: zs) with (isZipped xs ys zs)
    | (Yes remaining) with(decEq z (x,y))
        | (Yes eq) = Yes (rewrite eq in Zip x y remaining)
        | (No zNOTxy) = No  (\(Zip x y rem) => zNOTxy Refl)
    | (No remainingContra) = No (\(Zip x y remaining) => remainingContra remaining)


mutual
    data OperationSeq : (expression : SExpr) ->
                        (startVarNo : Nat) ->
                        (varBindings : List (String, Nat)) ->
                        (sexprList : SExprList) ->
                        (List R1CSStatement) ->
                        (nextVarNo : Nat) ->
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
                                  k  -- no expansion so no change in depth

        -- Execute left, Execute right, then collect their results in 2 vars
        -- Finally do a PLUS of these 2 vars and then return the next available counter
        WritePlus : (startVarNo : Nat) ->
                    (existingVarBindings : List (String, Nat)) ->
                    (sexprList : SExprList) ->
                    (leftExpr : SExpr) ->
                    (rightExpr : SExpr) ->                           {--)=>--}
                    (leftExprOperationSeq : OperationSeq leftExpr
                                                         startVarNo
                                                         existingVarBindings
                                                         sexprList
                                                         leftExprOperations
                                                         (S leftResultVarNo)
                                                         k) ->
                    (rightExprOperationSeq : OperationSeq rightExpr
                                                          (S leftResultVarNo)
                                                          existingVarBindings
                                                          sexprList
                                                          rightExprOperations
                                                          (S rightResultVarNo)
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
                                 k

        -- Execute left, Execute right, then collect their results in 2 vars
        -- Finally do a PLUS of these 2 vars and then return the next available counter
        WriteMinus : (startVarNo : Nat) ->
                     (existingVarBindings : List (String, Nat)) ->
                     (sexprList : SExprList) ->
                     (leftExpr : SExpr) ->
                     (rightExpr : SExpr) ->                           {--)=>--}
                     (leftExprOperationSeq : OperationSeq leftExpr
                                                         startVarNo
                                                         existingVarBindings
                                                         sexprList
                                                         leftExprOperations
                                                         (S leftResultVarNo)
                                                         k) ->
                     (rightExprOperationSeq : OperationSeq rightExpr
                                                          (S leftResultVarNo)
                                                          existingVarBindings
                                                          sexprList
                                                          rightExprOperations
                                                          (S rightResultVarNo)
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
                                  k


        -- Execute left, Execute right, then collect their results in 2 vars
        -- Finally do a PLUS of these 2 vars and then return the next available counter
        WriteMul : (startVarNo : Nat) ->
                   (existingVarBindings : List (String, Nat)) ->
                   (sexprList : SExprList) ->
                   (leftExpr : SExpr) ->
                   (rightExpr : SExpr) ->                           {--)=>--}
                   (leftExprOperationSeq : OperationSeq leftExpr
                                                        startVarNo
                                                        existingVarBindings
                                                        sexprList
                                                        leftExprOperations
                                                        (S leftResultVarNo)
                                                        k) ->
                   (rightExprOperationSeq : OperationSeq rightExpr
                                                         (S leftResultVarNo)
                                                         existingVarBindings
                                                         sexprList
                                                         rightExprOperations
                                                         (S rightResultVarNo)
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
                                k

        -- let consists of a binding var + associated SExpr. and then a body SExpr
        -- first execute the binding SExpr, store the result in a Var, insert this result Var
        -- into the environment and then execute the body
        WriteLet : (startVarNo : Nat) ->
                   (bindingVarName : String) ->
                   (bindingExpr : SExpr) ->
                   (letBody : SExpr) ->
                   (sexprList : SExprList) ->                           {--)=>--}
                   (bindingExprWritten : OperationSeq bindingExpr
                                                      startVarNo
                                                      existingVarBindings
                                                      sexprList
                                                      bindingExprOperations
                                                      (S bindingExprResultVarNo)
                                                      k) ->
                   (letBodyWritten : OperationSeq letBody
                                                  (S bindingExprResultVarNo)
                                                  ((bindingVarName, bindingExprResultVarNo) :: existingVarBindings)
                                                  sexprList
                                                  letBodyOperations
                                                  (S letBodyResultVarNo)
                                                  k) ->
                   (OperationSeq (MkLet bindingVarName bindingExpr letBody)
                                 startVarNo
                                 existingVarBindings
                                 sexprList
                                 (bindingExprOperations ++ letBodyOperations)
                                 (S letBodyResultVarNo)
                                 k)

        -- run is just an invocation so hand off to that guy
        WriteRun : (startVarNo : Nat) ->
                   (runInvocation : SExpr) ->
                   (sexprList : SExprList) ->                           {--)=>--}
                   (invocationWritten : OperationSeq runInvocation
                                                     startVarNo
                                                     existingVarBindings
                                                     sexprList
                                                     invocationOpSeq
                                                     (S invocationResultVarNo)
                                                     k) ->
                   OperationSeq (MkRun runInvocation)
                                startVarNo
                                existingVarBindings
                                sexprList
                                invocationOpSeq
                                (S invocationResultVarNo)
                                k

        WriteVar : (startVarNo : Nat) ->
                   (varName : String) ->
                   (sexprList : SExprList) ->
                   (exprBindings : List (String, Nat)) ->
                   (varInBindings : VarInBindings varName bindingVarNo exprBindings) ->
                   (OperationSeq (MkVar varName)
                                 startVarNo
                                 exprBindings
                                 sexprList
                                 ((Operation startVarNo ASGN (VarLeaf bindingVarNo) NilLeaf) :: [])
                                 (S startVarNo)
                                 k)

        WriteInvocation : (startVarNo : Nat) ->
                          (existingVarBindings : List (String, Nat)) ->
                          (sexprList : SExprList) ->
                          (fnName : String) ->
                          (invocationArgs : List SExpr) ->
                          (defArgs : List String) ->
                          (defBody : SExpr) ->                           {--)=>--}
                          (invDefPrf : (ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody)
                                                                        sexprList)) ->
                          (invocationArgsWritten : OperationSeqFormList (MkFormList invocationArgs)
                                                                        startVarNo
                                                                        existingVarBindings
                                                                        sexprList
                                                                        invocationArgsWrittenOperations
                                                                        (S invocationArgsFinalResultVarNo)
                                                                        constructedArgBindings
                                                                        k) ->
                          (invocationBodyWritten : OperationSeq defBody
                                                                (S invocationArgsFinalResultVarNo)
                                                                zippedList
                                                                sexprList
                                                                invocationBodyWrittenOperations
                                                                (S invocationBodyResultVarNo)
                                                                k) ->
                          (isZippedList : Zipped defArgs constructedArgBindings zippedList ) ->
                          OperationSeq (MkInvocation fnName (MkFormList invocationArgs))
                                       startVarNo
                                       existingVarBindings
                                       sexprList
                                       (invocationArgsWrittenOperations ++ invocationBodyWrittenOperations)
                                       (S invocationBodyResultVarNo)
                                       (S k)

        WriteEq : (startVarNo : Nat) ->
                  (existingVarBindings : List (String, Nat)) ->
                  (sexprList : SExprList) ->
                  (leftExpr : SExpr) ->                           {--)=>--}
                  (rightExpr : SExpr) ->                           {--)=>--}
                  (leftWritten : (OperationSeq leftExpr
                                               startVarNo
                                               existingVarBindings
                                               sexprList
                                               leftWrittenOperations
                                               (S leftResultVarNo)
                                               k)) ->                           {--)=>--}
                  (rightWritten : (OperationSeq rightExpr
                                                (S leftResultVarNo)
                                                existingVarBindings
                                                sexprList
                                                rightWrittenOperations
                                                (S rightResultVarNo)
                                                k)) ->                           {--)=>--}
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
                                k)

        WriteCond : (startVarNo : Nat) ->
                    (existingVarBindings : List (String, Nat)) ->
                    (sexprList : SExprList) ->
                    (ifExpr : SExpr) ->
                    (thenExpr : SExpr) ->
                    (elseExpr : SExpr) ->                           {--)=>--}
                    (ifExprWritten : (OperationSeq ifExpr
                                                   startVarNo
                                                   existingVarBindings
                                                   sexprList
                                                   ifExprWrittenOps
                                                   (S ifWrittenResultVarNo)
                                                   k)) ->                           {--)=>--}
                    (thenExprWritten : (OperationSeq thenExpr
                                                     (S ifWrittenResultVarNo)
                                                     existingVarBindings
                                                     sexprList
                                                     thenExprWrittenOps
                                                     (S thenExprWrittenVarNo)
                                                     k)) ->                           {--)=>--}
                    (elseExprWritten : (OperationSeq elseExpr
                                                     (S thenExprWrittenVarNo)
                                                     existingVarBindings
                                                     sexprList
                                                     elseExprWrittenOps
                                                     (S elseExprWrittenVarNo)
                                                     k)) ->               {--)=>--}
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
                                  k)

    data OperationSeqFormList : (formlist : FormList) ->
                                (startVarNo : Nat) ->
                                (existingVarBindings : List (String, Nat)) ->
                                (sexprList : SExprList) ->
                                (operations : List R1CSStatement) ->
                                (endVarNo : Nat) ->
                                (producedBindings : List Nat) ->
                                (depth : Nat) -> Type where
        WriteFormList : (startVarNo : Nat) ->
                        (existingVarBindings : List (String, Nat)) ->
                        (sexprList : SExprList) ->
                        (curArg : SExpr) ->
                        (remainingArgs : List SExpr) ->                           {--)=>--}
                        (curArgWritten : OperationSeq curArg
                                                      startVarNo
                                                      existingVarBindings
                                                      sexprList
                                                      curArgWrittenOperations
                                                      (S curArgResultNo)
                                                      k) ->
                         (remainingWritten : OperationSeqFormList
                                                (MkFormList remainingArgs)
                                                (S curArgResultNo)
                                                existingVarBindings
                                                sexprList
                                                remainingWrittenOperations
                                                (S remainingWrittenResultVarNo)
                                                remainingBindings
                                                k) ->
                        (operations = curArgWrittenOperations ++ remainingWrittenOperations)->
                     (OperationSeqFormList
                        (MkFormList (curArg :: remainingArgs))
                        startVarNo
                        existingVarBindings
                        sexprList
                        operations
                        (S remainingWrittenResultVarNo)
                        ([curArgResultNo] ++ remainingBindings)
                        k)

        WriteFormListEmpty : (startVarNo : Nat) ->
                              (existingVarBindings : List (String, Nat)) ->
                              (sexprList : SExprList) ->
                              (OperationSeqFormList
                                (MkFormList [])
                                startVarNo
                                existingVarBindings
                                sexprList
                                []
                                startVarNo
                                []
                                k)


{--)=>--}
data SExprToOperatorReturnType : (curVar : Nat) -> (sexpr: SExpr) -> (sexprList : SExprList) -> (exprBindings : List (String, Nat)) -> (depth:Nat) -> Type where
  RetVal : (curVar : Nat) ->
           (sexpr: SExpr) ->
           (sexprList : SExprList) ->
           (exprBindings : List (String, Nat)) ->
           (nextVarNo : Nat) ->
           (prfLTE1:LT Z nextVarNo) ->
           (operationSeq : List R1CSStatement) ->
           (depth:Nat) ->
           (opSeqType : OperationSeq sexpr
                                     curVar
                                     exprBindings
                                     sexprList
                                     operationSeq
                                     nextVarNo
                                     depth) ->
           SExprToOperatorReturnType curVar sexpr sexprList exprBindings depth

--
--)=>
