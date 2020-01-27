module WriteR1CSRoutines

import Data.List
import Examples.SExpr
import Examples.EnvironmentVF
import Examples.WriteR1CS
import Examples.R1CSHelper

%access export
%default partial
%access public export



failedWriteLetBody : (x : LTE 0 bindingExprResultVarNo) ->
                     (letBodyContra : SExprToOperatorReturnType (S bindingExprResultVarNo) letBody sexprList ((bindingVarName, bindingExprResultVarNo) :: exprBindings) depth -> Void) ->
                     (bindingExprWritten : OperationSeq bindingVarVal curVarNo exprBindings sexprList bindingValOps (S bindingExprResultVarNo) depth) ->
                     SExprToOperatorReturnType curVarNo (MkLet bindingVarName bindingVarVal letBody) sexprList exprBindings depth ->
                     Void
failedWriteLetBody x letBodyContra bindingExprWritten (RetVal curVarNo
                                                              (MkLet bindingVarName bindingVarVal letBody)
                                                              sexprList
                                                              exprBindings
                                                              (S letBodyResultVarNo)
                                                              prfLTE1
                                                              (bindingExprOperations ++ letBodyOperations)
                                                              depth
                                                              (WriteLet curVarNo bindingVarName bindingVarVal letBody sexprList y letBodyWritten {bindingExprResultVarNo})) =
    let Refl = sameSExprSameR1CS y bindingExprWritten
        retVal = RetVal (S bindingExprResultVarNo) letBody sexprList ((bindingVarName, bindingExprResultVarNo) :: exprBindings) (S letBodyResultVarNo) (LTESucc LTEZero) letBodyOperations depth letBodyWritten
    in
    letBodyContra (retVal)


varNotInBindings : (varInBindingsContra : (bindingVarNo : Nat ** VarInBindings x bindingVarNo exprBindings) -> Void) -> SExprToOperatorReturnType curVarNo (MkVar x) sexprList exprBindings depth -> Void
varNotInBindings varInBindingsContra (RetVal curVarNo (MkVar x) sexprList exprBindings (S curVarNo) prfLTE1 ([Operation curVarNo ASGN (VarLeaf bindingVarNo) NilLeaf]) depth (WriteVar curVarNo x sexprList exprBindings varInBindings)) = varInBindingsContra (bindingVarNo ** varInBindings)

getFinalVarNo : OperationSeq bindingVarVal curVarNo exprBindings sexprList bindingExprOperations (S bindingExprResultVarNo) depth -> Nat
getFinalVarNo x {bindingExprResultVarNo} = (S bindingExprResultVarNo)

failedWriteBindingVal : (bindingVarValContra : SExprToOperatorReturnType curVarNo bindingVarVal sexprList exprBindings depth -> Void) -> SExprToOperatorReturnType curVarNo (MkLet bindingVarName bindingVarVal letBody) sexprList exprBindings depth -> Void
failedWriteBindingVal bindingVarValContra
                     (RetVal curVarNo
                             (MkLet bindingVarName
                                    bindingVarVal
                                    letBody)
                      sexprList
                      exprBindings
                      (S letBodyResultVarNo)
                      prfLTE1
                      (bindingExprOperations ++ letBodyOperations)
                      depth
                      (WriteLet curVarNo bindingVarName bindingVarVal letBody sexprList bindingExprWritten letBodyWritten)) =
                          bindingVarValContra (RetVal
                                                curVarNo
                                                bindingVarVal
                                                sexprList
                                                exprBindings
                                                (getFinalVarNo bindingExprWritten)
                                                (LTESucc LTEZero)
                                                bindingExprOperations
                                                depth
                                                bindingExprWritten)


failedWriteIfExpression : (ifExprContra : SExprToOperatorReturnType curVarNo ifExpr sexprList exprBindings depth -> Void) -> SExprToOperatorReturnType curVarNo (MkCond ifExpr thenExpr elseExpr) sexprList exprBindings depth -> Void
failedWriteIfExpression ifExprContra
                        (RetVal
                            curVarNo
                            (MkCond ifExpr thenExpr elseExpr)
                                sexprList
                                exprBindings
                                (S (S (S (S elseExprWrittenVarNo))))
                                prfLTE1
                                (ifExprWrittenOps ++
                                  thenExprWrittenOps ++
                                  elseExprWrittenOps ++
                                  [Operation (S elseExprWrittenVarNo)
                                             MUL
                                             (VarLeaf ifWrittenResultVarNo)
                                             (VarLeaf elseExprWrittenVarNo),
                                   Operation (S (S elseExprWrittenVarNo))
                                             MINUS
                                             (DigitLeaf 1)
                                             (VarLeaf ifWrittenResultVarNo),
                                   Operation (S (S (S elseExprWrittenVarNo)))
                                             MUL
                                             (VarLeaf (S (S elseExprWrittenVarNo)))
                                             (VarLeaf thenExprWrittenVarNo)])
                                depth
                                (WriteCond curVarNo exprBindings sexprList ifExpr thenExpr elseExpr ifExprWritten thenExprWritten elseExprWritten)) =
    ifExprContra (RetVal curVarNo ifExpr sexprList exprBindings (getFinalVarNo ifExprWritten) (LTESucc LTEZero) ifExprWrittenOps depth ifExprWritten)



failedWriteThenExpression : (prfLTE1IF : LT 0 (S varNoAfterIF)) ->
                            (thenExprContra : SExprToOperatorReturnType (S varNoAfterIF) thenExpr sexprList exprBindings depth -> Void) ->
                            (opSeqTypeIF : OperationSeq ifExpr curVarNo exprBindings sexprList ifExprWrittenOps (S varNoAfterIF) depth) ->
                            SExprToOperatorReturnType curVarNo (MkCond ifExpr thenExpr elseExpr) sexprList exprBindings depth -> Void
failedWriteThenExpression prfLTE1IF thenExprContra opSeqTypeIF (RetVal
                                                                    curVarNo
                                                                    (MkCond ifExpr thenExpr elseExpr)
                                                                    sexprList
                                                                    exprBindings
                                                                    (S (S (S (S elseExprWrittenVarNo))))
                                                                    prfLTE1
                                                                    (ifExprWrittenOps ++
                                                                    thenExprWrittenOps ++
                                                                    elseExprWrittenOps ++
                                                                    [Operation (S elseExprWrittenVarNo)
                                                                               MUL
                                                                               (VarLeaf ifWrittenResultVarNo)
                                                                               (VarLeaf elseExprWrittenVarNo),
                                                                     Operation (S (S elseExprWrittenVarNo))
                                                                               MINUS
                                                                               (DigitLeaf 1)
                                                                               (VarLeaf ifWrittenResultVarNo),
                                                                     Operation (S (S (S elseExprWrittenVarNo)))
                                                                               MUL
                                                                               (VarLeaf (S (S elseExprWrittenVarNo)))
                                                                               (VarLeaf thenExprWrittenVarNo)])
                                                                    depth
                                                                    (WriteCond curVarNo exprBindings sexprList ifExpr thenExpr elseExpr ifExprWritten thenExprWritten elseExprWritten)) =
    let Refl = sameSExprSameR1CS ifExprWritten opSeqTypeIF
    in
    thenExprContra (RetVal
                        (S ifWrittenResultVarNo)
                        thenExpr
                        sexprList
                        exprBindings
                        (S thenExprWrittenVarNo)
                        (LTESucc LTEZero)
                        thenExprWrittenOps
                        depth
                        thenExprWritten)


failedWriteElseExpression : (prfLTE1THEN : LT 0 (S varNoAfterTHEN)) ->
                            (elseContra : SExprToOperatorReturnType (S varNoAfterTHEN) elseExpr sexprList exprBindings depth -> Void) ->
                            (opSeqTypeIF : OperationSeq ifExpr curVarNo exprBindings sexprList ifExprWrittenOps (S varNoAfterIF) depth) ->
                            (opSeqTypeTHEN : OperationSeq thenExpr (S varNoAfterIF) exprBindings sexprList thenExprWrittenOps (S varNoAfterTHEN) depth) ->
                            (prfLTE1IF : LT 0 (S varNoAfterIF)) ->
                            SExprToOperatorReturnType curVarNo (MkCond ifExpr thenExpr elseExpr) sexprList exprBindings depth -> Void
failedWriteElseExpression prfLTE1THEN
                          elseContra
                          opSeqTypeIF
                          opSeqTypeTHEN
                          prfLTE1IF
                          (RetVal
                                curVarNo
                                (MkCond ifExpr thenExpr elseExpr)
                                sexprList
                                exprBindings
                                (S (S (S (S elseExprWrittenVarNo))))
                                prfLTE1
                                (ifExprWrittenOps ++
                                thenExprWrittenOps ++
                                elseExprWrittenOps ++
                                [Operation (S elseExprWrittenVarNo)
                                           MUL
                                           (VarLeaf ifWrittenResultVarNo)
                                           (VarLeaf elseExprWrittenVarNo),
                                 Operation (S (S elseExprWrittenVarNo))
                                           MINUS
                                           (DigitLeaf 1)
                                           (VarLeaf ifWrittenResultVarNo),
                                 Operation (S (S (S elseExprWrittenVarNo)))
                                           MUL
                                           (VarLeaf (S (S elseExprWrittenVarNo)))
                                           (VarLeaf thenExprWrittenVarNo)])
                                depth
                                (WriteCond curVarNo exprBindings sexprList ifExpr thenExpr elseExpr ifExprWritten thenExprWritten elseExprWritten)) =
    let Refl = sameSExprSameR1CS ifExprWritten opSeqTypeIF
    in
    let thenExprWrittenVarNoEQvarNoAfterTHEN = sameSExprSameR1CS thenExprWritten opSeqTypeTHEN
        retVal = (RetVal
                        (S thenExprWrittenVarNo)
                        elseExpr
                        sexprList
                        exprBindings
                        (S elseExprWrittenVarNo)
                        (LTESucc LTEZero)
                        elseExprWrittenOps
                        depth
                        elseExprWritten)
    in
    elseContra  (rewrite sym thenExprWrittenVarNoEQvarNoAfterTHEN in retVal)



impossibleToContinueWithoutArgs : (extractedDef : ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody) sexprList) -> (invDefPrf : (defBody1 : SExpr ** defArgs1 : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs1 defBody1) sexprList)) -> (argsToOpSeqFormFailed : (operations : List R1CSStatement ** endVarNo : Nat ** producedBindings : List Nat ** OperationSeqFormList (MkFormList invocationArgs) curVarNo exprBindings sexprList operations endVarNo producedBindings preDepth) -> Void) -> SExprToOperatorReturnType curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings (S preDepth) -> Void
impossibleToContinueWithoutArgs extractedDef invDefPrf argsToOpSeqFormFailed
    (RetVal curVarNo
            (MkInvocation fnName
                          (MkFormList invocationArgs))
                          sexprList
                          exprBindings
                          (S invocationBodyResultVarNo)
                          prfLTE1
                          (invocationArgsWrittenOperations ++ invocationBodyWrittenOperations)
                          (S preDepth)
                          (WriteInvocation curVarNo
                                           exprBindings
                                           sexprList
                                           fnName
                                           invocationArgs
                                           defArgs
                                           defBody
                                           invDefPrf'
                                           invocationArgsWritten
                                           invocationBodyWritten
                                           isZippedList)) =
    argsToOpSeqFormFailed (invocationArgsWrittenOperations **
                           getEndVarFromOperationSeqFormList invocationArgsWritten **
                           getBindingsFromOperationSeqFormList invocationArgsWritten **
                           invocationArgsWritten)




bodyCannotBeWritten : (extractedDef : ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody) sexprList) ->
                      (bodyToOpSeqFailed : SExprToOperatorReturnType (S invocationArgsFinalResultVarNo) defBody sexprList zipped preDepth -> Void) ->
                      (zippedPrf : Zipped defArgs constructedArgBindings zipped) ->
                      (invocationArgsWritten : OperationSeqFormList (MkFormList invocationArgs) curVarNo exprBindings sexprList invocationArgsWrittenOperations (S invocationArgsFinalResultVarNo) constructedArgBindings preDepth) ->
                      SExprToOperatorReturnType curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings (S preDepth) -> Void
bodyCannotBeWritten extractedDef
                    bodyToOpSeqFailed
                    zippedPrf
                    invocationArgsWritten'
                    (RetVal curVarNo
                            (MkInvocation fnName (MkFormList invocationArgs))
                            sexprList
                            exprBindings
                            _
                            prfLTE1
                            _
                            (S preDepth)
                            (WriteInvocation curVarNo
                                             exprBindings
                                             sexprList
                                             fnName
                                             invocationArgs
                                             defArgs
                                             defBody
                                             invDefPrf
                                             invocationArgsWritten
                                             invocationBodyWritten
                                             isZippedList)) {invocationArgsFinalResultVarNo} {zipped}
    with (sameDefBody extractedDef invDefPrf)
        | (eq1, Refl, Refl) with (sameFormListSameOpseqFormList invocationArgsWritten' invocationArgsWritten)
            | (eq2, Refl, Refl) with (zippingUnique isZippedList zippedPrf )
                | (Refl, eq4) = case (eq2, eq4) of
                    (Refl, Refl) => let retVal = RetVal (S invocationArgsFinalResultVarNo)
                                                        defBody
                                                        sexprList
                                                        zipped
                                                        _
                                                        (LTESucc LTEZero)
                                                        _
                                                        preDepth
                                                        invocationBodyWritten
                        in bodyToOpSeqFailed retVal



impossibleToContinueWithoutFctDef : (definitionsForInvocationNotFound : (defBody : SExpr ** defArgs : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody) sexprList) -> Void) -> SExprToOperatorReturnType curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings (S preDepth) -> Void
impossibleToContinueWithoutFctDef definitionsForInvocationNotFound
                                  (RetVal curVarNo
                                          (MkInvocation fnName (MkFormList invocationArgs))
                                          sexprList
                                          exprBindings
                                          (S invocationBodyResultVarNo)
                                          prfLTE1
                                          (invocationArgsWrittenOperations ++ invocationBodyWrittenOperations)
                                          (S preDepth)
                                          (WriteInvocation curVarNo
                                                           exprBindings
                                                           sexprList
                                                           fnName
                                                           invocationArgs
                                                           defArgs
                                                           defBody
                                                           invDefPrf
                                                           invocationArgsWritten
                                                           invocationBodyWritten
                                                           isZippedList)) =
    definitionsForInvocationNotFound (defBody ** defArgs ** invDefPrf)


finalDepthReached : SExprToOperatorReturnType curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings 0 -> Void
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteDigit _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WritePlus _ _ _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteMinus _ _ _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteMul _ _ _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteLet _ _ _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteRun _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteVar _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteInvocation _ _ _ _ _ _ _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteEq _ _ _ _ _ _ _)) impossible
finalDepthReached (RetVal _ (MkInvocation _ (MkFormList _)) _ _ _ _ _ Z (WriteCond _ _ _ _ _ _ _ _ _)) impossible

cannotContinueWithoutZipping : (extractedDef : ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody) sexprList) ->
                               (invDefPrf : (defBody1 : SExpr ** defArgs1 : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs1 defBody1) sexprList)) ->
                               (notZippable : (zs : List (String, Nat) ** Zipped defArgs constructedArgBindings zs) -> Void) ->
                               (invocationArgsWritten : OperationSeqFormList (MkFormList invocationArgs) curVarNo exprBindings sexprList invocationArgsWrittenOperations (S invocationArgsFinalResultVarNo) constructedArgBindings preDepth) ->
                               SExprToOperatorReturnType curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings (S preDepth) -> Void
cannotContinueWithoutZipping extractedDef
                             invDefPrf'
                             notZippable
                             invocationArgsWritten'
                             (RetVal curVarNo
                                     (MkInvocation fnName (MkFormList invocationArgs))
                                     sexprList
                                     exprBindings
                                     _
                                     prfLTE1
                                     _
                                     (S preDepth)
                                     (WriteInvocation curVarNo
                                                      exprBindings
                                                      sexprList
                                                      fnName
                                                      invocationArgs
                                                      defArgs
                                                      defBody
                                                      invDefPrf
                                                      invocationArgsWritten
                                                      invocationBodyWritten
                                                      isZippedList {zippedList}))  with (sameDefBody extractedDef invDefPrf)
    | (eq1, Refl, Refl) with (sameFormListSameOpseqFormList invocationArgsWritten' invocationArgsWritten)
                 | (eq2, Refl, Refl) = notZippable (zippedList ** isZippedList)



rightExprFailed : (leftPrfLTE1 : LT 0 (S leftResultVarNo)) -> (rightContra : SExprToOperatorReturnType (S leftResultVarNo) right sexprList exprBindings depth -> Void) -> (leftOpSeqType : OperationSeq left curVarNo exprBindings sexprList leftOperationSeq (S leftResultVarNo) depth) -> SExprToOperatorReturnType curVarNo (MkArithGate left right operator) sexprList exprBindings depth -> Void
rightExprFailed leftPrfLTE1 rightContra leftOpSeqType (RetVal curVarNo (MkArithGate left right PLUS) sexprList exprBindings (S (S rightResultVarNo)) prfLTE1 (leftExprOperations ++ (rightExprOperations ++ [Operation (S rightResultVarNo) PLUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo)])) depth (WritePlus curVarNo exprBindings sexprList left right leftExprOperationSeq rightExprOperationSeq)) =
    let leftWrittenSame = sameSExprSameR1CS leftOpSeqType leftExprOperationSeq
        retVal = (RetVal
                    (S leftResultVarNo)
                    right
                    sexprList
                    exprBindings
                    (S rightResultVarNo)
                    (LTESucc LTEZero)
                    rightExprOperations
                    depth
                    rightExprOperationSeq) in
        rightContra (rewrite leftWrittenSame in retVal)
rightExprFailed leftPrfLTE1 rightContra leftOpSeqType (RetVal curVarNo (MkArithGate left right MINUS) sexprList exprBindings (S (S rightResultVarNo)) prfLTE1 (leftExprOperations ++ (rightExprOperations ++ [Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo)])) depth (WriteMinus curVarNo exprBindings sexprList left right leftExprOperationSeq rightExprOperationSeq)) =
    let leftWrittenSame = sameSExprSameR1CS leftOpSeqType leftExprOperationSeq
        retVal = (RetVal
                    (S leftResultVarNo)
                    right
                    sexprList
                    exprBindings
                    (S rightResultVarNo)
                    (LTESucc LTEZero)
                    rightExprOperations
                    depth
                    rightExprOperationSeq) in
        rightContra (rewrite leftWrittenSame in retVal)
rightExprFailed leftPrfLTE1 rightContra leftOpSeqType (RetVal curVarNo (MkArithGate left right MUL) sexprList exprBindings (S (S rightResultVarNo)) prfLTE1 (leftExprOperations ++ (rightExprOperations ++ [Operation (S rightResultVarNo) MUL (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo)])) depth (WriteMul curVarNo exprBindings sexprList left right leftExprOperationSeq rightExprOperationSeq)) =
    let leftWrittenSame = sameSExprSameR1CS leftOpSeqType leftExprOperationSeq
        retVal = (RetVal
                    (S leftResultVarNo)
                    right
                    sexprList
                    exprBindings
                    (S rightResultVarNo)
                    (LTESucc LTEZero)
                    rightExprOperations
                    depth
                    rightExprOperationSeq) in
        rightContra (rewrite leftWrittenSame in retVal)
rightExprFailed leftPrfLTE1 rightContra leftOpSeqType (RetVal curVarNo (MkArithGate left right EQ) sexprList exprBindings (S (S (S (S rightResultVarNo)))) prfLTE1 (leftWrittenOperations ++ (rightWrittenOperations ++ [Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo), Operation (S (S (S rightResultVarNo))) MUL (VarLeaf (S (S rightResultVarNo))) (VarLeaf (S rightResultVarNo)), Operation (S rightResultVarNo) MUL (VarLeaf (S (S (S rightResultVarNo)))) (VarLeaf (S rightResultVarNo))])) depth (WriteEq curVarNo exprBindings sexprList left right leftWritten rightWritten)) =
    let leftWrittenSame = sameSExprSameR1CS leftOpSeqType leftWritten
        retVal = (RetVal
                    (S leftResultVarNo)
                    right
                    sexprList
                    exprBindings
                    (S rightResultVarNo)
                    (LTESucc LTEZero)
                    rightWrittenOperations
                    depth
                    rightWritten) in
        rightContra (rewrite leftWrittenSame in retVal)


leftExprFailed : (leftContra : SExprToOperatorReturnType curVarNo left sexprList exprBindings depth -> Void) -> SExprToOperatorReturnType curVarNo (MkArithGate left right operator) sexprList exprBindings depth -> Void
leftExprFailed leftContra (RetVal curVarNo (MkArithGate left right PLUS) sexprList exprBindings (S (S rightResultVarNo)) prfLTE1 (leftExprOperations ++ (rightExprOperations ++ [Operation (S rightResultVarNo) PLUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo)])) depth (WritePlus curVarNo exprBindings sexprList left right leftExprOperationSeq rightExprOperationSeq)) =
    leftContra
        (RetVal
            curVarNo
            left
            sexprList
            exprBindings
            (S leftResultVarNo)
            (LTESucc LTEZero)
            leftExprOperations
            depth
            leftExprOperationSeq)
leftExprFailed leftContra (RetVal curVarNo (MkArithGate left right MINUS) sexprList exprBindings (S (S rightResultVarNo)) prfLTE1 (leftExprOperations ++ (rightExprOperations ++ [Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo)])) depth (WriteMinus curVarNo exprBindings sexprList left right leftExprOperationSeq rightExprOperationSeq)) =
    leftContra
        (RetVal
            curVarNo
            left
            sexprList
            exprBindings
            (S leftResultVarNo)
            (LTESucc LTEZero)
            leftExprOperations
            depth
            leftExprOperationSeq)
leftExprFailed leftContra (RetVal curVarNo (MkArithGate left right MUL) sexprList exprBindings (S (S rightResultVarNo)) prfLTE1 (leftExprOperations ++ (rightExprOperations ++ [Operation (S rightResultVarNo) MUL (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo)])) depth (WriteMul curVarNo exprBindings sexprList left right leftExprOperationSeq rightExprOperationSeq)) =
    leftContra
        (RetVal
            curVarNo
            left
            sexprList
            exprBindings
            (S leftResultVarNo)
            (LTESucc LTEZero)
            leftExprOperations
            depth
            leftExprOperationSeq)
leftExprFailed leftContra (RetVal curVarNo (MkArithGate left right EQ) sexprList exprBindings (S (S (S (S rightResultVarNo)))) prfLTE1 (leftWrittenOperations ++ (rightWrittenOperations ++ [Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo), Operation (S (S (S rightResultVarNo))) MUL (VarLeaf (S (S rightResultVarNo))) (VarLeaf (S rightResultVarNo)), Operation (S rightResultVarNo) MUL (VarLeaf (S (S (S rightResultVarNo)))) (VarLeaf (S rightResultVarNo))])) depth (WriteEq curVarNo exprBindings sexprList left right leftWritten rightWritten)) =
    leftContra
        (RetVal
            curVarNo
            left
            sexprList
            exprBindings
            (S leftResultVarNo)
            (LTESucc LTEZero)
            leftWrittenOperations
            depth
            leftWritten)

runInvocationFailed : (contra : SExprToOperatorReturnType curVarNo invocation sexprList exprBindings depth -> Void) -> SExprToOperatorReturnType curVarNo (MkRun invocation) sexprList exprBindings depth -> Void
runInvocationFailed contra (RetVal curVarNo (MkRun invocation) sexprList exprBindings (S invocationResultVarNo) prfLTE1 operationSeq depth (WriteRun curVarNo invocation sexprList invocationWritten)) =
    contra
        (RetVal
            curVarNo
            invocation
            sexprList
            exprBindings
            (S invocationResultVarNo)
            (LTESucc LTEZero)
            operationSeq
            depth
            invocationWritten)



remainingArgFailed : (remainingArgs : List SExpr) ->
                     (remainingWrittenContra : (operations : List R1CSStatement ** endVarNo : Nat ** producedBindings : List Nat ** OperationSeqFormList (MkFormList remainingArgs) (S curArgResultNo) existingVarBindings sexprList operations endVarNo producedBindings depth) -> Void) ->
                     (curArgPrfLTE1 : LTE 1 (S curArgResultNo)) ->
                     (curArgWritten : OperationSeq curArg startVarNo existingVarBindings sexprList curArgOperationSeq (S curArgResultNo) depth) ->
                     (operations : List R1CSStatement ** endVarNo : Nat ** producedBindings : List Nat ** OperationSeqFormList (MkFormList (curArg :: remainingArgs)) startVarNo existingVarBindings sexprList operations endVarNo producedBindings depth) -> Void
remainingArgFailed []
                   remainingWrittenContra
                   curArgPrfLTE1
                   curArgWritten
                   (op ** endVarNo ** b ** opSeqFL)
                   {curArgResultNo} {existingVarBindings} {sexprList} =
                       (remainingWrittenContra ([] **
                                                (S curArgResultNo) **
                                                [] **
                                                WriteFormListEmpty (S curArgResultNo) existingVarBindings sexprList))
remainingArgFailed (arg :: args)
                   contra
                   prevArgPrfLTE1
                   prevArgWritten
                   (operations ** (S remainingWrittenResultVarNo) ** (initArgResultNumber :: (curArgResultNumber :: remainingBindings)) ** fromCurrentOperationSeqFormList)
                   with (fromCurrentOperationSeqFormList)
        | (WriteFormList startVarNo existingVarBindings sexprList curArg (arg :: args) curArgWritten remainingWritten prf')
            with (remainingWritten)
            | (WriteFormList (S initArgResultNumber) existingVarBindings sexprList arg args argOpSeq argsOperationsSeqFormList r1csListCompositionEquality) {curArgWrittenOperations} {remainingBindings} with (extractR1CSList argsOperationsSeqFormList)
                 | remOps with (sameOperationSeqFromSameSExpr prevArgWritten curArgWritten)
                    | (_, Refl, _) = contra ((curArgWrittenOperations ++ remOps) **
                                            (S remainingWrittenResultVarNo) **
                                            (curArgResultNumber :: remainingBindings) **
                                            (WriteFormList (S initArgResultNumber)
                                                                        existingVarBindings
                                                                        sexprList
                                                                        arg
                                                                        args
                                                                        argOpSeq
                                                                        argsOperationsSeqFormList
                                                                        Refl))




curArgFailed : (remainingArgs : List SExpr) ->
               (curArgContra : SExprToOperatorReturnType startVarNo curArg sexprList existingVarBindings depth -> Void) ->
               (operations : List R1CSStatement ** endVarNo : Nat ** producedBindings : List Nat ** OperationSeqFormList (MkFormList (curArg :: remainingArgs)) startVarNo existingVarBindings sexprList operations endVarNo producedBindings depth) -> Void
curArgFailed remainingArgs curArgContra (operations ** (S remainingWrittenResultVarNo) ** (curArgResultNo :: remainingBindings) ** opSeq) with (opSeq)
    | (WriteFormList startVarNo existingVarBindings sexprList curArg remainingArgs curArgWritten remainingWritten prf) {curArgWrittenOperations} =
        curArgContra (RetVal startVarNo
                             curArg
                             sexprList
                             existingVarBindings
                             (S curArgResultNo)
                             (LTESucc LTEZero)
                             curArgWrittenOperations
                             depth
                             curArgWritten)

mutual
    sexprToOperationSeqFormList : (formlist : FormList) ->
                                (startVarNo : Nat) ->
                                (sexprList : SExprList) ->
                                (existingVarBindings : List (String, Nat)) ->
                                (depth : Nat) ->
                          Dec (operations : List R1CSStatement ** endVarNo : Nat ** producedBindings : List Nat ** OperationSeqFormList formlist startVarNo existingVarBindings sexprList operations endVarNo producedBindings depth)
    sexprToOperationSeqFormList (MkFormList []) startVarNo sexprList existingVarBindings depth =
        Yes ([] ** startVarNo ** [] ** WriteFormListEmpty startVarNo existingVarBindings sexprList)
    sexprToOperationSeqFormList (MkFormList (curArg :: remainingArgs))
                                startVarNo
                                sexprList
                                existingVarBindings
                                depth with (sexprToOperationSeq startVarNo curArg sexprList existingVarBindings depth)
        | (Yes (RetVal startVarNo
                       curArg
                       sexprList
                       existingVarBindings
                       (S curArgResultNo)
                       curArgPrfLTE1
                       curArgOperationSeq
                       depth
                       curArgWritten)) with (sexprToOperationSeqFormList (MkFormList remainingArgs) (S curArgResultNo) sexprList existingVarBindings depth)
            | (Yes (remainingWrittenOperations ** (S remainingWrittenResultVarNo) ** remainingBindings ** opSeqFormListRemaining)) =
                Yes ((curArgOperationSeq ++ remainingWrittenOperations) **
                     (S remainingWrittenResultVarNo) **
                     (curArgResultNo :: remainingBindings) **
                     (WriteFormList startVarNo
                                    existingVarBindings
                                    sexprList
                                    curArg
                                    remainingArgs
                                    curArgWritten
                                    opSeqFormListRemaining
                                    Refl))
            | (No remainingWrittenContra) = No (remainingArgFailed remainingArgs remainingWrittenContra curArgPrfLTE1 curArgWritten)
        | (No curArgContra) = No(curArgFailed remainingArgs curArgContra)


    sexprToOperationSeq : (curVarNo : Nat) ->
                          (sexpr: SExpr) ->
                          (sexprList : SExprList) ->
                          (exprBindings : List (String, Nat)) ->
                          (depth:Nat) ->
                          Dec (SExprToOperatorReturnType curVarNo sexpr sexprList exprBindings depth)
    sexprToOperationSeq curVarNo (MkDigit x) sexprList exprBindings depth = Yes
        (RetVal curVarNo
                (MkDigit x)
                sexprList
                exprBindings
                (S curVarNo)
                (LTESucc LTEZero)
                [(Operation curVarNo DIGIT (DigitLeaf x) NilLeaf)]
                depth
                (WriteDigit curVarNo
                            x
                            exprBindings
                            sexprList))
    sexprToOperationSeq curVarNo (MkString x) sexprList exprBindings depth = ?sexprToOperationSeq_rhs_2
    sexprToOperationSeq curVarNo (MkDef x xs y) sexprList exprBindings depth = ?sexprToOperationSeq_rhs_3
    sexprToOperationSeq curVarNo (MkLet bindingVarName bindingVarVal letBody) sexprList exprBindings depth = case (sexprToOperationSeq curVarNo bindingVarVal sexprList exprBindings depth) of
        (Yes
            (RetVal
                curVarNo
                bindingVarVal
                sexprList
                exprBindings
                (S bindingExprResultVarNo)
                (LTESucc x)
                bindingValOps
                depth
                bindingExprWritten)) =>
                    case (sexprToOperationSeq
                            (S bindingExprResultVarNo)
                            letBody
                            sexprList
                            ((bindingVarName, bindingExprResultVarNo) :: exprBindings)
                            depth) of
                        (Yes (RetVal (S bindingExprResultVarNo) letBody sexprList ((bindingVarName, bindingExprResultVarNo) :: exprBindings) (S letBodyResultVarNo) (LTESucc x) letBodyOperations depth letBodyWritten)) =>
                            Yes
                                (RetVal
                                    curVarNo
                                    (MkLet bindingVarName bindingVarVal letBody)
                                    sexprList
                                    exprBindings
                                    (S letBodyResultVarNo)
                                    (LTESucc x)
                                    (bindingValOps ++ letBodyOperations)
                                    depth
                                    (WriteLet
                                        curVarNo
                                        bindingVarName
                                        bindingVarVal
                                        letBody
                                        sexprList
                                        bindingExprWritten
                                        letBodyWritten))
                        (No letBodyContra) => No (failedWriteLetBody x letBodyContra bindingExprWritten)
        (No bindingVarValContra) => No (failedWriteBindingVal bindingVarValContra)
    sexprToOperationSeq curVarNo (MkCond ifExpr thenExpr elseExpr) sexprList exprBindings depth =
        case (sexprToOperationSeq curVarNo ifExpr sexprList exprBindings depth) of
            (Yes (RetVal
                    curVarNo
                    ifExpr
                    sexprList
                    exprBindings
                    (S varNoAfterIF)
                    prfLTE1IF
                    ifExprWrittenOps
                    depth
                    opSeqTypeIF)) => case (sexprToOperationSeq (S varNoAfterIF) thenExpr sexprList exprBindings depth) of
                (Yes (RetVal
                        (S varNoAfterIF)
                        thenExpr
                        sexprList
                        exprBindings
                        (S varNoAfterTHEN)
                        prfLTE1THEN
                        thenExprWrittenOps
                        depth
                        opSeqTypeTHEN)) => case (sexprToOperationSeq (S varNoAfterTHEN) elseExpr sexprList exprBindings depth) of
                    (Yes (RetVal
                            (S varNoAfterTHEN)
                            elseExpr
                            sexprList
                            exprBindings
                            (S varNoAfterELSE)
                            prfLTE1ELSE
                            elseExprWrittenOps
                            depth
                            opSeqTypeELSE)) =>
                            Yes (RetVal
                                    curVarNo
                                    (MkCond ifExpr thenExpr elseExpr)
                                    sexprList
                                    exprBindings
                                    (S (S (S (S varNoAfterELSE))))
                                    (LTESucc LTEZero)
                                    (ifExprWrittenOps ++
                                     thenExprWrittenOps ++
                                     elseExprWrittenOps ++
                                     [Operation (S varNoAfterELSE)
                                               MUL
                                               (VarLeaf varNoAfterIF)
                                               (VarLeaf varNoAfterELSE),
                                      Operation (S (S varNoAfterELSE))
                                               MINUS
                                               (DigitLeaf 1)
                                               (VarLeaf varNoAfterIF),
                                      Operation (S (S (S varNoAfterELSE)))
                                               MUL
                                               (VarLeaf (S (S varNoAfterELSE)))
                                               (VarLeaf varNoAfterTHEN)])
                                        depth
                                      (WriteCond curVarNo exprBindings sexprList ifExpr thenExpr elseExpr opSeqTypeIF opSeqTypeTHEN opSeqTypeELSE))
                    (No elseContra) => No (failedWriteElseExpression prfLTE1THEN elseContra opSeqTypeIF opSeqTypeTHEN prfLTE1IF)
                (No thenExprContra) => No (failedWriteThenExpression prfLTE1IF thenExprContra opSeqTypeIF)
            (No ifExprContra) => No (failedWriteIfExpression ifExprContra)
    sexprToOperationSeq curVarNo (MkVar x) sexprList exprBindings depth = case (isVarInBindings x exprBindings) of
        (Yes (varNo ** prf)) => Yes
            (RetVal
                curVarNo
                (MkVar x)
                sexprList
                exprBindings
                (S curVarNo)
                (LTESucc LTEZero)
                [(Operation curVarNo ASGN (VarLeaf varNo) NilLeaf)]
                depth
                (WriteVar curVarNo
                          x
                          sexprList
                          exprBindings
                          prf))
        (No varInBindingsContra) => No (varNotInBindings varInBindingsContra)
    sexprToOperationSeq curVarNo (MkArithGate left right operator) sexprList exprBindings depth =
        case (sexprToOperationSeq curVarNo left sexprList exprBindings depth) of
            (Yes
                (RetVal curVarNo left sexprList exprBindings (S leftResultVarNo) leftPrfLTE1 leftOperationSeq depth leftOpSeqType)) =>
                    case (sexprToOperationSeq (S leftResultVarNo) right sexprList exprBindings depth) of
                        (Yes (RetVal (S leftResultVarNo) right sexprList exprBindings (S rightResultVarNo) rightPrfLTE1 rightOperationSeq depth rightOpSeqType)) =>
                            case operator of
                                EQ =>   Yes (RetVal
                                                curVarNo
                                                (MkArithGate left right EQ)
                                                sexprList
                                                exprBindings
                                                (S (S (S (S rightResultVarNo))))
                                                (LTESucc LTEZero)
                                                (leftOperationSeq ++
                                                rightOperationSeq ++
                                                [Operation (S rightResultVarNo)
                                                           MINUS
                                                           (VarLeaf leftResultVarNo)
                                                           (VarLeaf rightResultVarNo),
                                                 Operation (S (S (S rightResultVarNo)))
                                                           MUL
                                                           (VarLeaf (S (S rightResultVarNo)))
                                                           (VarLeaf (S rightResultVarNo)),
                                                 Operation (S rightResultVarNo)
                                                           MUL
                                                           (VarLeaf (S (S (S rightResultVarNo))))
                                                           (VarLeaf (S rightResultVarNo))])
                                                depth
                                                (WriteEq curVarNo
                                                         exprBindings
                                                         sexprList
                                                         left
                                                         right
                                                         leftOpSeqType
                                                         rightOpSeqType
                                                         ))
                                PLUS => Yes (RetVal
                                            curVarNo
                                            (MkArithGate left right PLUS)
                                            sexprList
                                            exprBindings
                                            (S (S rightResultVarNo))
                                            (LTESucc LTEZero)
                                            (leftOperationSeq ++ rightOperationSeq ++ [(Operation (S rightResultVarNo) PLUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))])
                                            depth
                                            (WritePlus curVarNo
                                                       exprBindings
                                                       sexprList
                                                       left
                                                       right
                                                       leftOpSeqType
                                                       rightOpSeqType))
                                MUL => Yes (RetVal
                                            curVarNo
                                            (MkArithGate left right MUL)
                                            sexprList
                                            exprBindings
                                            (S (S rightResultVarNo))
                                            (LTESucc LTEZero)
                                            (leftOperationSeq ++ rightOperationSeq ++ [(Operation (S rightResultVarNo) MUL (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))])
                                            depth
                                            (WriteMul curVarNo
                                                       exprBindings
                                                       sexprList
                                                       left
                                                       right
                                                       leftOpSeqType
                                                       rightOpSeqType))
                                MINUS => Yes (RetVal
                                            curVarNo
                                            (MkArithGate left right MINUS)
                                            sexprList
                                            exprBindings
                                            (S (S rightResultVarNo))
                                            (LTESucc LTEZero)
                                            (leftOperationSeq ++ rightOperationSeq ++ [(Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))])
                                            depth
                                            (WriteMinus curVarNo
                                                       exprBindings
                                                       sexprList
                                                       left
                                                       right
                                                       leftOpSeqType
                                                       rightOpSeqType))
                                GT => ?rhs_8
                                LT => ?rhs_9
                                GTE => ?rhs_10
                                LTE => ?rhs_11
                        (No rightContra) => No (rightExprFailed leftPrfLTE1 rightContra leftOpSeqType)
            (No leftContra) => No (leftExprFailed leftContra)
    sexprToOperationSeq curVarNo (MkSTREQ left right) sexprList exprBindings depth = ?sexprToOperationSeq_rhs_8
    sexprToOperationSeq curVarNo (MkConcat left right) sexprList exprBindings depth = ?sexprToOperationSeq_rhs_9
    sexprToOperationSeq curVarNo (MkAppend item coll) sexprList exprBindings depth = ?sexprToOperationSeq_rhs_10
    sexprToOperationSeq curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings Z =
        No finalDepthReached
    sexprToOperationSeq curVarNo (MkInvocation fnName (MkFormList invocationArgs)) sexprList exprBindings (S preDepth)
        with (canExtractDefinitionForInvocation fnName invocationArgs IsInvocation sexprList)
        | (Yes invDefPrf) with (invDefPrf)
            | (defBody ** defArgs ** extractedDef) with (sexprToOperationSeqFormList (MkFormList invocationArgs) curVarNo sexprList exprBindings preDepth)
                | (Yes (invocationArgsWrittenOperations ** (S invocationArgsFinalResultVarNo)  ** constructedArgBindings ** invocationArgsWritten))
                    with (getZip  defArgs constructedArgBindings)
                    | (Yes (zipped ** zippedPrf)) with (sexprToOperationSeq (S invocationArgsFinalResultVarNo) defBody sexprList zipped preDepth)
                        | (Yes (RetVal (S invocationArgsFinalResultVarNo)
                                       defBody
                                       sexprList
                                       zipped --(zipWith (\x, y => (x, y)) defArgs constructedArgBindings)
                                       (S invocationBodyResultVarNo)
                                       prfLTE1
                                       operationSeq
                                       preDepth
                                       invocationBodyWritten)) = let opSeq = WriteInvocation curVarNo
                                                                                               exprBindings
                                                                                               sexprList
                                                                                               fnName
                                                                                               invocationArgs
                                                                                               defArgs
                                                                                               defBody
                                                                                               extractedDef
                                                                                               invocationArgsWritten
                                                                                               invocationBodyWritten
                                                                                               zippedPrf
                            in Yes (RetVal curVarNo
                                   (MkInvocation fnName (MkFormList invocationArgs))
                                   sexprList
                                   exprBindings
                                   (S invocationBodyResultVarNo)
                                   (LTESucc LTEZero)
                                   (invocationArgsWrittenOperations ++ operationSeq)
                                   (S preDepth)
                                   opSeq)
                        | (No bodyToOpSeqFailed) = No (bodyCannotBeWritten extractedDef bodyToOpSeqFailed zippedPrf invocationArgsWritten)
                    | (No notZippable) = No (cannotContinueWithoutZipping extractedDef invDefPrf notZippable invocationArgsWritten)
                    -- with (isZipped defArgs constructedArgBindings exprBindings)
                | (No argsToOpSeqFormFailed) = No (impossibleToContinueWithoutArgs extractedDef invDefPrf argsToOpSeqFormFailed)
        | (No definitionsForInvocationNotFound) = No(impossibleToContinueWithoutFctDef definitionsForInvocationNotFound)
    sexprToOperationSeq curVarNo (MkRun invocation) sexprList exprBindings depth = case (sexprToOperationSeq curVarNo invocation sexprList exprBindings depth) of
        (Yes (RetVal curVarNo invocation sexprList exprBindings (S invocationResultVarNo) prfLTE1 operationSeq depth opSeqType)) =>
            Yes
                (RetVal
                    curVarNo
                    (MkRun invocation)
                    sexprList
                    exprBindings
                    (S invocationResultVarNo)
                    prfLTE1
                    operationSeq
                    depth
                    (WriteRun
                        curVarNo
                        invocation
                        sexprList
                        opSeqType))
        (No contra) => No (runInvocationFailed contra)
