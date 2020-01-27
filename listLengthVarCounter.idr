module listLengthVarCounter

import Data.List
import Examples.SExpr
import Examples.EnvironmentVF
import Examples.WriteR1CS

contractLists : {ty:Type} -> (xs:List ty) -> (xs ++ [] = xs)
contractLists [] = Refl
contractLists (x :: xs) = rewrite contractLists xs in Refl

listLengthCommutative : {ty:Type} -> (xs,ys:List ty) -> (length (xs ++ ys) = length (ys ++ xs))
listLengthCommutative [] ys = rewrite contractLists ys in Refl
listLengthCommutative (x :: xs) ys = rewrite listLengthCommutative (ys) (x :: xs) in Refl


listLengths : {ty:Type} -> (xs,ys:List ty) -> (length (xs ++ ys) = (length xs) + (length ys))
listLengths [] b = Refl
listLengths (x :: xs) [] = rewrite contractLists xs in rewrite plusCommutative (length xs) (0) in Refl
listLengths (x :: xs) (y :: ys) = rewrite listLengthCommutative xs (y::ys) in
                                  rewrite listLengths ys xs in
                                  rewrite plusCommutative (length xs) (S (length ys)) in Refl


listLengths3 : {ty:Type} -> (xs,ys:List ty) -> (z:ty) -> (length (xs ++ ys ++ [z]) = S ((length xs) + (length ys)))
listLengths3 xs ys z = rewrite listLengths xs (ys ++ [z]) in
                       rewrite listLengths ys [z] in
                       rewrite plusCommutative (length ys) 1 in
                       rewrite plusCommutative (length xs) (S (length ys)) in
                       rewrite plusCommutative (length ys) (length xs) in
                       Refl

listLengths3Lists :  {ty:Type} -> (xs,ys,zs:List ty) -> (length (xs ++ ys ++ zs) = (length xs) + (length ys)+ (length zs))
listLengths3Lists xs ys zs = rewrite listLengths xs (ys ++ zs) in
                       rewrite listLengths ys zs in
                       rewrite plusAssociative (length xs) (length ys) (length zs) in
                       Refl

listLengths4Lists :  {ty:Type} -> (ws,xs,ys,zs:List ty) -> (length (ws ++ xs ++ ys ++ zs) = (length ws) + (length xs) + (length ys) + (length zs))
listLengths4Lists ws xs ys zs = rewrite listLengths (ws) (xs ++ ys ++ zs) in
                                rewrite listLengths3Lists xs ys zs in
                                rewrite  (plusAssociative (length ws) (plus (length xs) (length ys))  (length zs)) in
                                rewrite  plusAssociative (length ws) (length xs) (length ys) in
                                Refl

extractExprOperations : (OperationSeq _ _ _ _ r1css _ _) ->
    (ops : List R1CSStatement ** ops = r1css)
extractExprOperations x {r1css} = (r1css ** Refl)

extractPrevResultVarNo : (OperationSeq _ _ _ _ _ (S endVal) _) -> (x ** x = endVal)
extractPrevResultVarNo ops {endVal} = (endVal ** Refl)


export
lengthR1CSStatementEqualVarCounterIncrement : (OperationSeq expressions startVal exprBindings sexprList bindingExprOperations endVal depth) ->
    ((length bindingExprOperations) + startVal  = endVal)
lengthR1CSStatementEqualVarCounterIncrement (WriteDigit startVal digit exprBindings sexprList) = Refl
lengthR1CSStatementEqualVarCounterIncrement (WritePlus startVal exprBindings sexprList leftExpr rightExpr leftExprOperationSeq rightExprOperationSeq)
    with (extractExprOperations leftExprOperationSeq)
        | (leftExprOperations ** Refl) with (extractPrevResultVarNo leftExprOperationSeq)
            | (leftResultVarNo ** Refl) with (extractExprOperations rightExprOperationSeq)
                | (rightExprOperations ** Refl) with (extractPrevResultVarNo rightExprOperationSeq)
                    | (rightResultVarNo ** Refl) = rewrite listLengths3 leftExprOperations
                                                                        rightExprOperations
                                                                        (Operation (S rightResultVarNo) PLUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))
                                                    in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement rightExprOperationSeq) in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement leftExprOperationSeq)  in
                                                    rewrite plusCommutative (length rightExprOperations) (plus (length leftExprOperations) startVal) in
                                                    rewrite sym (plusAssociative (length leftExprOperations) startVal (length rightExprOperations)) in
                                                    rewrite plusCommutative startVal (length rightExprOperations) in
                                                    rewrite plusAssociative (length leftExprOperations) (length rightExprOperations) startVal in
                                                    Refl

lengthR1CSStatementEqualVarCounterIncrement (WriteMinus startVal exprBindings sexprList leftExpr rightExpr leftExprOperationSeq rightExprOperationSeq)
    with (extractExprOperations leftExprOperationSeq)
        | (leftExprOperations ** Refl) with (extractPrevResultVarNo leftExprOperationSeq)
            | (leftResultVarNo ** Refl) with (extractExprOperations rightExprOperationSeq)
                | (rightExprOperations ** Refl) with (extractPrevResultVarNo rightExprOperationSeq)
                    | (rightResultVarNo ** Refl) = rewrite listLengths3 leftExprOperations
                                                                        rightExprOperations
                                                                        (Operation (S rightResultVarNo) MINUS (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))
                                                    in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement rightExprOperationSeq) in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement leftExprOperationSeq)  in
                                                    rewrite plusCommutative (length rightExprOperations) (plus (length leftExprOperations) startVal) in
                                                    rewrite sym (plusAssociative (length leftExprOperations) startVal (length rightExprOperations)) in
                                                    rewrite plusCommutative startVal (length rightExprOperations) in
                                                    rewrite plusAssociative (length leftExprOperations) (length rightExprOperations) startVal in
                                                    Refl

lengthR1CSStatementEqualVarCounterIncrement (WriteMul startVal exprBindings sexprList leftExpr rightExpr leftExprOperationSeq rightExprOperationSeq)
    with (extractExprOperations leftExprOperationSeq)
        | (leftExprOperations ** Refl) with (extractPrevResultVarNo leftExprOperationSeq)
            | (leftResultVarNo ** Refl) with (extractExprOperations rightExprOperationSeq)
                | (rightExprOperations ** Refl) with (extractPrevResultVarNo rightExprOperationSeq)
                    | (rightResultVarNo ** Refl) = rewrite listLengths3 leftExprOperations
                                                                        rightExprOperations
                                                                        (Operation (S rightResultVarNo) MUL (VarLeaf leftResultVarNo) (VarLeaf rightResultVarNo))
                                                    in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement rightExprOperationSeq) in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement leftExprOperationSeq)  in
                                                    rewrite plusCommutative (length rightExprOperations) (plus (length leftExprOperations) startVal) in
                                                    rewrite sym (plusAssociative (length leftExprOperations) startVal (length rightExprOperations)) in
                                                    rewrite plusCommutative startVal (length rightExprOperations) in
                                                    rewrite plusAssociative (length leftExprOperations) (length rightExprOperations) startVal in
                                                    Refl

lengthR1CSStatementEqualVarCounterIncrement (WriteLet startVal bindingVarName bindingExpr letBody sexprList bindingExprWritten letBodyWritten)
    with (extractExprOperations bindingExprWritten)
        | (bindingExprOperations ** Refl) with (extractPrevResultVarNo bindingExprWritten)
            | (bindingExprResultVarNo ** Refl) with (extractExprOperations letBodyWritten)
                | (letBodyOperations ** Refl) with (extractPrevResultVarNo letBodyWritten)
                    | (letBodyResultVarNo ** Refl) = rewrite listLengths bindingExprOperations letBodyOperations in
                                                     rewrite sym (lengthR1CSStatementEqualVarCounterIncrement letBodyWritten) in
                                                     rewrite sym (lengthR1CSStatementEqualVarCounterIncrement bindingExprWritten) in
                                                     rewrite plusCommutative (length bindingExprOperations) (length letBodyOperations) in
                                                     rewrite plusAssociative (length letBodyOperations) (length bindingExprOperations) startVal in
                                                     Refl

lengthR1CSStatementEqualVarCounterIncrement (WriteRun startVal runInvocation sexprList invocationWritten)
    with (extractExprOperations invocationWritten)
        | (bindingExprOperations ** Refl) = rewrite lengthR1CSStatementEqualVarCounterIncrement invocationWritten in Refl

lengthR1CSStatementEqualVarCounterIncrement (WriteVar startVal varName sexprList exprBindings varInBindings) = Refl

lengthR1CSStatementEqualVarCounterIncrement (WriteInvocation startVal exprBindings sexprList fnName invocationArgs defArgs defBody invDefPrf invocationArgsWritten invocationBodyWritten isZippedList) with (lengthR1CSStatementEqualVarCounterIncrement invocationBodyWritten)
    | (eq) = ?lengthR1CSStatementEqualVarCounterIncrement_rhs_8

lengthR1CSStatementEqualVarCounterIncrement (WriteEq startVal exprBindings sexprList leftExpr rightExpr leftWritten rightWritten)
    with (extractExprOperations leftWritten)
        | (leftWrittenOperations ** Refl) with (extractPrevResultVarNo leftWritten)
            | (leftResultVarNo ** Refl) with (extractExprOperations rightWritten)
                | (rightWrittenOperations ** Refl) with (extractPrevResultVarNo rightWritten)
                    | (rightResultVarNo ** Refl) =
                                                    rewrite listLengths3Lists leftWrittenOperations
                                                                              rightWrittenOperations
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
                                                                 (VarLeaf (S rightResultVarNo))]
                                                    in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement rightWritten) in
                                                    rewrite sym (lengthR1CSStatementEqualVarCounterIncrement leftWritten) in
                                                    rewrite plusCommutative (plus (length leftWrittenOperations) (length rightWrittenOperations)) 3 in
                                                    rewrite (plusAssociative (length rightWrittenOperations) (length leftWrittenOperations) startVal) in
                                                    rewrite plusCommutative (length leftWrittenOperations) (length rightWrittenOperations) in
                                                    Refl
lengthR1CSStatementEqualVarCounterIncrement (WriteCond startVal exprBindings sexprList ifExpr thenExpr elseExpr ifExprWritten thenExprWritten elseExprWritten)
    with (extractExprOperations elseExprWritten)
        | (elseExprWrittenOps ** Refl) with (extractPrevResultVarNo elseExprWritten)
            | (elseExprWrittenVarNo ** Refl) with (extractExprOperations thenExprWritten)
                | (thenExprWrittenOps ** Refl) with (extractPrevResultVarNo thenExprWritten)
                    | (thenExprWrittenVarNo ** Refl) with (extractExprOperations ifExprWritten)
                        | (ifExprWrittenOps ** Refl) with (extractPrevResultVarNo ifExprWritten)
                            | (ifWrittenResultVarNo ** Refl) = rewrite listLengths4Lists ifExprWrittenOps
                                                                                         thenExprWrittenOps
                                                                                         elseExprWrittenOps
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
                                                                                                  (VarLeaf thenExprWrittenVarNo)] in
                                                               rewrite plusCommutative  (plus (plus (length ifExprWrittenOps) (length thenExprWrittenOps)) (length elseExprWrittenOps)) 3 in
                                                               rewrite sym (lengthR1CSStatementEqualVarCounterIncrement elseExprWritten) in
                                                               rewrite sym (lengthR1CSStatementEqualVarCounterIncrement thenExprWritten) in
                                                               rewrite sym (lengthR1CSStatementEqualVarCounterIncrement ifExprWritten) in
                                                               rewrite plusCommutative (length ifExprWrittenOps) (length thenExprWrittenOps) in
                                                               rewrite sym (plusAssociative (length thenExprWrittenOps) (length ifExprWrittenOps) (length elseExprWrittenOps)) in
                                                               rewrite plusCommutative (length thenExprWrittenOps) (plus (length ifExprWrittenOps) (length elseExprWrittenOps)) in
                                                               rewrite plusCommutative (length ifExprWrittenOps) (length elseExprWrittenOps) in
                                                               rewrite sym (plusAssociative (length elseExprWrittenOps) (length ifExprWrittenOps) (length thenExprWrittenOps)) in
                                                               rewrite plusCommutative (length ifExprWrittenOps) (length thenExprWrittenOps) in
                                                               rewrite sym (plusAssociative (length elseExprWrittenOps) (plus (length thenExprWrittenOps) (length ifExprWrittenOps)) startVal) in
                                                               rewrite sym (plusAssociative (length thenExprWrittenOps) (length ifExprWrittenOps) startVal) in
                                                               Refl


-- --
-- -- lengthR1CSStatementEqualVarCounterIncrement (WriteVarHere startVal varName sexprList curBindingVarNo remainingBindings) = Refl
-- -- lengthR1CSStatementEqualVarCounterIncrement (WriteVarLater startVal varName sexprList curBindingVarName curBindingVarNo remainingBindings varWrittenLater)
-- --     with (extractExprOperations varWrittenLater)
-- --         | (bindingExprOperations ** Refl) = rewrite lengthR1CSStatementEqualVarCounterIncrement varWrittenLater in Refl
-- --
-- -- lengthR1CSStatementEqualVarCounterIncrement (WriteListSExprEmpty startVal exprBindings sexprList) = Refl
-- --
-- -- lengthR1CSStatementEqualVarCounterIncrement (WriteInvocation startVal exprBindings sexprList fnName invocationArgs defArgs defBody invDefPrf invocationArgsWritten invocationBodyWritten)
-- --     with (extractExprOperations invocationArgsWritten)
-- --         | (invocationArgsWrittenOperations ** Refl) with (extractPrevResultVarNo invocationArgsWritten)
-- --            | (invocationArgsFinalResultVarNo ** Refl) with (extractExprOperations invocationBodyWritten)
-- --                 | (invocationBodyWrittenOperations ** Refl) with (extractPrevResultVarNo invocationBodyWritten)
-- --                     | (invocationBodyResultVarNo ** Refl) = rewrite listLengths invocationArgsWrittenOperations invocationBodyWrittenOperations in
-- --                                                             rewrite sym (lengthR1CSStatementEqualVarCounterIncrement invocationBodyWritten) in
-- --                                                             rewrite sym (lengthR1CSStatementEqualVarCounterIncrement invocationArgsWritten) in
-- --                                                             rewrite plusCommutative  (length invocationArgsWrittenOperations) (length invocationBodyWrittenOperations) in
-- --                                                             rewrite plusAssociative (length invocationBodyWrittenOperations) (length invocationArgsWrittenOperations) startVal in
-- --                                                             Refl
--

--

--
