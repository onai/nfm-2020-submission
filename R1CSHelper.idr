module R1CSHelper

import Data.List
import Examples.SExpr
import Examples.EnvironmentVF
import Examples.WriteR1CS

%access export
%default partial
%access public export



getEndVarFromOperationSeqFormList : OperationSeqFormList _ _ _ _ _ k _ _ -> Nat
getEndVarFromOperationSeqFormList _ {k} = k

getBindingsFromOperationSeqFormList : OperationSeqFormList _ _ _ _ _ _ bs _ -> List Nat
getBindingsFromOperationSeqFormList _ {bs} = bs

getZippedList : {a,b:Type} -> {xs:List a} -> {ys:List b} -> (Zipped xs ys zs) -> List (a,b)
getZippedList _ {zs} = zs

extractR1CSList : (OperationSeqFormList _ _ _ _ r1csList _ _ _) -> List R1CSStatement
extractR1CSList _ {r1csList} = r1csList

endValue : (OperationSeq _ _ _ _ _ (S k) _) -> Nat
endValue _ {k} = k

twoVoidProofsEquivalent : (notHere : (currentSExpr = MkDef fnName defArgs defBody) -> Void) ->
                          (notHere' : (currentSExpr = MkDef fnName defArgs defBody) -> Void) ->
                          (notHere=notHere')
twoVoidProofsEquivalent notHere notHere' = believe_me (notHere = notHere')


argsOrBodyDifferent : ((MkDef fnName defArgs defBody = MkDef fnName defArgs' defBody') -> Void) -> Either (Not (defArgs = defArgs'))  (Not (defBody = defBody'))
argsOrBodyDifferent f {defBody} {defBody'} {defArgs} {defArgs'} {fnName} = case (decEq defBody defBody') of
    (No contra) => Right contra
    (Yes Refl) => case (decEq defArgs defArgs') of
        (No contra) => Left contra
        (Yes Refl) => absurd (f Refl)




Uninhabited ((ty_a, ty_a',ty_b,ty_c:Type) -> (a1:ty_a) -> (a2:ty_a') -> (b1,b2:ty_b) -> (c1,c2:ty_c) ->  Not (b1=b2) -> (a1=a2, b1=b2, c1=c2)) where
  uninhabited f = let tuple = (f Nat Nat Nat Nat Z Z Z (S Z) Z Z (the (Not (0 = S 0)) uninhabited)) in uninhabited (fst (snd tuple))


secondInTupleImpossible : (ty_a,ty_a',ty_b,ty_c:Type) -> (a1:ty_a) -> (a2:ty_a') -> (b1,b2:ty_b) -> (c1,c2:ty_c) ->  Not (b1=b2) -> (a1=a2, b1=b2, c1=c2)
secondInTupleImpossible ty_a ty_a' ty_b ty_c a1 a2 b1 b2 c1 c2 x = absurd secondInTupleImpossible

secondInTupleImpossible' : {ty_a,ty_a',ty_b,ty_c:Type} -> {a1:ty_a} -> {a2:ty_a'} -> {b1,b2:ty_b} -> {c1,c2:ty_c} ->  (Not (b1=b2)) -> (a1=a2, b1=b2, c1=c2)
secondInTupleImpossible' contra {ty_a} {ty_a'} {ty_b} {ty_c} {a1} {a2} {b1} {b2} {c1} {c2} = secondInTupleImpossible ty_a ty_a' ty_b ty_c a1 a2 b1 b2 c1 c2 contra

impossibleToUniteArgs : (argsDifferent : Not (defArgs = defArgs')) ->
                        (DefinitionHere fnName defArgs defBody invocationArgs = DefinitionLater fnName defArgs' defBody' invocationArgs notHere previous, defArgs = defArgs', defBody = defBody')
impossibleToUniteArgs argsDifferent = secondInTupleImpossible' argsDifferent

swap2nd3ndElementInTuple : (a,b,c) -> (a,c,b)
swap2nd3ndElementInTuple x = ((fst x), snd (snd x), fst (snd x))

symInNot : {ty:Type} -> {a,b:ty} -> ((a = b) -> Void) -> (b=a) -> Void
symInNot f Refl = f Refl

sameDefBody : (a:ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs defBody) sexprList) ->
              (b:ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName invocationArgs defArgs' defBody') sexprList) ->
              (a=b, defArgs=defArgs', defBody=defBody')
sameDefBody (DefinitionHere fnName defArgs defBody invocationArgs) (DefinitionHere fnName defArgs defBody invocationArgs) = (Refl, Refl, Refl)
sameDefBody (DefinitionHere fnName defArgs defBody invocationArgs) (DefinitionLater fnName defArgs' defBody' invocationArgs notHere previous)
 = case argsOrBodyDifferent notHere of
     (Left argsDifferent) => secondInTupleImpossible' argsDifferent
     (Right bodyDifferent) => swap2nd3ndElementInTuple (secondInTupleImpossible' bodyDifferent)
sameDefBody (DefinitionLater fnName defArgs defBody invocationArgs notHere previous) (DefinitionHere fnName defArgs' defBody' invocationArgs)
    = case argsOrBodyDifferent notHere of
        (Left argsDifferent) => secondInTupleImpossible' (symInNot argsDifferent)
        (Right bodyDifferent) => swap2nd3ndElementInTuple (secondInTupleImpossible' (symInNot bodyDifferent))
sameDefBody (DefinitionLater fnName defArgs defBody invocationArgs notHere previous) (DefinitionLater fnName defArgs' defBody' invocationArgs notHere' previous') =
    case (sameDefBody previous previous') of
        (Refl, Refl, Refl) => rewrite twoVoidProofsEquivalent notHere notHere' in (Refl, Refl, Refl)



eqTransitive : {ty:Type} -> {a,b,x:List ty} -> (prf1:a=x) -> (prf2:b=x) -> (a=b, prf1 = prf2)
eqTransitive Refl Refl = (Refl, Refl)


zippingUnique : (z1:Zipped xs ys zas) -> (z2:Zipped xs ys zbs) -> (zas=zbs, z1=z2)
zippingUnique ZipEnd ZipEnd = (Refl, Refl)
zippingUnique (Zip x y remaining) (Zip x y remaining') with (zippingUnique remaining remaining')
    | (eq1, eq2) = rewrite eq1 in rewrite eq2 in (Refl, Refl)

mutual
    sameOperationSeqFormListSame :  (a:OperationSeqFormList formlist startVarNo existingVarBindings sexprList operations1 endVarNo1 producedBindings1 depth) ->
                                    (b:OperationSeqFormList formlist startVarNo existingVarBindings sexprList operations2 endVarNo2 producedBindings2 depth) ->
                                    (a=b, operations1=operations2, endVarNo1=endVarNo2, producedBindings1=producedBindings2)
    sameOperationSeqFormListSame (WriteFormList startVarNo existingVarBindings sexprList curArg remainingArgs curArgWritten remainingWritten prf)
                                 (WriteFormList startVarNo existingVarBindings sexprList curArg remainingArgs curArgWritten' remainingWritten' prf') =
        case sameOperationSeqFromSameSExpr curArgWritten curArgWritten' of
            (Refl, Refl, Refl) => case sameOperationSeqFormListSame remainingWritten remainingWritten' of
                (Refl, Refl, Refl, Refl) => case eqTransitive prf prf' of
                    (Refl, Refl) => (Refl, Refl, Refl, Refl)
    sameOperationSeqFormListSame (WriteFormListEmpty startVarNo existingVarBindings sexprList) (WriteFormListEmpty startVarNo existingVarBindings sexprList) = (Refl, Refl, Refl, Refl)


    sameOperationSeqFromSameSExpr : (a:OperationSeq sexpr startVar varBindings sexprList r1css1 endVarNo1 depth) ->
                                    (b:OperationSeq sexpr startVar varBindings sexprList r1css2 endVarNo2 depth) ->
                                    (a=b, endVarNo1=endVarNo2, r1css1=r1css2)
    sameOperationSeqFromSameSExpr (WriteDigit startVar digit varBindings sexprList) (WriteDigit startVar digit varBindings sexprList) = (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WritePlus startVar varBindings sexprList leftExpr rightExpr leftExprOperationSeq rightExprOperationSeq)
                                  (WritePlus startVar varBindings sexprList leftExpr rightExpr leftExprOperationSeq' rightExprOperationSeq') =
        case (sameOperationSeqFromSameSExpr leftExprOperationSeq leftExprOperationSeq') of
            (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr rightExprOperationSeq rightExprOperationSeq') of
                (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteMinus startVar varBindings sexprList leftExpr rightExpr leftExprOperationSeq rightExprOperationSeq)
                                  (WriteMinus startVar varBindings sexprList leftExpr rightExpr leftExprOperationSeq' rightExprOperationSeq') =
        case (sameOperationSeqFromSameSExpr leftExprOperationSeq leftExprOperationSeq') of
            (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr rightExprOperationSeq rightExprOperationSeq') of
                (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteMul startVar varBindings sexprList leftExpr rightExpr leftExprOperationSeq rightExprOperationSeq)
                                  (WriteMul startVar varBindings sexprList leftExpr rightExpr leftExprOperationSeq' rightExprOperationSeq') =
        case (sameOperationSeqFromSameSExpr leftExprOperationSeq leftExprOperationSeq') of
            (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr rightExprOperationSeq rightExprOperationSeq') of
                (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteLet startVar bindingVarName bindingExpr letBody sexprList bindingExprWritten letBodyWritten)
                                  (WriteLet startVar bindingVarName bindingExpr letBody sexprList bindingExprWritten' letBodyWritten') =
        case (sameOperationSeqFromSameSExpr bindingExprWritten bindingExprWritten') of
            (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr letBodyWritten letBodyWritten') of
                (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteRun startVar runInvocation sexprList invocationWritten)
                                  (WriteRun startVar runInvocation sexprList invocationWritten') =
        case (sameOperationSeqFromSameSExpr invocationWritten invocationWritten') of
            (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteVar startVar varName sexprList exprBindings varInBindings)
                                  (WriteVar startVar varName sexprList exprBindings varInBindings') =
        case sameVarNameSameBinding varInBindings varInBindings' of
            (Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteInvocation startVar varBindings sexprList fnName invocationArgs defArgs defBody invDefPrf invocationArgsWritten invocationBodyWritten isZippedList)
                                  (WriteInvocation startVar varBindings sexprList fnName invocationArgs defArgs' defBody' invDefPrf' invocationArgsWritten' invocationBodyWritten' isZippedList') =
        case (sameOperationSeqFormListSame invocationArgsWritten invocationArgsWritten') of
            (Refl, Refl, Refl, Refl) => case (sameDefBody invDefPrf invDefPrf') of
                (Refl, Refl, Refl) => case zippingUnique isZippedList isZippedList' of
                    (Refl, Refl) => case (sameOperationSeqFromSameSExpr invocationBodyWritten invocationBodyWritten') of
                        (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteEq startVar varBindings sexprList leftExpr rightExpr leftWritten rightWritten)
                                  (WriteEq startVar varBindings sexprList leftExpr rightExpr leftWritten' rightWritten') =
        case (sameOperationSeqFromSameSExpr leftWritten leftWritten') of
            (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr rightWritten rightWritten') of
                         (Refl, Refl, Refl) => (Refl, Refl, Refl)
    sameOperationSeqFromSameSExpr (WriteCond startVar varBindings sexprList ifExpr thenExpr elseExpr ifExprWritten thenExprWritten elseExprWritten)
                                  (WriteCond startVar varBindings sexprList ifExpr thenExpr elseExpr ifExprWritten' thenExprWritten' elseExprWritten') =
        case (sameOperationSeqFromSameSExpr ifExprWritten ifExprWritten') of
            (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr thenExprWritten thenExprWritten') of
                (Refl, Refl, Refl) => case (sameOperationSeqFromSameSExpr elseExprWritten elseExprWritten') of
                    (Refl, Refl, Refl) => (Refl, Refl, Refl)


sameFormListSameOpseqFormList : (a : OperationSeqFormList formlist startVarNo existingVarBindings sexprList operations endVarNo producedBindings depth) ->
                                (b : OperationSeqFormList formlist startVarNo existingVarBindings sexprList operations' endVarNo' producedBindings' depth) ->
                                (a=b, operations=operations', producedBindings=producedBindings')
sameFormListSameOpseqFormList
(WriteFormListEmpty endVarNo existingVarBindings sexprList)
(WriteFormListEmpty endVarNo existingVarBindings sexprList) = (Refl, Refl, Refl)
sameFormListSameOpseqFormList
    (WriteFormList startVarNo existingVarBindings sexprList curArg remainingArgs curArgWritten remainingWritten prf)
    (WriteFormList startVarNo existingVarBindings sexprList curArg remainingArgs curArgWritten' remainingWritten' prf') =
    case (sameOperationSeqFromSameSExpr curArgWritten curArgWritten') of
        (Refl, Refl, Refl) => case (sameFormListSameOpseqFormList remainingWritten remainingWritten') of
            (Refl, Refl, Refl) => case eqTransitive prf prf' of
                (Refl, Refl) => (Refl, Refl, Refl)



sameSExprSameR1CS : OperationSeq sexpr startVar varBindings sexprList r1css1 endVarNo1 depth ->
                    OperationSeq sexpr startVar varBindings sexprList r1css2 endVarNo2 depth ->
                    endVarNo1 = endVarNo2
sameSExprSameR1CS x y = case sameOperationSeqFromSameSExpr x y of
    (Refl, Refl, Refl) => Refl
