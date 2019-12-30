module Environment

import Data.List
import Examples.SExpr

%access export
%default partial
%access public export



data Definitions : (sexprs : SExprList) -> (defnBindings : List (String, SExpr)) -> Type where
    EmptyDefs : Definitions (MkSExprList []) []
    NextDef : (defName : String) ->
              (defArgs : List String) ->
              (defBody : SExpr) ->
              (remainingExprs : List SExpr) ->
              (remaining : Definitions (MkSExprList remainingExprs) remainingBindings) ->
              Definitions
                (MkSExprList ((MkDef defName defArgs defBody) :: remainingExprs))
                ((defName, (MkDef defName defArgs defBody)) :: remainingBindings)
    CurNotDef : (x : SExpr) ->
                (remainingExprs : List SExpr) ->
                (remainingPrf : Definitions (MkSExprList remainingExprs) remainingBindings) ->
                (notDef : (Not (Definition x))) ->
                Definitions (MkSExprList (x :: remainingExprs))
                            remainingBindings

collectDefinitions : (sexprs : SExprList) -> (defnBindings ** (Definitions sexprs defnBindings))
collectDefinitions (MkSExprList []) = ([] ** EmptyDefs)
collectDefinitions (MkSExprList (x :: xs)) with (collectDefinitions (MkSExprList xs))
    | (remainingBindings ** remainingPrf) = case (isDefinition x) of
        (Yes (IsDefinition {name} {argNames} {body})) => (((name, (MkDef name argNames body)) :: remainingBindings) ** (NextDef name argNames body xs remainingPrf))
        (No contra) => (remainingBindings ** (CurNotDef x xs remainingPrf contra))

data Run : (sexpr : SExpr) -> Type where
    IsRun : Run (MkRun fnName)

isRun : (sexpr : SExpr) -> (Dec (Run sexpr))
isRun (MkDigit x) = No (\IsRun impossible)
isRun (MkString x) = No (\IsRun impossible)
isRun (MkDef x xs y) = No (\IsRun impossible)
isRun (MkLet x y z) = No (\IsRun impossible)
isRun (MkCond ife thene elsee) = No (\IsRun impossible)
isRun (MkVar x) = No (\IsRun impossible)
isRun (MkArithGate left right operator) = No (\IsRun impossible)
isRun (MkSTREQ left right) = No (\IsRun impossible)
isRun (MkConcat left right) = No (\IsRun impossible)
isRun (MkAppend item coll) = No (\IsRun impossible)
isRun (MkInvocation fnName args) = No (\IsRun impossible)
isRun (MkListSExpr exprs) = No (\IsRun impossible)
isRun (MkRun fnName) = Yes IsRun

data CollectedRun : (sexprs : SExprList) -> (runExpr : SExpr) -> Type where
    CurSExpr : (runSExpr : SExpr) -> (runPrf : Run runSExpr) -> (rest : List SExpr) -> CollectedRun (MkSExprList (runSExpr :: rest)) runSExpr
    Rest : (x : SExpr) -> (runContra : Not (Run x)) -> (rest : List SExpr) -> (restPrf : CollectedRun (MkSExprList rest) runExpr) -> CollectedRun (MkSExprList (x :: rest)) runExpr

emptySExprList : (runExpr ** CollectedRun (MkSExprList []) runExpr) -> Void
emptySExprList (_ ** (CurSExpr _ _ _)) impossible
emptySExprList (_ ** (Rest _ _ _ _)) impossible

neitherHeadNorRest : (xs : List SExpr) -> (restContra : (runExpr : SExpr ** CollectedRun (MkSExprList xs) runExpr) -> Void) -> (curContra : Run x -> Void) -> (runExpr : SExpr ** CollectedRun (MkSExprList (x :: xs)) runExpr) -> Void
neitherHeadNorRest xs restContra curContra (x ** (CurSExpr x xPrf xs)) = curContra xPrf
neitherHeadNorRest xs restContra curContra (x ** (Rest _ _ xs restPrf)) = restContra (x ** restPrf)

hasRun : (sexprs : SExprList) -> Dec (runExpr ** (CollectedRun sexprs runExpr))
hasRun (MkSExprList []) = No emptySExprList
hasRun (MkSExprList (x :: xs)) = case (isRun x) of
    (Yes prf) => Yes (x ** CurSExpr x prf xs)
    (No curContra) => case (hasRun (MkSExprList xs)) of
        (Yes (restRun ** restRunPrf)) => Yes (restRun ** (Rest x curContra xs restRunPrf))
        (No restContra) => No (neitherHeadNorRest xs restContra curContra)


data InvokationOfDefinition : (invocSExpr:SExpr) -> (defSExpr:SExpr) -> Type where
    IsInvokationOfDefinition : (fnName : String) ->
                               (argVals : List SExpr) ->
                               (defArgs : List String) ->
                               (defBody : SExpr) ->
                               InvokationOfDefinition (MkInvocation fnName (MkListSExpr argVals)) (MkDef fnName defArgs defBody)



isInvokationOfDefinition : (invocSExpr:SExpr) -> (defSExpr:SExpr) -> Dec (InvokationOfDefinition invocSExpr defSExpr)
isInvokationOfDefinition (MkDigit x) defSExpr                       = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkString x) defSExpr                      = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkDef x xs y) defSExpr                    = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkLet x y z) defSExpr                     = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkCond ifE thenE elseE) defSExpr                       = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkVar x) defSExpr                         = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkArithGate left right operator) defSExpr = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkSTREQ left right) defSExpr              = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkConcat left right) defSExpr             = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkAppend item coll) defSExpr              = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkRun invocation) defSExpr                = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkListSExpr args) defSExpr                = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkDigit x)                       = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkString x)                      = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkLet x y z)                     = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkCond ifE thenE elseE)                       = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkVar x)                         = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkArithGate left right operator) = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkSTREQ left right)              = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkConcat left right)             = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkAppend item coll)              = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkInvocation x xs)               = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName args) (MkRun invocation)                = No (\(IsInvokationOfDefinition _ _ _ _) impossible)
isInvokationOfDefinition (MkInvocation fnName (MkListSExpr args)) (MkDef x xs y) with (decEq fnName x)
    | (Yes prf) = rewrite prf in (Yes (IsInvokationOfDefinition x args xs y))
    | (No contra) = No (\(IsInvokationOfDefinition fnName args xs y) => contra Refl)

getInvocPartOfInvokationOfDefinition : (invocDef:InvokationOfDefinition i d) -> (x : String ** xs:SExpr ** (i = MkInvocation x xs))
getInvocPartOfInvokationOfDefinition (IsInvokationOfDefinition fnName argVals defArgs defBody) = (fnName ** (MkListSExpr argVals) ** Refl)

getDefPartOfInvokationOfDefinition : (invocDef:InvokationOfDefinition i d) -> (x : String ** xs:(List String) ** y:SExpr ** (d = MkDef x xs y))
getDefPartOfInvokationOfDefinition (IsInvokationOfDefinition fnName argVals defArgs defBody) = (fnName ** defArgs ** defBody ** Refl)


data ExtractDefinitionFromInvocation : (InvokationOfDefinition invocation definition) -> (sexprs : SExprList) -> Type where
    DefinitionHere : (defName : String) ->
                     (defArgs : List String) ->
                     (defBody : SExpr) ->
                     (argVals : List SExpr) ->
                     ExtractDefinitionFromInvocation (IsInvokationOfDefinition defName argVals defArgs defBody) (MkSExprList ((MkDef defName defArgs defBody) :: remainingBindings))
    DefinitionLater: (defName : String) ->
                     (defArgs : List String) ->
                     (defBody : SExpr) ->
                     (argVals : List SExpr) ->
                     (previous: ExtractDefinitionFromInvocation (IsInvokationOfDefinition defName argVals defArgs defBody) (MkSExprList previousSExprLst)) ->
                     ExtractDefinitionFromInvocation (IsInvokationOfDefinition defName argVals defArgs defBody) (MkSExprList (currentSExpr :: previousSExprLst))



emptySExprListImpossible : (invPrf : Invocation (MkInvocation fnName (MkListSExpr args))) -> (defBody : SExpr ** defArgs : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName args defArgs defBody) (MkSExprList [])) -> Void
emptySExprListImpossible invPrf (defBody ** defArgs ** pf) with (pf)
    | (DefinitionHere _ _ _ _) impossible
    | (DefinitionLater _ _ _ _ _) impossible



notHereNotLater : (notFoundLater : (defBody : SExpr ** defArgs : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName args defArgs defBody) (MkSExprList sexprs)) -> Void) -> (notFoundHere : (fnName' = fnName) -> Void) -> (defBody1 : SExpr ** defArgs1 : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName args defArgs1 defBody1) (MkSExprList ((MkDef fnName' defArgs defBody) :: sexprs))) -> Void
notHereNotLater notFoundLater notFoundHere (n ** axs ** pf) with (pf)
    | (DefinitionHere _ _ _ _) = notFoundHere Refl
    | (DefinitionLater fnName axs n args previous) = notFoundLater (n ** axs ** previous)


alsoNotFoundLater : (notFoundHere : InvokationOfDefinition (MkInvocation fnName (MkListSExpr args)) sexprHead -> Void) -> (notFoundLater : (defBody : SExpr ** defArgs : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName args defArgs defBody) (MkSExprList sexprs)) -> Void) -> (defBody : SExpr ** defArgs : List String ** ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName args defArgs defBody) (MkSExprList (sexprHead :: sexprs))) -> Void
alsoNotFoundLater notFoundHere notFoundLater (n ** axs ** pf)  with (pf)
    | (DefinitionHere invocFname _ _ invocArgs) = notFoundHere (IsInvokationOfDefinition invocFname invocArgs axs n)
    | (DefinitionLater fnName axs n args previous) = notFoundLater (n ** axs ** previous)



{-

Principal function to extract the body and the arguments of an invocation from a List of SExprs

-}

canExtractDefinitionForInvocation : (fnName : String) -> (args : List SExpr) ->
                                    (invPrf : Invocation (MkInvocation fnName (MkListSExpr args))) ->
                                    (sexprs : SExprList) ->
                                    Dec (defBody : SExpr  ** defArgs : (List String) ** (ExtractDefinitionFromInvocation (IsInvokationOfDefinition fnName args defArgs defBody) sexprs))
canExtractDefinitionForInvocation fnName args invPrf (MkSExprList []) = No (emptySExprListImpossible invPrf)
canExtractDefinitionForInvocation fnName args IsInvocation (MkSExprList (sexprHead :: sexprs)) with (isInvokationOfDefinition (MkInvocation fnName (MkListSExpr args)) sexprHead)
    | (Yes prf)  with (getDefPartOfInvokationOfDefinition prf)
        | (fnName' ** defArgs ** defBody ** sexprHeadEQMkDef) = rewrite sexprHeadEQMkDef in case (decEq fnName' fnName) of
            (Yes Refl) => Yes (defBody ** defArgs ** DefinitionHere fnName defArgs defBody args)
            (No notFoundHere) => case (canExtractDefinitionForInvocation fnName args IsInvocation (MkSExprList sexprs)) of
                (Yes foundLater) => case (foundLater) of
                    (db ** da ** extractedDef) => Yes (db ** da ** DefinitionLater fnName da db args extractedDef)
                (No notFoundLater) => No (notHereNotLater notFoundLater notFoundHere)
    | (No notFoundHere) = case (canExtractDefinitionForInvocation fnName args IsInvocation (MkSExprList sexprs)) of
        (Yes foundLater) => case (foundLater) of
            (db ** da ** extractedDef) => Yes (db ** da ** DefinitionLater fnName da db args extractedDef)
        (No notFoundLater) => No (alsoNotFoundLater notFoundHere notFoundLater)
