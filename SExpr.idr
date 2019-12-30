module SExpr

%access export
%default partial
%access public export

data ArithmeticOperator = EQ | PLUS | MUL | MINUS | GT | LT | GTE | LTE


data SExpr : Type where
    -- temporary, figure out how to make parseSymbol _guarantee_ a call to
    -- MkName (MkSymbol name) -- with a non-empty name

    -- syntax
    MkDigit : Integer -> SExpr
    MkString : String -> SExpr
    MkDef : String -> List String -> SExpr -> SExpr
    MkLet : String -> SExpr -> SExpr -> SExpr
    MkCond : (ifExpr : SExpr) -> (thenExpr : SExpr) -> (elseExpr : SExpr) -> SExpr
    --MkSExpr : List SExpr -> SExpr
    MkVar : String -> SExpr

    -- arithmetic
    MkArithGate : (left : SExpr) -> (right : SExpr) -> (operator : ArithmeticOperator) -> SExpr

    -- strings
    MkSTREQ : (left : SExpr) -> (right : SExpr) -> SExpr
    MkConcat : (left : SExpr) -> (right : SExpr) -> SExpr
    MkAppend : (item : String) -> (coll : SExpr) -> SExpr
    MkInvocation : (fnName : String) -> (args : SExpr) -> SExpr
    MkRun : (invocation : SExpr) -> SExpr
    MkListSExpr : (sexprs : List SExpr) -> SExpr



toString : SExpr -> String
toString (MkDigit x) = show x
toString (MkString x) = show x
toString (MkDef name xs x) = "(def " ++ name ++ " (" ++ (unwords (map show xs))  ++ ") " ++ (toString x) ++ ")"
toString (MkLet varname varval bd) = "(let" ++ "( " ++ (show varname) ++ " " ++ (toString varval) ++ ")" ++ (toString bd) ++ ")"
toString (MkCond ifExpr thenExpr elseExpr) = "(cond " ++ (toString ifExpr) ++ "\n" ++ (toString thenExpr) ++ "\n" ++ (toString elseExpr) ++ ")"
toString (MkVar x) = show x
toString (MkArithGate left right EQ) = "(EQ" ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right PLUS) = "(PLUS " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right MUL) = "(MUL " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right MINUS) = "(MINUS " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right GT) = "(GT " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right LT) = "(LT " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right GTE) = "(GTE " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkArithGate left right LTE) = "(LTE " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkSTREQ left right) = "(STREQ " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkConcat left right) = "(CONCAT " ++ (toString left) ++ " " ++ (toString right) ++ ")"
toString (MkAppend item coll) = "(APPEND " ++ (show item) ++ " " ++ (toString coll) ++ ")"
toString (MkInvocation fnName args) = "(invoke:" ++ fnName ++ " " ++ (toString args) ++ ")"
toString (MkRun fnName) = "(run " ++ (toString fnName) ++ ")"
toString (MkListSExpr sexprs) = (unwords (map toString sexprs))

data SExprList : Type where
    MkSExprList : List SExpr -> SExprList

writeSExprList : SExprList -> String
writeSExprList (MkSExprList xs) = "(\n" ++ (unlines (map toString xs)) ++ ")"


{--

DecEqs

--}


data Definition : (s:SExpr) -> Type where
    IsDefinition : Definition (MkDef name argNames body)

isDefinition : (s:SExpr) -> (Dec (Definition s))
isDefinition (MkDigit x)                = No (\IsDefinition impossible)
isDefinition (MkString x)               = No (\IsDefinition impossible)
isDefinition (MkDef x xs y)             = Yes IsDefinition
isDefinition (MkLet x y z)              = No (\IsDefinition impossible)
isDefinition (MkCond ifExpr thenExpr elseExpr)                = No (\IsDefinition impossible)
isDefinition (MkVar x)                  = No (\IsDefinition impossible)
isDefinition (MkArithGate left right op) = No (\IsDefinition impossible)
isDefinition (MkSTREQ left right)       = No (\IsDefinition impossible)
isDefinition (MkConcat left right)      = No (\IsDefinition impossible)
isDefinition (MkAppend item coll)       = No (\IsDefinition impossible)
isDefinition (MkInvocation fnName args) = No (\IsDefinition impossible)
isDefinition (MkRun fnName)             = No (\IsDefinition impossible)

data Invocation : (sexpr : SExpr) -> Type where
    IsInvocation : Invocation (MkInvocation fnName args)

isInvocation : (sexpr : SExpr) -> Dec (Invocation sexpr)
isInvocation (MkDigit x) = No (\IsInvocation impossible)
isInvocation (MkString x) = No (\IsInvocation impossible)
isInvocation (MkDef x xs y) = No (\IsInvocation impossible)
isInvocation (MkLet x y z) = No (\IsInvocation impossible)
isInvocation (MkCond ifExpr thenExpr elseExpr) = No (\IsInvocation impossible)
isInvocation (MkVar x) = No (\IsInvocation impossible)
isInvocation (MkArithGate left right operator) = No (\IsInvocation impossible)
isInvocation (MkSTREQ left right) = No (\IsInvocation impossible)
isInvocation (MkConcat left right) = No (\IsInvocation impossible)
isInvocation (MkAppend item coll) = No (\IsInvocation impossible)
isInvocation (MkInvocation fnName args) = Yes (IsInvocation)
isInvocation (MkRun invocation) = No (\IsInvocation impossible)
