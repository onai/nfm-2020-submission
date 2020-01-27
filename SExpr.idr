module SExpr

%access export
%default partial
%access public export

data ArithmeticOperator = EQ | PLUS | MUL | MINUS | GT | LT | GTE | LTE

DecEq ArithmeticOperator where
    decEq    EQ EQ    = Yes Refl
    decEq    EQ PLUS  = No (\Refl impossible)
    decEq    EQ MUL   = No (\Refl impossible)
    decEq    EQ MINUS = No (\Refl impossible)
    decEq    EQ GT    = No (\Refl impossible)
    decEq    EQ LT    = No (\Refl impossible)
    decEq    EQ GTE   = No (\Refl impossible)
    decEq    EQ LTE   = No (\Refl impossible)
    decEq  PLUS EQ    = No (\Refl impossible)
    decEq  PLUS PLUS  = Yes Refl
    decEq  PLUS MUL   = No (\Refl impossible)
    decEq  PLUS MINUS = No (\Refl impossible)
    decEq  PLUS GT    = No (\Refl impossible)
    decEq  PLUS LT    = No (\Refl impossible)
    decEq  PLUS GTE   = No (\Refl impossible)
    decEq  PLUS LTE   = No (\Refl impossible)
    decEq   MUL EQ    = No (\Refl impossible)
    decEq   MUL PLUS  = No (\Refl impossible)
    decEq   MUL MUL   = Yes Refl
    decEq   MUL MINUS = No (\Refl impossible)
    decEq   MUL GT    = No (\Refl impossible)
    decEq   MUL LT    = No (\Refl impossible)
    decEq   MUL GTE   = No (\Refl impossible)
    decEq   MUL LTE   = No (\Refl impossible)
    decEq MINUS EQ    = No (\Refl impossible)
    decEq MINUS PLUS  = No (\Refl impossible)
    decEq MINUS MUL   = No (\Refl impossible)
    decEq MINUS MINUS = Yes Refl
    decEq MINUS GT    = No (\Refl impossible)
    decEq MINUS LT    = No (\Refl impossible)
    decEq MINUS GTE   = No (\Refl impossible)
    decEq MINUS LTE   = No (\Refl impossible)
    decEq    GT EQ    = No (\Refl impossible)
    decEq    GT PLUS  = No (\Refl impossible)
    decEq    GT MUL   = No (\Refl impossible)
    decEq    GT MINUS = No (\Refl impossible)
    decEq    GT GT    = Yes Refl
    decEq    GT LT    = No (\Refl impossible)
    decEq    GT GTE   = No (\Refl impossible)
    decEq    GT LTE   = No (\Refl impossible)
    decEq    LT EQ    = No (\Refl impossible)
    decEq    LT PLUS  = No (\Refl impossible)
    decEq    LT MUL   = No (\Refl impossible)
    decEq    LT MINUS = No (\Refl impossible)
    decEq    LT GT    = No (\Refl impossible)
    decEq    LT LT    = Yes Refl
    decEq    LT GTE   = No (\Refl impossible)
    decEq    LT LTE   = No (\Refl impossible)
    decEq   GTE EQ    = No (\Refl impossible)
    decEq   GTE PLUS  = No (\Refl impossible)
    decEq   GTE MUL   = No (\Refl impossible)
    decEq   GTE MINUS = No (\Refl impossible)
    decEq   GTE GT    = No (\Refl impossible)
    decEq   GTE LT    = No (\Refl impossible)
    decEq   GTE GTE   = Yes Refl
    decEq   GTE LTE   = No (\Refl impossible)
    decEq   LTE EQ    = No (\Refl impossible)
    decEq   LTE PLUS  = No (\Refl impossible)
    decEq   LTE MUL   = No (\Refl impossible)
    decEq   LTE MINUS = No (\Refl impossible)
    decEq   LTE GT    = No (\Refl impossible)
    decEq   LTE LT    = No (\Refl impossible)
    decEq   LTE GTE   = No (\Refl impossible)
    decEq   LTE LTE   = Yes Refl

mutual
    data FormList : Type where
        MkFormList : List SExpr -> FormList

    writeFormList : FormList -> String
    writeFormList (MkFormList xs) = "(\n" ++ (unlines (map toString xs)) ++ ")"


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
        MkInvocation : (fnName : String) -> (args : FormList) -> SExpr
        MkRun : (invocation : SExpr) -> SExpr





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
    toString (MkInvocation fnName args) = "(invoke:" ++ fnName ++ " " ++ (writeFormList args) ++ ")"
    toString (MkRun fnName) = "(run " ++ (toString fnName) ++ ")"

mutual
    DecEq FormList where
      decEq (MkFormList xs) (MkFormList ys) = case (decEq xs ys) of
            (Yes Refl) => Yes Refl
            (No contra) => No (\Refl => contra Refl)

    DecEq SExpr where
      decEq (MkDigit x) (MkDigit y) = case (decEq x y) of
            (Yes Refl) => Yes Refl
            (No contra) => No (\Refl => contra Refl)
      decEq (MkDigit x) (MkString y)                                            = No (\Refl impossible)
      decEq (MkDigit x) (MkDef y xs z)                                          = No (\Refl impossible)
      decEq (MkDigit x) (MkLet y z w)                                           = No (\Refl impossible)
      decEq (MkDigit x) (MkCond ifExpr thenExpr elseExpr)                       = No (\Refl impossible)
      decEq (MkDigit x) (MkVar y)                                               = No (\Refl impossible)
      decEq (MkDigit x) (MkArithGate left right operator)                       = No (\Refl impossible)
      decEq (MkDigit x) (MkSTREQ left right)                                    = No (\Refl impossible)
      decEq (MkDigit x) (MkConcat left right)                                   = No (\Refl impossible)
      decEq (MkDigit x) (MkAppend item coll)                                    = No (\Refl impossible)
      decEq (MkDigit x) (MkInvocation fnName args)                              = No (\Refl impossible)
      decEq (MkDigit x) (MkRun invocation)                                      = No (\Refl impossible)
      decEq (MkString x) (MkDigit y)                                            = No (\Refl impossible)
      decEq (MkString x) (MkString y) = case (decEq x y) of
            (Yes Refl) => Yes Refl
            (No contra) => No (\Refl => contra Refl)
      decEq (MkString x) (MkDef y xs z)                                         = No (\Refl impossible)
      decEq (MkString x) (MkLet y z w)                                          = No (\Refl impossible)
      decEq (MkString x) (MkCond ifExpr thenExpr elseExpr)                      = No (\Refl impossible)
      decEq (MkString x) (MkVar y)                                              = No (\Refl impossible)
      decEq (MkString x) (MkArithGate left right operator)                      = No (\Refl impossible)
      decEq (MkString x) (MkSTREQ left right)                                   = No (\Refl impossible)
      decEq (MkString x) (MkConcat left right)                                  = No (\Refl impossible)
      decEq (MkString x) (MkAppend item coll)                                   = No (\Refl impossible)
      decEq (MkString x) (MkInvocation fnName args)                             = No (\Refl impossible)
      decEq (MkString x) (MkRun invocation)                                     = No (\Refl impossible)
      decEq (MkDef x xs y) (MkDigit z)                                          = No (\Refl impossible)
      decEq (MkDef x xs y) (MkString z)                                         = No (\Refl impossible)
      decEq (MkDef x xs y) (MkDef z ys w) = case decEq (x,xs,y) (z,ys,w) of
          (Yes Refl) => Yes Refl
          (No contra) => No (\Refl => contra Refl)
      decEq (MkDef x xs y) (MkLet z w s)                                        = No (\Refl impossible)
      decEq (MkDef x xs y) (MkCond ifExpr thenExpr elseExpr)                    = No (\Refl impossible)
      decEq (MkDef x xs y) (MkVar z)                                            = No (\Refl impossible)
      decEq (MkDef x xs y) (MkArithGate left right operator)                    = No (\Refl impossible)
      decEq (MkDef x xs y) (MkSTREQ left right)                                 = No (\Refl impossible)
      decEq (MkDef x xs y) (MkConcat left right)                                = No (\Refl impossible)
      decEq (MkDef x xs y) (MkAppend item coll)                                 = No (\Refl impossible)
      decEq (MkDef x xs y) (MkInvocation fnName args)                           = No (\Refl impossible)
      decEq (MkDef x xs y) (MkRun invocation)                                   = No (\Refl impossible)
      decEq (MkLet x y z) (MkDigit w)                                           = No (\Refl impossible)
      decEq (MkLet x y z) (MkString w)                                          = No (\Refl impossible)
      decEq (MkLet x y z) (MkDef w xs s)                                        = No (\Refl impossible)
      decEq (MkLet x y z) (MkLet w s t) = case decEq (x,y,z) (w,s,t) of
          (Yes Refl) => Yes Refl
          (No contra) => No (\Refl => contra Refl)
      decEq (MkLet x y z) (MkCond ifExpr thenExpr elseExpr)                     = No (\Refl impossible)
      decEq (MkLet x y z) (MkVar w)                                             = No (\Refl impossible)
      decEq (MkLet x y z) (MkArithGate left right operator)                     = No (\Refl impossible)
      decEq (MkLet x y z) (MkSTREQ left right)                                  = No (\Refl impossible)
      decEq (MkLet x y z) (MkConcat left right)                                 = No (\Refl impossible)
      decEq (MkLet x y z) (MkAppend item coll)                                  = No (\Refl impossible)
      decEq (MkLet x y z) (MkInvocation fnName args)                            = No (\Refl impossible)
      decEq (MkLet x y z) (MkRun invocation)                                    = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkDigit x)                       = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkString x)                      = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkDef x xs y)                    = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkLet x y z)                     = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkCond ifExpr' thenExpr' elseExpr') =
          case decEq (ifExpr, thenExpr, elseExpr) (ifExpr', thenExpr', elseExpr') of
          (Yes Refl) => Yes Refl
          (No contra) => No (\Refl => contra Refl)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkVar x)                         = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkArithGate left right operator) = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkSTREQ left right)              = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkConcat left right)             = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkAppend item coll)              = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkInvocation fnName args)        = No (\Refl impossible)
      decEq (MkCond ifExpr thenExpr elseExpr) (MkRun invocation)                = No (\Refl impossible)
      decEq (MkVar x) (MkDigit y)                                               = No (\Refl impossible)
      decEq (MkVar x) (MkString y)                                              = No (\Refl impossible)
      decEq (MkVar x) (MkDef y xs z)                                            = No (\Refl impossible)
      decEq (MkVar x) (MkLet y z w)                                             = No (\Refl impossible)
      decEq (MkVar x) (MkCond ifExpr thenExpr elseExpr)                         = No (\Refl impossible)
      decEq (MkVar x) (MkVar y) = case (decEq x y) of
          (Yes Refl) => Yes Refl
          (No contra) => No (\Refl => contra Refl)
      decEq (MkVar x) (MkArithGate left right operator)                         = No (\Refl impossible)
      decEq (MkVar x) (MkSTREQ left right)                                      = No (\Refl impossible)
      decEq (MkVar x) (MkConcat left right)                                     = No (\Refl impossible)
      decEq (MkVar x) (MkAppend item coll)                                      = No (\Refl impossible)
      decEq (MkVar x) (MkInvocation fnName args)                                = No (\Refl impossible)
      decEq (MkVar x) (MkRun invocation)                                        = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkDigit x)                       = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkString x)                      = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkDef x xs y)                    = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkLet x y z)                     = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkCond ifExpr thenExpr elseExpr) = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkVar x)                         = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkArithGate left' right' operator') =
          case decEq (left, right, operator) (left', right', operator') of
              (Yes Refl) => Yes Refl
              (No contra) => No (\Refl => contra Refl)
      decEq (MkArithGate left right operator) (MkSTREQ x y)                     = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkConcat x y)                    = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkAppend item coll)              = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkInvocation fnName args)        = No (\Refl impossible)
      decEq (MkArithGate left right operator) (MkRun invocation)                = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkDigit x)                                    = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkString x)                                   = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkDef x xs y)                                 = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkLet x y z)                                  = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkCond ifExpr thenExpr elseExpr)              = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkVar x)                                      = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkArithGate x y operator)                     = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkSTREQ left' right') =
          case decEq (left,right) (left', right') of
              (Yes Refl) => Yes Refl
              (No contra) => No (\Refl => contra Refl)
      decEq (MkSTREQ left right) (MkConcat x y)                                 = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkAppend item coll)                           = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkInvocation fnName args)                     = No (\Refl impossible)
      decEq (MkSTREQ left right) (MkRun invocation)                             = No (\Refl impossible)
      decEq (MkConcat left right) (MkDigit x)                                   = No (\Refl impossible)
      decEq (MkConcat left right) (MkString x)                                  = No (\Refl impossible)
      decEq (MkConcat left right) (MkDef x xs y)                                = No (\Refl impossible)
      decEq (MkConcat left right) (MkLet x y z)                                 = No (\Refl impossible)
      decEq (MkConcat left right) (MkCond ifExpr thenExpr elseExpr)             = No (\Refl impossible)
      decEq (MkConcat left right) (MkVar x)                                     = No (\Refl impossible)
      decEq (MkConcat left right) (MkArithGate x y operator)                    = No (\Refl impossible)
      decEq (MkConcat left right) (MkSTREQ x y)                                 = No (\Refl impossible)
      decEq (MkConcat left right) (MkConcat left' right') =
          case decEq (left,right) (left', right') of
              (Yes Refl) => Yes Refl
              (No contra) => No (\Refl => contra Refl)
      decEq (MkConcat left right) (MkAppend item coll)                          = No (\Refl impossible)
      decEq (MkConcat left right) (MkInvocation fnName args)                    = No (\Refl impossible)
      decEq (MkConcat left right) (MkRun invocation)                            = No (\Refl impossible)
      decEq (MkAppend item coll) (MkDigit x)                                    = No (\Refl impossible)
      decEq (MkAppend item coll) (MkString x)                                   = No (\Refl impossible)
      decEq (MkAppend item coll) (MkDef x xs y)                                 = No (\Refl impossible)
      decEq (MkAppend item coll) (MkLet x y z)                                  = No (\Refl impossible)
      decEq (MkAppend item coll) (MkCond ifExpr thenExpr elseExpr)              = No (\Refl impossible)
      decEq (MkAppend item coll) (MkVar x)                                      = No (\Refl impossible)
      decEq (MkAppend item coll) (MkArithGate left right operator)              = No (\Refl impossible)
      decEq (MkAppend item coll) (MkSTREQ left right)                           = No (\Refl impossible)
      decEq (MkAppend item coll) (MkConcat left right)                          = No (\Refl impossible)
      decEq (MkAppend item coll) (MkAppend item' coll') =
          case decEq (item, coll) (item', coll') of
              (Yes Refl) => Yes Refl
              (No contra) => No (\Refl => contra Refl)
      decEq (MkAppend item coll) (MkInvocation fnName args)                     = No (\Refl impossible)
      decEq (MkAppend item coll) (MkRun invocation)                             = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkDigit x)                              = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkString x)                             = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkDef x xs y)                           = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkLet x y z)                            = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkCond ifExpr thenExpr elseExpr)        = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkVar x)                                = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkArithGate left right operator)        = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkSTREQ left right)                     = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkConcat left right)                    = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkAppend item coll)                     = No (\Refl impossible)
      decEq (MkInvocation fnName args) (MkInvocation fnName' args') =
          case decEq (fnName, args) (fnName', args') of
              (Yes Refl) => Yes Refl
              (No contra) => No (\Refl => contra Refl)
      decEq (MkInvocation fnName args) (MkRun invocation)                       = No (\Refl impossible)
      decEq (MkRun invocation) (MkDigit x)                                      = No (\Refl impossible)
      decEq (MkRun invocation) (MkString x)                                     = No (\Refl impossible)
      decEq (MkRun invocation) (MkDef x xs y)                                   = No (\Refl impossible)
      decEq (MkRun invocation) (MkLet x y z)                                    = No (\Refl impossible)
      decEq (MkRun invocation) (MkCond ifExpr thenExpr elseExpr)                = No (\Refl impossible)
      decEq (MkRun invocation) (MkVar x)                                        = No (\Refl impossible)
      decEq (MkRun invocation) (MkArithGate left right operator)                = No (\Refl impossible)
      decEq (MkRun invocation) (MkSTREQ left right)                             = No (\Refl impossible)
      decEq (MkRun invocation) (MkConcat left right)                            = No (\Refl impossible)
      decEq (MkRun invocation) (MkAppend item coll)                             = No (\Refl impossible)
      decEq (MkRun invocation) (MkInvocation fnName args)                       = No (\Refl impossible)
      decEq (MkRun invocation) (MkRun invocation') = case decEq invocation invocation' of
          (Yes Refl) => Yes Refl
          (No contra) => No (\Refl => contra Refl)

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
