module IRTS.CodegenDSL(codegenDSL) where

import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Simplified
import Idris.Core.TT

import Data.Maybe
import Data.Char

import Text.PrettyPrint hiding (Str)

dslPreamble :: Doc
dslPreamble = vcat . map text $
  [
    -- "def idris_error(str); puts str; exit(0); end",
    -- "def idris_writeStr(str); puts str; end",
    -- "def idris_readStr;return gets;end",
    -- "def idris_append(l, r);return l + r;end",
    -- "def idris_is_none(l,r); l == r ? 1 : 0;end"
    --"; Auto generated Onai R1CS DSL"
     ]

codegenDSL :: CodeGenerator
codegenDSL ci = writeFile (outputFile ci) (render source)
  where
    source = text "(" $+$
        dslPreamble $+$ br $+$
        (text out) $+$
        text "(run " <> start  <> text ")" $+$
        text ")"
    out = concatMap (show . doCodegen) (simpleDecls ci)
    start = dslname (sMN 0 "runMain")

dslname :: Name -> Doc
dslname n = text "idris_" <> (text $ concatMap dslchar (showCG n))
  where dslchar x | isAlpha x || isDigit x = [x]
                   | otherwise = "_" ++ show (fromEnum x) ++ "_"

var :: Name -> Doc
var n = dslname n

loc :: Int -> Doc
loc i = text "loc" <> (text $ show i)

doCodegen :: (Name, SDecl) -> Doc
doCodegen (n, SFun _ args i def) = cgFun n args def

cgComment :: Doc -> Doc
cgComment t = text ";" <+> t

cgIndent :: Doc
cgIndent = text "  "

doRet :: Doc -> Doc
doRet str = cgIndent <> str

def :: Doc
def = text "(def"

end :: Doc
end = text ")"

br :: Doc
br = text "\n"


cgFun :: Name -> [Name] -> SExp -> Doc
cgFun n args d
    -- = comment $+$ function $+$ br
    = function $+$ br
    where
      function = def <+> signature $+$  body <> end
      signature = dslname n
        <> text " (" <> text (showSep " " (map (show . loc . fst) (zip [0..] args)))
        <> text ")"
      body = cgBody doRet d
      comment = cgComment (text $ (show n))

-- cgBody converts the SExp into a chunk of DSL which calculates the result
-- of an expression, then runs the function on the resulting bit of code.
--
-- We do it this way because we might calculate an expression in a deeply nested
-- case statement, or inside a let, etc, so the assignment/return of the calculated
-- expression itself may happen quite deeply.


cgBody :: (Doc -> Doc) -> SExp -> Doc
cgBody ret (SV (Glob n)) = ret $ dslname n
cgBody ret (SV (Loc i)) = ret $ loc i
cgBody ret (SApp _ f args) = ret $ text " (" <> dslname f <> text " " <>
                                   text (showSep " " (map (show . cgVar) args)) <> text ")"
cgBody ret (SLet (Loc i) v sc) =
    cgIndent <> text "(let ("<> loc i <+> text " " <+> cgBody (\x -> x) v <> text ") "  <+> br <> cgBody ret sc <> text ")"
cgBody ret (SUpdate n e) = text "update" <> cgIndent <> cgBody ret e
cgBody ret (SProj e i)
   = ret $ cgVar e <> lbrack <> text (show (i + 1)) <> rbrack
cgBody ret (SCon _ t n args)
   = ret $ text "(list " <> text (showSep " " ((show t) : (map (show . cgVar) args))) <> text ")"
cgBody ret (SCase _ e alts)
   = let scrvar = cgVar e
         scr = if any conCase alts then text "(first " <> scrvar <> text ")" else scrvar in
          cgIndent <> text "(cond"  $+$
          text (showSep "\n" (map (show . (cgAlt scr ret scrvar )) alts)) $+$
          cgIndent <> end <+> br
  where conCase (SConCase _ _ _ _ _) = True
        conCase _ = False
cgBody ret (SChkCase e alts)
   = let scrvar = cgVar e
         scr = if any conCase alts then text "(first " <> scrvar <> text ")" else  scrvar  in
          cgIndent <+> text "(cond " $+$
            text (showSep "\n" (map (show . (cgAlt scr ret scrvar)) alts)) $+$
            cgIndent <> end <+> br
  where conCase (SConCase _ _ _ _ _) = True
        conCase _ = False

cgBody ret (SConst c) = ret $ (cgConst c)
cgBody ret (SOp op args) = ret $ cgOp op (map (show . cgVar) args)
cgBody ret SNothing = ret $ text "0"
cgBody ret (SError x) = ret $ text ("(string ERROR " ++ show x ++ ")")
cgBody ret _ = ret $ text "idris_error(\"NOT IMPLEMENTED!!!!\")"



cgAlt :: Doc -> (Doc -> Doc) -> Doc -> SAlt -> Doc
cgAlt cond ret scr (SConstCase t exp)
   = cgIndent <> text "(EQ " <+> text (show t) <> text " " <> text (show cond) <> text ")" $+$
     cgIndent <> cgBody ret exp
cgAlt cond ret scr (SDefaultCase exp)
   = cgIndent <> text " (EQ " <> scr <> text " -1)" $+$
     cgIndent <> text "    (-1)" $+$
     cgIndent <> text" otherwise" $+$
                                   cgIndent <> cgBody ret exp
cgAlt cond ret scr (SConCase lv t n args exp)
   = cgIndent <> text "(EQ " <> text (show cond) <> text " " <+> text (show t) <> text ")" $+$
     cgIndent <> project 1 lv args $+$
     cgIndent <> cgBody ret exp <> closingParens args
   where project i v [] = text ""
         project i v (n : ns) =  text "(let " <> loc v <>
                                text " (nth " <> scr <> text " " <> text (show i) <> text ")" $+$
                                cgIndent <> project (i + 1) (v + 1) ns
         closingParens [] = text ""
         closingParens (n : ns) = text ")" <> closingParens ns

cgVar :: LVar -> Doc
cgVar (Loc i) = loc i
cgVar (Glob n) = var n

printString :: String -> Doc
printString "(" = text "(LPAREN)"
printString ")" = text "(RPAREN)"
printString s = text "(string \"" <> text s <> text "\")"


cgConst :: Const -> Doc
cgConst (I i) = text $ show i
cgConst (Ch i) = text $ show (ord i)
cgConst (BI i) = text $ show i
cgConst (Str s) = printString s
cgConst TheWorld = text "0"
cgConst x | isTypeConst x = text "0"
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

cgOp :: PrimFn -> [String] -> Doc
cgOp (LPlus (ATInt _)) [l, r]
     = text $ "(PLUS " ++ l ++ " " ++ r ++ ")"
cgOp (LMinus (ATInt _)) [l, r]
     = text $ "(MINUS " ++ l ++ " " ++ r ++ ")"
cgOp (LTimes (ATInt _)) [l, r]
     = text $ "(MUL " ++ l ++ " " ++ r ++ ")"
cgOp (LEq (ATInt _)) [l, r]
     = text $ "(EQ " ++ l ++ " " ++ r ++ ")"
cgOp (LSLt (ATInt _)) [l, r]
     = text $ "(LT " ++ l ++ " " ++ r ++ ")"
cgOp (LSLe (ATInt _)) [l, r]
     = text $ "(LTE " ++ l ++ " " ++ r ++ ")"
cgOp (LSGt (ATInt _)) [l, r]
     = text $ "(GT " ++ l ++ " " ++ r ++ ")"
cgOp (LSGe (ATInt _)) [l, r]
     = text $ "(GTE " ++ l ++ " " ++ r ++ ")"
cgOp LStrEq [l,r] = text $ "(strEq " ++ l ++ "  " ++ r ++ ")"
cgOp LStrRev [x]
    = text $ "(reverse " ++ x ++ ")"
cgOp LStrLen [x]
    = text $ "(length " ++ x ++ ")"
cgOp LStrHead [x]
    = text $ "(ord (first " ++ x ++ "))"
cgOp LStrIndex [x, y]
    = text $ "(ord (nth " ++ x ++ " " ++ y ++ "))"
cgOp LStrTail [x]
    = text $ "(rest " ++ x ++ ")"
cgOp (LIntStr _) [x]
    = text $ "(str " ++ x ++ ")"
cgOp (LChInt _) [x] = text $ x
cgOp (LIntCh _) [x] = text $ x
cgOp (LSExt _ _) [x] = text $ x
cgOp (LTrunc _ _) [x] = text $ x
cgOp LWriteStr [_,str] = text $ "(print " ++ str ++ ")"
cgOp LStrConcat [l,r] = text $ "(concat " ++ l ++ " " ++ r ++ ")"
cgOp LStrCons [l,r] = text $ "(cons (chr " ++ l ++ ") " ++ r ++ ")"
cgOp op exps = text $ "(string OPERATOR " ++ show op ++ " NOT IMPLEMENTED)"
   -- error("Operator " ++ show op ++ " not implemented")
