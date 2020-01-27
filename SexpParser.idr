module SexpParser

import public Lightyear
import Lightyear.Char
import Lightyear.Strings
-- import Examples.WriteR1CS
import Data.Vect
import Data.SortedMap
import Examples.SExpr
--import Examples.EnvironmentVF

%access export
%default partial
%access public export


isCtrlChar : Char -> Bool
isCtrlChar '_' = True
isCtrlChar _ = False

isName : Char -> Bool
isName x = isCtrlChar x || isAlphaNum x

name : (Monad m, Stream Char s) => ParserT s m Char
name = satisfy isName <?> "name"

hex : Parser Int
hex = do
    c <- map (ord . toUpper) $ satisfy isHexDigit
    pure $ if c >= ord '0' && c <= ord '9' then c - ord '0'
                                           else 10 + c - ord 'A'

hexQuad : Parser Int
hexQuad = do
    a <- hex
    b <- hex
    c <- hex
    d <- hex
    pure $ a * 4096 + b * 256 + c * 16 + d

specialChar : Parser Char
specialChar = do
    c <- anyChar
    case c of
      '"'  => pure '"'
      '\\' => pure '\\'
      '/'  => pure '/'
      'b'  => pure '\b'
      'f'  => pure '\f'
      'n'  => pure '\n'
      'r'  => pure '\r'
      't'  => pure '\t'
      'u'  => map chr hexQuad
      _    => fail "expected special char"

parseName : Parser String
parseName = lexeme (letter >>= \x => commitTo $ do {
              xs <- many name
              let name = pack (x :: xs)
              pure name
          })


parseString' : Parser (List Char)
parseString' = (char '"' *!> pure Prelude.List.Nil) <|> do
    c <- satisfy (/= '"')
    if (c == '\\') then map (::) specialChar <*> parseString'
                   else map (c ::) parseString'

parseString : Parser String
parseString = char '"' *> map pack parseString' <?> "SExp string"

-- whitespace separated token sequence
parseForm : Parser String
parseForm = parseName <* spaces

parseForms : Parser (List String)
parseForms = many parseForm

-- expressions

mutual
    parseOperator : Parser String
    parseOperator = do
        res <- string "EQ" <* spaces
            <|> string "PLUS" <* spaces
            <|> string "MINUS" <* spaces
            <|> string "GT" <* spaces
            <|> string "GTE" <* spaces
            <|> string "LT" <* spaces
            <|> string "LTE" <* spaces
            <|> string "MUL" <* spaces
        pure res

    parseArithGate : Parser SExpr
    parseArithGate = do
        token "("
        operator <- parseOperator
        left <- parseExpr
        right <- parseExpr
        token ")"
        pure (MkArithGate left right (case operator of
            "EQ" => EQ
            "PLUS" => PLUS
            "MINUS" => MINUS
            "GT" => GT
            "GTE" => GTE
            "LT" => LT
            "LTE" => LTE
            "MUL" => MUL))

    parseSTREQ : Parser SExpr
    parseSTREQ = do
        token "(STREQ"
        left <- parseExpr
        right <- parseExpr
        token ")"
        pure (MkSTREQ left right)

    parseCONCAT : Parser SExpr
    parseCONCAT = do
        token "(CONCAT"
        left <- parseExpr
        right <- parseExpr
        token ")"
        pure (MkConcat left right)

    parseAPPEND : Parser SExpr
    parseAPPEND = do
        token "(APPEND"
        left <- parseString
        right <- parseExpr
        token ")"
        pure (MkAppend left right)

    parseInvocation : Parser SExpr
    parseInvocation = do
        token "("
        fnName <- parseName
        args <- many parseExpr
        token ")"
        pure (MkInvocation fnName (MkFormList args))


    parseExpr : Parser SExpr
    parseExpr = parseArithGate
        <|> (map MkDigit parseDigit)
        <|> (map MkVar parseName)
        <|> (map MkString parseString)
        <|> parseSTREQ
        <|> parseCONCAT
        <|> parseAPPEND
        <|> parseLet
        <|> parseCond
        <|> parseInvocation

    parseDef : Parser (String, List String, SExpr)
    parseDef = do
        token "(def"
        name <- ntimes 1 parseName
        token "("
        args <- parseForms
        token ")"
        body <- parseExpr
        token ")"
        -- pure ((head name), args, body)
        pure (
            (head name),
            args,
            body
        )

    parseDigit : Parser Integer
    parseDigit = do
      digits <- integer  <* spaces
      pure $ digits

    parseIt : Parser SExpr
    parseIt = (map MkVar parseName)
           <|>
           (map MkDigit parseDigit)
           <|>
           (map MkString parseString)
           <|>
           (map (\(name, args, body) => (MkDef name args body))  parseDef)
           <|>
           parseRun

    parseRun : Parser SExpr
    parseRun = do
        token "(run"
        fnName <- parseName
        token ")"
        pure (MkRun (MkInvocation fnName (MkFormList [])))

    parseBinding : Parser (String, SExpr)
    parseBinding = do
        token "("
        varname <- parseName
        varval  <- parseExpr
        token ")"
        pure (varname, varval)

    parseLet : Parser SExpr
    parseLet = do
        token "(let"
        (varname, varval) <- parseBinding
        body <- parseExpr
        token ")"
        pure (MkLet varname varval body)

    parseCond : Parser SExpr
    parseCond = do
        token "(cond"
        sexprs <- many parseExpr
        token ")"
        pure (consumeConds sexprs)

    consumeConds : List SExpr -> SExpr
    consumeConds [] = (MkCond (MkVar "illegal") (MkVar "illegal") (MkVar "illegal"))
    consumeConds (x :: []) = (MkCond (MkVar "illegal") (MkVar "illegal") (MkVar "illegal"))
    consumeConds ((MkVar "otherwise") :: (y :: xs)) = y
    consumeConds (x :: (y :: xs)) = (MkCond x y (consumeConds xs))

parseSExprList : Parser SExprList
parseSExprList = (MkSExprList <$> parens (many parseIt))

loadP : IO String
loadP = do
    Right read <- readFile "/Users/shriphani/Downloads/pythag.dsl" | Left _ => pure ""
    pure read

main : IO ()
main = do
    Right read <- readFile "/Users/shriphani/onu/ly/pytharg/pythagVerif.dsl" | Left _ => pure ()
    Right parsed <- pure $ (Lightyear.Strings.parse parseSExprList read) | Left er => do
        putStrLn er
        pure ()
    putStrLn ("parsed!" ++ (writeSExprList parsed))
    pure ()
