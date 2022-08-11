module emerson-lang.Lang exposing (..)

import Parser exposing (..)
import Set
import Array

-- type TypeLit = TNumLit | TBoolLit | TFuncLit TypeLit TypeLit

type Expr = Ident String 
          | Call (Located Expr) (Located Expr)
          | Function (List String) (Located Expr)
          | If (Located Expr) (Located Expr) (Located Expr)
          | NumberLit Float
          | BoolLit Bool
          | CharLit Char
          | StringLit String
          | Tuple (List (Located Expr))
          | Prefix String (Located Expr)
          | Infix (Located Expr) String (Located Expr)
          | ArrayLit (List (Located Expr))
          | Index (Located Expr) (Located Expr)
          | LetBlock (Located (String, Located Expr)) (Located Expr)

keywords : Set.Set String
keywords = Set.fromList ["true", "false", "if", "else", "in"]

type alias Located a =
  { start : (Int, Int)
  , value : a
  , end : (Int, Int)
  }

located : Parser a -> Parser (Located a)
located parser =
  succeed Located
    |= getPosition
    |= parser
    |= getPosition

locmap : Located a -> b -> Located b
locmap loc constraint = case loc of
    {start, end} -> {start=start, value=constraint, end=end}

parseIdentString : Parser String
parseIdentString = variable
    { start = Char.isLower
    , inner = \c -> Char.isAlphaNum c || c == '_'
    , reserved = keywords
    }

-- simplyTypedArg : Parser (String, TypeLit)
-- simplyTypedArg = succeed Tuple.pair
--               |= variable
--                 { start = Char.isLower
--                 , inner = \c -> Char.isAlphaNum c || c == '_'
--                 , reserved = keywords
--                 }
--               |. ws
--               |. symbol ":"
--               |. ws
--               |= parseType

-- parseTypeLit : Parser TypeLit
-- parseTypeLit = oneOf [keyword "Num" |> map (\_->TNumLit), keyword "Bool" |> map (\_->TBoolLit)]

-- parseType : Parser TypeLit
-- parseType = oneOf [succeed identity |. symbol "(" |= lazy (\_->parseType) |. symbol ")", parseTypeLit |> andThen (\t->oneOf [succeed (TFuncLit t) |. symbol "->" |= lazy (\_->parseType), succeed t])]

parseIdent : Parser (Located Expr)
parseIdent = map Ident parseIdentString |> located

parseBool : Parser (Located Expr)
parseBool = oneOf 
    [ keyword "true"  |> map (\_ -> BoolLit True )
    , keyword "false" |> map (\_ -> BoolLit False)
    ] |> located

parseNumber : Parser (Located Expr)
parseNumber = map NumberLit float |> located

parseIf : Parser (Located Expr)
parseIf = succeed If
       |. keyword "if"
       |. ws
       |. symbol "("
       |= expression
       |. symbol ")"
       |= expression
       |. keyword "else"
       |= expression
       |> located

parseFunction : Parser (Located Expr)
parseFunction = succeed Function
             |= sequence
                { start = "\\"
                , separator = ","
                , end = "."
                , spaces = ws
                , item = parseIdentString
                , trailing = Forbidden
                }
             |= expression
             |> located

literal : Parser (Located Expr)
literal = oneOf [parseIdent, parseBool, parseChar, parseString, parseNumber, parseTuple, parseIf, parseFunction, parseArray]

compoundExpr : Located Expr -> Parser (Located Expr)
compoundExpr lit = loop lit (\left 
            -> succeed identity
            |= oneOf 
                [ parseInfixOp
                    |> andThen (\op-> succeed (Infix left op) |= expression |> located)
                    |> map Loop
                , parseTuple
                    |> map (Call lit)
                    |> located
                    |> map Loop
                , succeed (Index lit)
                    |. symbol "["
                    |= expression
                    |. symbol "]"
                    |> located
                    |> map Loop
                , succeed left
                    |> map Done
                ]
            |. ws
    )

parseChar : Parser (Located Expr)
parseChar = (token "'"
         |. oneOf [token "\\" |. chompIf (\_->True), chompIf (\_->True)]
         |. token "'")
         |> getChompedString
         |> map (String.slice 1 -1)
         |> map String.toList
         |> map Array.fromList
         |> map (\a-> 
                if Array.get 0 a == Just '\\' then
                    case Array.get 1 a of
                        Just 'n' -> '\n'
                        Just 't' -> '\t'
                        Just 'r' -> '\r'
                        Just c -> c
                        Nothing -> 'r'
                else 
                    Maybe.withDefault 'r' (Array.get 0 a))
         |> map CharLit
         |> located

parseString : Parser (Located Expr)
parseString = succeed StringLit
            |. token "\""
            |= loop [] (\revChunks->
                oneOf 
                    [ succeed (\chunk -> Loop (chunk::revChunks))
                        |. token "\\"
                        |= oneOf
                            [ map (\_->"\n") (token "n")
                            , map (\_->"\t") (token "t")
                            , map (\_->"\r") (token "r")
                            -- , map (\_->"\"") (token "\"")
                            , chompIf (\_->True) |> getChompedString
                            ]
                    , token "\""
                        |> map (\_->Done (String.join "" (List.reverse revChunks)))
                    , chompWhile (\c->c/='"'&&c/='\\')
                        |> getChompedString
                        |> map (\chunk->Loop(chunk::revChunks))
                    ]
            ) |> located

parseTuple : Parser (Located Expr)
parseTuple = succeed Tuple
          |= sequence
            { start = "("
            , item = expression
            , separator = ","
            , end = ")"
            , spaces = ws
            , trailing = Forbidden
            }
          |> located
          |> map (
            \expr -> case expr of
              { value } -> case value of
                  Tuple [x] -> x
                  _ -> expr
          )

chompSymbol : String -> Parser String
chompSymbol s = symbol s |> map (\_->s)

parseInfixOp : Parser String
parseInfixOp = oneOf 
    [ chompSymbol "=" |> andThen (\c->oneOf 
        [ chompSymbol ">" 
        , chompSymbol "="
        ] |> andThen (\d->succeed (c++d)))
    , chompSymbol "<" |> andThen (\c->oneOf
        [ chompSymbol "="
        , chompSymbol "|"
        , succeed ""
        ] |> andThen (\d->succeed (c++d)))
    , chompSymbol ">" |> andThen (\c->oneOf 
        [ chompSymbol "="
        , succeed ""
        ] |> andThen (\d->succeed (c++d)))
    , chompSymbol "|" |> andThen (\c->oneOf 
        [ chompSymbol ">"
        , chompSymbol "|"
        ] |> andThen (\d->succeed (c++d)))
    , chompSymbol "+" |> andThen (\c->oneOf 
        [ chompSymbol "+"
        , succeed ""
        ] |> andThen (\d->succeed (c++d)))
    , chompSymbol "-"
    , chompSymbol "*"
    , chompSymbol "/"
    , chompSymbol "^"
    , chompSymbol "%"
    , chompSymbol "!="
    , chompSymbol "&&"
    ]

parsePrefixOp : Parser String
parsePrefixOp = List.map chompSymbol ["!", "-"] |> oneOf

ws : Parser ()
ws = chompWhile (\c -> c == ' ' || c == '\n' || c == '\r' || c == '\t') |> getChompedString |> map (\_->())

parseArray : Parser (Located Expr)
parseArray = succeed ArrayLit
        |= sequence
            { start = "["
            , separator = ","
            , end = "]"
            , spaces = ws
            , item = expression
            , trailing = Forbidden
            }
        |> located

expression : Parser (Located Expr)
expression = succeed identity
          |. ws
          |= oneOf 
            [ parsePrefixOp
                |> andThen (\op->succeed (Prefix op) |= literal |> located)
            , lazy (\_->literal)
            ]
          |. ws
          |> andThen compoundExpr

parseLetBlock : Parser (Located Expr)
parseLetBlock = succeed (\(vars, e)->linesToNestedLet vars e)
                |. symbol "{"
                |. ws
                |= loop [] (\lines->
                    oneOf 
                        [ succeed identity
                            |. keyword "in"
                            |= expression
                            |> map (\expr->(List.reverse lines, expr))
                            |> map Done
                        , succeed Tuple.pair
                            |= parseIdentString
                            |. ws
                            |. symbol "="
                            |= expression
                            |. symbol ";"
                            |> located
                            |> map (\line->line::lines)
                            |> map Loop
                        ])
                |. symbol "}"

linesToNestedLet : List (Located (String, Located Expr)) -> Located Expr -> Located Expr
linesToNestedLet lines val = case lines of
    line::rest -> LetBlock line (linesToNestedLet rest val) |> locmap {start=line.end, value=(), end=val.end}
    [] -> val

-- parseTypeDef : Parser (Located Statement)
-- parseTypeDef = succeed TypeDefinition
--             |. backtrackable (keyword "typedef")
--             |. ws
--             |= parseTypeString
--             |. ws
--             |= parseType
--             |> located


-- parseTypeName : Parser (Located TypeLiteral)
-- parseTypeName = map TypeIdent parseTypeString |> located

-- parseProductType : Parser (Located TypeLiteral)
-- parseProductType = succeed ProductType
--                 |= sequence
--                     { start = "("
--                     , separator = ","
--                     , end = ")"
--                     , spaces = ws
--                     , item = lazy (\_->parseType)
--                     , trailing = Forbidden
--                     }
--                 |> located

-- typeLit : Parser (Located TypeLiteral)
-- typeLit = oneOf [parseTypeName, parseProductType]

-- compoundType lit = loop lit (\left
--         -> succeed identity
--         |= oneOf 
--             [ succeed (GenericType left)
--                 |= sequence 
--                 { start = "<"
--                 , separator = ","
--                 , end = ">"
--                 , spaces = ws
--                 , item = parseType
--                 , trailing = Forbidden
--                 }
--                 |> located
--                 |> map Loop
--             , succeed left
--                 |> map Done
--             ])
--         |. ws

-- parseType = succeed identity
--          |. ws
--          |= typeLit
--          |. ws
--          |> andThen compoundType

parse : Parser (Located Expr)
parse    = succeed (\(vars, e)->linesToNestedLet vars e)
        |= loop [] (\lines->
            succeed identity 
            |. ws
            |= oneOf 
                [ succeed (\expr->Done (List.reverse lines, expr))
                    |. keyword "main"
                    |. ws
                    |. symbol "="
                    |= expression
                    |. symbol ";"
                    |. ws
                , succeed Tuple.pair
                    |= parseIdentString
                    |. ws
                    |. symbol "="
                    |= expression
                    |. symbol ";"
                    |> located
                    |> map (\line->line::lines)
                    |> map Loop
                ])
