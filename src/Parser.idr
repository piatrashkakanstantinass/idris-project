module Parser

import Data.List
import Data.Vect
import Data.String
import Types

%default total

data Parser a = MkParser (List Char -> Either ErrorMessage (List Char, a))
%name Parser p, p1, p2, p3

parse : Parser a -> List Char -> Either ErrorMessage (List Char, a)
parse (MkParser f) cs = f cs

Functor Parser where
    map f a = MkParser $ \inp => case parse a inp of
                                      (Left x) => Left x
                                      (Right (x, y)) => Right (x, f y)

Applicative Parser where
    fa <*> aa = MkParser $ \inp => case parse fa inp of
                                        (Left x) => Left x
                                        (Right (x, f)) => parse (map f aa) x
    pure a = MkParser $ \inp => Right (inp, a)

Monad Parser where
    a >>= f = MkParser $ \inp => case parse a inp of
                                      (Left x) => Left x
                                      (Right (x, y)) => parse (f y) x

Alternative Parser where
    a <|> b = MkParser $ \inp => case parse a inp of
                                      (Left x) => parse b inp
                                      (Right x) => Right x
    empty = MkParser $ \_ => Left "Error"

optional : Alternative f => f a -> f (Maybe a)
optional x = map Just x <|> pure Nothing

parseChar : Char -> Parser Char
parseChar c = let err = "\{show c} expected"
    in MkParser $ \inp =>
        case inp of
            (x :: xs) => if x == c then Right (xs, c) else Left $ fromString err
            [] => Left $ fromString err

parseWhitespace : Parser (List Char)
parseWhitespace = MkParser $ \inp =>
    let res = takeWhile isSpace inp
    in case null res of
            False => Right (drop (length res) inp, res)
            True => Left "Whitespace expected"

parseEnd : Parser ()
parseEnd = MkParser $ \inp => case null inp of
                                   False => Left "End expected"
                                   True => Right (inp, ())

parseIgnoreCaseString : String -> Parser String
parseIgnoreCaseString str = MkParser $ \inp => case map toLower (take (length str) inp) == map toLower (unpack str) of
                                                    False => Left $ fromString "\{str} expected"
                                                    True => Right (drop (length str) inp, pack $ take (length str) inp)

parseName : Parser SQLName
parseName = MkParser $ \inp => let res = takeWhile isAlphaNum inp in
    case null res of
         False => Right (drop (length res) inp, fromString $ pack res)
         True => Left "Name expected"

parseLeftRight : (parserLeft: Parser a) -> (parserRight: Parser b) -> (parser: Parser c) -> Parser c
parseLeftRight parserLeft parserRight parser = do
    _ <- parserLeft
    res <- parser
    _ <- parserRight
    pure res

parseInOptSpace : Parser a -> Parser a
parseInOptSpace p = do
    _ <- optional parseWhitespace
    res <- p
    _ <- optional parseWhitespace
    pure res

parseInParantheses : Parser a -> Parser a
parseInParantheses p = parseLeftRight (parseInOptSpace $ parseChar '(') (parseInOptSpace $ parseChar ')') p

parseSeparatedBy : (by: Parser a) -> (p: Parser b) -> Parser (List b)
parseSeparatedBy by p = MkParser $ \inp =>
    case parse p inp of
         (Left x) => Right (inp, [])
         (Right (x, y)) => let (inp', res) = parseSeparatedBy' (length inp) [y] x
            in Right (inp', reverse res)
    where
        parseSeparatedBy' : Nat -> List b -> List Char -> (List Char, List b)
        parseSeparatedBy' Z xs inp = (inp, xs)
        parseSeparatedBy' (S k) xs inp = case parse ((map (\x => ()) by) >> p) inp of
                                       (Left x) => (inp, xs)
                                       (Right (x, y)) => parseSeparatedBy' k (y :: xs) x

parseCommaSeparated: Parser a -> Parser (List a)
parseCommaSeparated p = parseSeparatedBy (parseInOptSpace $ parseChar ',') p

parseSelect : Parser Query
parseSelect = do
    _ <- parseIgnoreCaseString "select"
    _ <- parseWhitespace
    _ <- parseIgnoreCaseString "*"
    _ <- parseWhitespace
    _ <- parseIgnoreCaseString "from"
    _ <- parseWhitespace
    name <- parseName
    pure $ Select name

parseSQLSchema: Parser SQLSchema
parseSQLSchema = parseName >>= \name => MkParser $ \inp =>
    if name == "string" then Right (inp, SQLSString)
    else if name == "int" then Right (inp, SQLSInt)
    else if name == "bool" then Right (inp, SQLSBool)
    else Left "SQL type expected"

parseColumnDecl : Parser (SQLSchema, SQLName)
parseColumnDecl = do
    name <- parseName
    _ <- parseWhitespace
    schema <- parseSQLSchema
    pure (schema, name)

parseInt : Parser Int
parseInt = MkParser $ \inp => let
    cs = takeWhile isDigit inp
    parsedValue = parseInteger (pack cs)
    in case parsedValue of
        Nothing => Left "Int value expected"
        (Just v) => Right (drop (length cs) inp, v)

parseSQLVString : Parser (s ** SQLValue s)
parseSQLVString = parseLeftRight (parseChar '"') (parseChar '"') (MkParser $ \inp =>
    let res = takeWhile (\c => not (isSpace c || c == ',' || c == '"')) inp
    in case null res of
        True => Left "SQL String value expected"
        False => Right (drop (length res) inp, (SQLSString ** SQLVString (pack res))))

parseSQLVInt : Parser (s ** SQLValue s)
parseSQLVInt = do
    i <- parseInt
    pure $ (SQLSInt ** SQLVInt i)

parseSQLVBool : Parser (s ** SQLValue s)
parseSQLVBool = (do
    _ <- parseIgnoreCaseString "false"
    pure $ (SQLSBool ** SQLVBool False)) <|> (do
        _ <- parseIgnoreCaseString "true"
        pure $ (SQLSBool ** SQLVBool True))

parseSQLValue : Parser (s ** SQLValue s)
parseSQLValue = parseSQLVString <|> parseSQLVInt <|> parseSQLVBool

parseColumnList : Parser (List (SQLSchema, SQLName))
parseColumnList = parseCommaSeparated parseColumnDecl

parseValueList : Parser (List (s ** SQLValue s))
parseValueList = parseCommaSeparated parseSQLValue
    
parseCreate : Parser Query
parseCreate = do
    _ <- parseIgnoreCaseString "create"
    _ <- parseWhitespace
    _ <- parseIgnoreCaseString "table"
    _ <- parseWhitespace
    name <- parseName
    _ <- optional parseWhitespace
    cols <- parseInParantheses parseColumnList
    (let (s ** names) = schemaAndNameFromList cols
        in pure $ Create name (MkDataFrame s names []))

parseInsert : Parser Query
parseInsert = do
    _ <- parseIgnoreCaseString "insert"
    _ <- parseWhitespace
    _ <- parseIgnoreCaseString "into"
    _ <- parseWhitespace
    name <- parseName
    _ <- parseWhitespace
    _ <- parseIgnoreCaseString "values"
    _ <- optional parseWhitespace
    values <- parseInParantheses parseValueList
    pure $ Insert name (rowValueFromList values)


parseQuery' : Parser Query
parseQuery' = do
    _ <- optional parseWhitespace
    q <- parseSelect <|> parseCreate <|> parseInsert
    _ <- optional parseWhitespace
    parseEnd
    pure q

export
parseQuery : String -> Either ErrorMessage Query
parseQuery str = map snd $ parse parseQuery' (unpack str)
                                