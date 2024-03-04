module Parser

import Data.List
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
parseName = MkParser $ \inp => let res = takeWhile (not . isSpace) inp in
    case null res of
         False => Right (drop (length res) inp, fromString $ pack res)
         True => Left "Name expected"

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
    

parseQuery' : Parser Query
parseQuery' = do
    _ <- optional parseWhitespace
    q <- parseSelect
    _ <- optional parseWhitespace
    parseEnd
    pure q

export
parseQuery : String -> Either ErrorMessage Query
parseQuery str = map snd $ parse parseQuery' (unpack str)
                                