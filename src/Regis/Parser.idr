module Regis.Parser

import Text.Parser as P
import Text.Parser.Core as PC
import Regis.Types

%default total

Rule: Type -> Type
Rule x = PC.Grammar () Char True x

Rule1: Type -> Type
Rule1 x = PC.Grammar () Char False x

rChar : Rule RegexSegment
rChar = terminal "Char expected" (\c => Just $ RChar c)

regexSegment : Rule RegexSegment
regexSegment = rChar

rand : Regex
rand = []

regex : Rule1 Regex
regex = do
    segments <- many regexSegment
    pure $ cast segments

public export
parse : String -> Maybe Regex
parse str = case PC.parse regex (map irrelevantBounds $ unpack str) of
                 Left _ => Nothing
                 Right (r,_) => Just r
