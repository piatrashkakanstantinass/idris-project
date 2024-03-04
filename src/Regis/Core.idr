module Regis.Core

import Regis.Types
import Regis.Parser
import Data.List

%default total

record ProcessedGroup where
    constructor MkProcessedGroup
    groups : List String
    currGroup : List Char
%name ProcessedGroup pgrp, pgrp1, pgrp2

public export
compile : String -> Regex
compile str = case parse str of
               Nothing => Nil
               (Just x) => x

processedGroupToMatch : ProcessedGroup -> Match
processedGroupToMatch (MkProcessedGroup groups currGroup) = let
    rest = (pack currGroup :: groups)
    first = foldl (++) "" rest in
    case length rest == 1 of
        True => MkMatch rest
        False => MkMatch (first :: rest)

matchRegexSegment : RegexSegment -> List Char -> Maybe (List Nat)
matchRegexSegment (RChar c) [] = Nothing
matchRegexSegment (RChar c) (x :: xs) = Just [1]

mutual
    processChoices : Regex -> List Char -> ProcessedGroup -> List Nat -> Maybe Match
    processChoices x cs pgrp [] = Nothing
    processChoices x cs pgrp (y :: xs) = case fullMatch' x (drop y cs) (MkProcessedGroup pgrp.groups (pgrp.currGroup ++ (take y cs))) of
        Nothing => processChoices x cs pgrp xs
        Just v => Just v

    fullMatch' : Regex -> List Char -> ProcessedGroup -> Maybe Match
    fullMatch' [] [] pgrp = Just $ processedGroupToMatch pgrp
    fullMatch' [] (x :: xs) _ = Nothing
    fullMatch' (x :: xs) cs pgrp = let
        choices = matchRegexSegment x cs in
        case choices of
            Nothing => Nothing
            Just (choices') => processChoices xs cs pgrp choices'

public export
fullMatch : Regex -> String -> Maybe Match
fullMatch x str = fullMatch' x (unpack str) (MkProcessedGroup [] [])
