module Main

import System.REPL
import Data.Vect
import Data.List
import Types
import Parser

%default total

database : DB
database = initialDB

displayDataFrame : DataFrame -> String
displayDataFrame (MkDataFrame _ cols rows) = let
    -- These calculations ensure that every column will be only as wide as it has to be.
    headerColWidths = map headerWidth cols
    valueColWidths = map valueColWidth (valueCols rows)
    colWidths = map (\(a,b) => maximum a b) $ zip headerColWidths valueColWidths
    in header cols colWidths ++ tableRows rows colWidths
    where
    headerWidth : (SQLName, SQLSchema) -> Nat
    headerWidth (x, _) = length x

    valueCols : {k: Nat} -> List (Vect k a) -> Vect k (List a)
    valueCols xss = map toList $ transpose (fromList xss)

    valueWidth : SQLValue -> Nat
    valueWidth (SQLVString str) = length str
    valueWidth (SQLVInt i) = length $ show i
    valueWidth (SQLVBool x) = length $ show x

    valueColWidth : List SQLValue -> Nat
    valueColWidth xs = foldl maximum 0 $ map valueWidth xs

    separatorLine' : Vect k Nat -> String
    separatorLine' [] = "+"
    separatorLine' (x :: xs) = pack (['+'] ++ (replicate x '-') ++ (unpack $ separatorLine' xs))

    separatorLine: Vect k Nat -> String
    separatorLine xs = separatorLine' xs ++ "\n"

    valueStr: (values: Vect k String) -> (sizes: Vect k Nat) -> String
    valueStr [] [] = "|"
    valueStr (x :: xs) (y :: ys) = "|" ++ x ++ pack (replicate (y `minus` length x) ' ') ++ valueStr xs ys

    header : (cols: Vect k (SQLName, _)) -> (sizes: Vect k Nat) -> String
    header cols sizes = separatorLine sizes ++ valueStr (map (show . fst) cols) sizes ++ "\n" ++ separatorLine sizes

    tableRows : (rows: List (Vect k SQLValue)) -> (sizes: Vect k Nat) -> String
    tableRows [] _ = ""
    tableRows (x :: xs) sizes = valueStr (map show x) sizes ++ "\n" ++ separatorLine sizes ++ tableRows xs sizes

processQuery : Query -> Either ErrorMessage DataFrame
processQuery (Select x) =
    case dbLookup database x of
         Nothing => Left "No such table"
         (Just y) => Right y

processInput : () -> String -> Maybe (String, ())
processInput _ str = case parseQuery str of
                          (Left x) => Just (show x ++ "\n", ())
                          (Right x) => case processQuery x of
                                            (Left y) => Just (show y ++ "\n", ())
                                            (Right y) => Just (displayDataFrame y, ())

covering
main : IO ()
main = putStrLn "Welcome to SQL DB" >> replWith () "> " processInput
