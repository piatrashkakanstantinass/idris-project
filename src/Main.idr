module Main

import System.REPL
import Data.Vect
import Data.List
import Types
import Parser
import Decidable.Equality.Core

%default total

displayDataFrame : DataFrame -> String
displayDataFrame df with (dataFrameWidths df)
  displayDataFrame (MkDataFrame schema names rows) | (DfWidths (MkDataFrame schema names rows) colWidths Refl) = let
    rows' = map (\r => rowValueToVect r) rows
    in header names colWidths ++ tableRows rows' colWidths
    where

    separatorLine' : Vect k Nat -> String
    separatorLine' [] = "+"
    separatorLine' (x :: xs) = pack (['+'] ++ (replicate x '-') ++ (unpack $ separatorLine' xs))

    separatorLine: Vect k Nat -> String
    separatorLine xs = separatorLine' xs ++ "\n"

    valueStr: (values: Vect k String) -> (sizes: Vect k Nat) -> String
    valueStr [] [] = "|"
    valueStr (x :: xs) (y :: ys) = "|" ++ x ++ pack (replicate (y `minus` length x) ' ') ++ valueStr xs ys

    header : (cols: Vect k SQLName) -> (sizes: Vect k Nat) -> String
    header cols sizes = separatorLine sizes ++ valueStr (map show cols) sizes ++ "\n" ++ separatorLine sizes

    tableRows : (rows: List (Vect k (s ** SQLValue s))) -> (sizes: Vect k Nat) -> String
    tableRows [] _ = ""
    tableRows (x :: xs) sizes = valueStr (map (\(_ ** v) => show v) x) sizes ++ "\n" ++ separatorLine sizes ++ tableRows xs sizes

data QueryResult = SimpleOutput String | Table DataFrame

lookupTable : DB -> SQLName -> Either ErrorMessage DataFrame
lookupTable db name =
    case dbLookup db name of
        Nothing => Left "No such table"
        (Just y) => Right y

processQuery : DB -> Query -> Either ErrorMessage (DB, QueryResult)
processQuery db (Select x _) = lookupTable db x >>= (\t => pure (db, Table t))
processQuery db (Create name df) =
    case dbInsert db name df of
         Nothing => Left "Table exists"
         (Just newDb) => Right (newDb, SimpleOutput "Created.")
processQuery db (Insert name values) = do
    df <- lookupTable db name
    case adaptRow df.schema values of
         Nothing => Left "Schema does not match"
         Just v' => Right (dbUpdate db name (dfInsert df v'), SimpleOutput "Inserted.")

displayQueryResult : QueryResult -> String
displayQueryResult (SimpleOutput str) = str ++ "\n"
displayQueryResult (Table x) = displayDataFrame x

processInput : DB -> String -> Maybe (String, DB)
processInput db str = case parseQuery str of
                          (Left x) => Just (show x ++ "\n", db)
                          (Right x) => case processQuery db x of
                                            (Left y) => Just (show y ++ "\n", db)
                                            (Right (newDb, res)) => Just (displayQueryResult res, newDb)

covering
main : IO ()
main = putStrLn "Welcome to SQL DB" >> replWith initialDB "> " processInput
