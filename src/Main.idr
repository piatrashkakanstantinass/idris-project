module Main

import System.REPL
import Types
import Parser

%default total

processQuery : Query -> Either ErrorMessage ()
processQuery _ = Left "not implemented"

processInput : () -> String -> Maybe (String, ())
processInput _ str = case parseQuery str of
                          (Left x) => Just (show x ++ "\n", ())
                          (Right x) => case processQuery x of
                                            (Left y) => Just (show y ++ "\n", ())
                                            (Right y) => Just ("todo\n", ())

covering
main : IO ()
main = putStrLn "Welcome to SQL DB" >> replWith () "> " processInput
