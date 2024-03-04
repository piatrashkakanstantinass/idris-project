module Regis.Types

import Data.Vect

%default total

public export
data RegexSegment : Type where
  RChar : Char -> RegexSegment

public export
data Regex : Type where
  Nil : Regex
  (::) : (x : RegexSegment) -> (xs : Regex) -> Regex

public export
record
Match where
  constructor MkMatch
  groups : List String

export
Cast (List RegexSegment) Regex where
  cast [] = Nil
  cast (x :: xs) = x :: cast xs
