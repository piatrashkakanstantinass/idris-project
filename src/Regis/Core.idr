module Regis.Core

import Regis.Types
import Regis.Parser

%default total

compile : String -> Maybe Regex
compile = parse
