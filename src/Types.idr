module Types

import Data.SortedMap
import Data.Vect

%default total

export
ErrorMessage : Type
ErrorMessage = String

export
FromString ErrorMessage where
    fromString = id

export
Show ErrorMessage where
    show = id

export
SQLName : Type
SQLName = String

export
FromString SQLName where
    fromString = id

export
Show SQLName where
    show = id

export
length : SQLName -> Nat
length str = String.length str

export
data SQLSchema = SQLSString | SQLSInt | SQLSBool

public export
data SQLValue = SQLVString String | SQLVInt Int | SQLVBool Bool

export
Show SQLValue where
    show (SQLVString str) = str
    show (SQLVInt i) = show i
    show (SQLVBool x) = show x

public export
record DataFrame where
    constructor MkDataFrame
    colSize: Nat
    cols : Vect colSize (SQLName, SQLSchema)
    rows: List (Vect colSize SQLValue)

export
data DB = MkDB (SortedMap SQLName DataFrame)

export
dbLookup : DB -> SQLName -> Maybe DataFrame
dbLookup (MkDB x) str = lookup str x

export initialDB : DB
initialDB = MkDB $ fromList [
    ("test", MkDataFrame 1 [("id", SQLSInt)] [[SQLVInt 123]])
]

public export
data Query = Select SQLName
