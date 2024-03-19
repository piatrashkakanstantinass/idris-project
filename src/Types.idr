module Types

import Data.SortedMap
import Data.Vect
import Data.String

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
data SQLName : Type where
    Name : String -> SQLName

export
FromString SQLName where
    fromString s = Name s

export
Show SQLName where
    show (Name s) = s

export
Eq SQLName where
    (Name a) == (Name b) = toLower a == toLower b

export
Ord SQLName where
    (Name a) < (Name b) = toLower a < toLower b

export
length : SQLName -> Nat
length (Name str) = String.length str

public export
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

export
dbInsert : DB -> SQLName -> DataFrame -> Maybe DB
dbInsert db @ (MkDB smap) name df =
    case dbLookup db name of
         Nothing => Just (MkDB $ insert name df smap)
         (Just x) => ?idk_1

export initialDB : DB
initialDB = MkDB $ fromList [
    ("test", MkDataFrame 1 [("id", SQLSInt)] [[SQLVInt 123]])
]

public export
data Query = Select SQLName | Create SQLName DataFrame
