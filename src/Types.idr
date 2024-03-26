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

export
Eq SQLSchema where
    SQLSString == SQLSString = True
    SQLSInt == SQLSInt = True
    SQLSBool == SQLSBool = True
    _ == _ = False

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
         (Just _) => Nothing

export
dbUpdate : DB -> SQLName -> DataFrame -> DB
dbUpdate db @ (MkDB smap) name df = MkDB $ updateExisting (\_ => df) name smap

export
dfInsert : (df: DataFrame) -> Vect (df.colSize) SQLValue -> DataFrame
dfInsert (MkDataFrame colSize cols rows) xs = MkDataFrame colSize cols $ reverse (xs :: rows)

export initialDB : DB
initialDB = MkDB $ fromList [
    ("test", MkDataFrame 1 [("id", SQLSInt)] [[SQLVInt 123]])
]

export
sqlValueToSchema : SQLValue -> SQLSchema
sqlValueToSchema (SQLVString _) = SQLSString
sqlValueToSchema (SQLVInt i) = SQLSInt
sqlValueToSchema (SQLVBool x) = SQLSBool

-- sqlValueMatchingSchema : SQLValue -> SQLSchema -> Bool
-- sqlValueMatchingSchema (SQLVString _) SQLSString = True
-- sqlValueMatchingSchema (SQLVInt _) SQLSInt = True
-- sqlValueMatchingSchema (SQLVBool _) SQLSBool = True
-- sqlValueMatchingSchema _ _ = False

public export
data Query = Select SQLName | Create SQLName DataFrame | Insert SQLName (List SQLValue)
