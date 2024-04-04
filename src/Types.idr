module Types

import Data.SortedMap
import Data.Vect
import Data.String
import Decidable.Equality.Core

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

Uninhabited (SQLSString = SQLSInt) where
    uninhabited Refl impossible

Uninhabited (SQLSString = SQLSBool) where
    uninhabited Refl impossible

Uninhabited (SQLSInt = SQLSString) where
    uninhabited Refl impossible

Uninhabited (SQLSInt = SQLSBool) where
    uninhabited Refl impossible

Uninhabited (SQLSBool = SQLSString) where
    uninhabited Refl impossible

Uninhabited (SQLSBool = SQLSInt) where
    uninhabited Refl impossible

DecEq SQLSchema where
    decEq SQLSString SQLSString = Yes Refl
    decEq SQLSString SQLSInt = No absurd
    decEq SQLSString SQLSBool = No absurd
    decEq SQLSInt SQLSString = No absurd
    decEq SQLSInt SQLSInt = Yes Refl
    decEq SQLSInt SQLSBool = No absurd
    decEq SQLSBool SQLSString = No absurd
    decEq SQLSBool SQLSInt = No absurd
    decEq SQLSBool SQLSBool = Yes Refl

public export
data SQLValue : SQLSchema -> Type where
    SQLVString : String -> SQLValue SQLSString
    SQLVInt : Int -> SQLValue SQLSInt
    SQLVBool : Bool -> SQLValue SQLSBool

export
Show (SQLValue _) where
    show (SQLVString str) = str
    show (SQLVInt i) = show i
    show (SQLVBool x) = show x

public export
data SQLRowSchema = RowSchemaEnd | RowSchemaSeq SQLSchema SQLRowSchema

Uninhabited (RowSchemaEnd = (RowSchemaSeq _ _)) where
    uninhabited Refl impossible

Uninhabited ((RowSchemaSeq _ _) =  RowSchemaEnd) where
    uninhabited Refl impossible

headUnequalSQLRow : (contr : x = y -> Void) -> (xs : SQLRowSchema) -> (ys : SQLRowSchema) -> ((RowSchemaSeq x xs) = (RowSchemaSeq y ys) -> Void)
headUnequalSQLRow contr RowSchemaEnd RowSchemaEnd Refl = contr Refl
headUnequalSQLRow contr (RowSchemaSeq x y) (RowSchemaSeq x y) Refl = case x of { SQLSString => contr Refl ; SQLSInt => contr Refl ; SQLSBool => contr Refl }

tailUnequalSQLRow : (xs : SQLRowSchema) -> (ys : SQLRowSchema) -> (contr : xs = ys -> Void) -> ((RowSchemaSeq x xs) = (RowSchemaSeq y ys) -> Void)
tailUnequalSQLRow RowSchemaEnd RowSchemaEnd contr Refl = contr Refl
tailUnequalSQLRow (RowSchemaSeq x y) (RowSchemaSeq x y) contr Refl = case x of { SQLSString => contr Refl ; SQLSInt => contr Refl ; SQLSBool => contr Refl }

export
DecEq SQLRowSchema where
    decEq RowSchemaEnd RowSchemaEnd = Yes Refl
    decEq RowSchemaEnd (RowSchemaSeq x y) = No absurd
    decEq (RowSchemaSeq x y) RowSchemaEnd = No absurd
    decEq (RowSchemaSeq x y) (RowSchemaSeq z w) = case decEq x z of
                                                       (Yes Refl) => case decEq y w of
                                                                         (Yes Refl) => Yes Refl
                                                                         (No contra) => No (tailUnequalSQLRow y w contra)
                                                       (No contra) => No (headUnequalSQLRow contra y w)

public export
rowSchemaSize : SQLRowSchema -> Nat
rowSchemaSize RowSchemaEnd = 0
rowSchemaSize (RowSchemaSeq _ y) = 1 + rowSchemaSize y

export
schemaAndNameFromList : List (SQLSchema, SQLName) -> (schema ** Vect (rowSchemaSize schema) SQLName)
schemaAndNameFromList [] = (RowSchemaEnd ** [])
schemaAndNameFromList (x :: xs) = let (nschema ** nnames) = schemaAndNameFromList xs
    in (RowSchemaSeq (fst x) nschema ** (snd x :: nnames))

public export
data SQLRowValue : SQLRowSchema -> Type where
    RowValueEnd : SQLRowValue RowSchemaEnd
    RowValueSeq : SQLValue s -> SQLRowValue rest -> SQLRowValue (RowSchemaSeq s rest)

export
rowValueFromList : List (schema ** SQLValue schema) -> (schema' ** SQLRowValue schema')
rowValueFromList [] = (RowSchemaEnd ** RowValueEnd)
rowValueFromList ((schema ** x) :: xs) = let (nschema ** nvalues) = rowValueFromList xs
    in (RowSchemaSeq schema nschema ** RowValueSeq x nvalues)

public export
rowValueToVect : {s : SQLRowSchema} -> SQLRowValue s -> Vect (rowSchemaSize s) (ss ** SQLValue ss)
rowValueToVect RowValueEnd = []
rowValueToVect {s = RowSchemaSeq sss _} (RowValueSeq x y) = (sss ** x) :: rowValueToVect y

public export
record DataFrame where
    constructor MkDataFrame
    schema : SQLRowSchema
    names : Vect (rowSchemaSize schema) SQLName
    rows: List (SQLRowValue schema)

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
dfInsert : (df: DataFrame) -> SQLRowValue df.schema -> DataFrame
dfInsert (MkDataFrame schema names rows) x = MkDataFrame schema names $ reverse (x :: rows)

export initialDB : DB
initialDB = MkDB $ fromList [
    ("test", (MkDataFrame (RowSchemaSeq SQLSInt RowSchemaEnd) ["id"] [(RowValueSeq (SQLVInt 123) RowValueEnd)]))
]

public export
data Query = Select SQLName | Create SQLName DataFrame | Insert SQLName (rowSchema ** SQLRowValue rowSchema)
