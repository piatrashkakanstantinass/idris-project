module Types

import Data.SortedMap
import Data.Vect
import Data.String
import Decidable.Equality.Core
import Decidable.Equality

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
data SQLPrimitiveSchema = SQLSString | SQLSInt | SQLSBool

export
Eq SQLPrimitiveSchema where
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

DecEq SQLPrimitiveSchema where
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
data SQLPrimitiveValue : SQLPrimitiveSchema -> Type where
    SQLVString : String -> SQLPrimitiveValue SQLSString
    SQLVInt : Int -> SQLPrimitiveValue SQLSInt
    SQLVBool : Bool -> SQLPrimitiveValue SQLSBool
    SQLVNull : SQLPrimitiveValue _

export
Show (SQLPrimitiveValue _) where
    show (SQLVString str) = str
    show (SQLVInt i) = show i
    show (SQLVBool x) = show x
    show SQLVNull = "null"

public export
record SQLSchema where
    constructor MkSQLSchema
    nullable : Bool
    primitiveSchema : SQLPrimitiveSchema

DecEq SQLSchema where
    decEq (MkSQLSchema nullable1 primitiveSchema1) (MkSQLSchema nullable2 primitiveSchema2) =
        case decEq nullable1 nullable2 of
             (Yes Refl) => case decEq primitiveSchema1 primitiveSchema2 of
                               (Yes Refl) => Yes Refl
                               (No contra) => No (\Refl => contra Refl)
             (No contra) => No (\Refl => contra Refl)

public export
data SQLValue : SQLSchema -> Type where
    NotNull : SQLPrimitiveValue s -> SQLValue (MkSQLSchema _ s)

export
Show (SQLValue _) where
    show (NotNull x) = show x

public export
data SQLRowSchema = RowSchemaEnd | RowSchemaSeq SQLSchema SQLRowSchema

Uninhabited (RowSchemaEnd = (RowSchemaSeq _ _)) where
    uninhabited Refl impossible

Uninhabited ((RowSchemaSeq _ _) =  RowSchemaEnd) where
    uninhabited Refl impossible

headUnequalSQLRow : (contr : x = y -> Void) -> (xs : SQLRowSchema) -> (ys : SQLRowSchema) -> ((RowSchemaSeq x xs) = (RowSchemaSeq y ys) -> Void)
headUnequalSQLRow contr _ _ Refl = contr Refl

tailUnequalSQLRow : (xs : SQLRowSchema) -> (ys : SQLRowSchema) -> (contr : xs = ys -> Void) -> ((RowSchemaSeq x xs) = (RowSchemaSeq y ys) -> Void)
tailUnequalSQLRow _ _ contr Refl = contr Refl

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
dfInsert (MkDataFrame schema names rows) x = MkDataFrame schema names $ rows ++ [x]

export initialDB : DB
initialDB = MkDB $ fromList [
    ("test", (MkDataFrame (RowSchemaSeq (MkSQLSchema True SQLSInt) RowSchemaEnd) ["id"] [(RowValueSeq (NotNull (SQLVInt 123)) RowValueEnd)]))
]

public export
data SQLQueryValue = SQLQVString String | SQLQVInt Int | SQLQVBool Bool | SQLQVNull

adaptSchema : (s : SQLSchema) -> SQLQueryValue -> Maybe (SQLValue s)
adaptSchema (MkSQLSchema nullable SQLSString) (SQLQVString str) = Just $ NotNull (SQLVString str)
adaptSchema (MkSQLSchema nullable SQLSInt) (SQLQVInt i) = Just $ NotNull (SQLVInt i)
adaptSchema (MkSQLSchema nullable SQLSBool) (SQLQVBool b) = Just $ NotNull (SQLVBool b)
adaptSchema (MkSQLSchema True _) SQLQVNull = Just $ NotNull SQLVNull
adaptSchema _ _ = Nothing

export
adaptRow : (s : SQLRowSchema) -> List SQLQueryValue -> Maybe (SQLRowValue s)
adaptRow RowSchemaEnd [] = Just RowValueEnd
adaptRow RowSchemaEnd _ = Nothing
adaptRow (RowSchemaSeq (MkSQLSchema True _) y) [] = case adaptRow y [] of
                                      Nothing => Nothing
                                      (Just z) => Just (RowValueSeq (NotNull SQLVNull) z)
adaptRow (RowSchemaSeq _ _) [] = Nothing
adaptRow (RowSchemaSeq x y) (z :: xs) = case adaptSchema x z of
                                             Nothing => Nothing
                                             (Just w) => case adaptRow y xs of
                                                              Nothing => Nothing
                                                              (Just v) => Just (RowValueSeq w v)

public export
data Query = Select SQLName | Create SQLName DataFrame | Insert SQLName (List SQLQueryValue)
