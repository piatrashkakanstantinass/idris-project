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
data SQLPrimitiveSchema = SQLSString | SQLSInt | SQLSBool

export
Eq SQLPrimitiveSchema where
    SQLSString == SQLSString = True
    SQLSInt == SQLSInt = True
    SQLSBool == SQLSBool = True
    _ == _ = False

public export
data SQLPrimitiveValue : SQLPrimitiveSchema -> Type where
    SQLVString : String -> SQLPrimitiveValue SQLSString
    SQLVInt : Int -> SQLPrimitiveValue SQLSInt
    SQLVBool : Bool -> SQLPrimitiveValue SQLSBool

export
Show (SQLPrimitiveValue _) where
    show (SQLVString str) = str
    show (SQLVInt i) = show i
    show (SQLVBool x) = show x

public export
record SQLSchema where
    constructor MkSQLSchema
    nullable : Bool
    primitiveSchema : SQLPrimitiveSchema

public export
data SQLValue : SQLSchema -> Type where
    NotNull : SQLPrimitiveValue s -> SQLValue (MkSQLSchema _ s)
    Null : SQLValue (MkSQLSchema True _)

export
Show (SQLValue _) where
    show (NotNull x) = show x
    show Null = "null"

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
data DataFrameState = Unlocked | Locked

public export
record DataFrame where
    constructor MkDataFrame
    schema : SQLRowSchema
    names : Vect (rowSchemaSize schema) SQLName
    rows: List (SQLRowValue schema)
    state : DataFrameState

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
dfInsert (MkDataFrame schema names rows st) x = MkDataFrame schema names (rows ++ [x]) st

export initialDB : DB
initialDB = MkDB $ fromList [
    ("test", (MkDataFrame (RowSchemaSeq (MkSQLSchema True SQLSInt) RowSchemaEnd) ["id"] [(RowValueSeq (NotNull (SQLVInt 123)) RowValueEnd)] Unlocked))
]

public export
data SQLQueryValue = SQLQVString String | SQLQVInt Int | SQLQVBool Bool | SQLQVNull

adaptSchema : (s : SQLSchema) -> SQLQueryValue -> Maybe (SQLValue s)
adaptSchema (MkSQLSchema nullable SQLSString) (SQLQVString str) = Just $ NotNull (SQLVString str)
adaptSchema (MkSQLSchema nullable SQLSInt) (SQLQVInt i) = Just $ NotNull (SQLVInt i)
adaptSchema (MkSQLSchema nullable SQLSBool) (SQLQVBool b) = Just $ NotNull (SQLVBool b)
adaptSchema (MkSQLSchema True _) SQLQVNull = Just $ Null
adaptSchema _ _ = Nothing

export
adaptRow : (s : SQLRowSchema) -> List SQLQueryValue -> Maybe (SQLRowValue s)
adaptRow RowSchemaEnd [] = Just RowValueEnd
adaptRow RowSchemaEnd _ = Nothing
adaptRow (RowSchemaSeq (MkSQLSchema True _) y) [] = case adaptRow y [] of
                                      Nothing => Nothing
                                      (Just z) => Just (RowValueSeq Null z)
adaptRow (RowSchemaSeq _ _) [] = Nothing
adaptRow (RowSchemaSeq x y) (z :: xs) = case adaptSchema x z of
                                             Nothing => Nothing
                                             (Just w) => case adaptRow y xs of
                                                              Nothing => Nothing
                                                              (Just v) => Just (RowValueSeq w v)
public export
data SelectCols = All | SpecificCols (List SQLName)

public export
data Query = Select SQLName SelectCols | Create SQLName DataFrame | Insert SQLName (List SQLQueryValue) | LockChange SQLName DataFrameState

public export
data DataFrameWidths : DataFrame -> Type where
    DfWidths : (df : DataFrame) -> Vect n Nat -> n = rowSchemaSize df.schema -> DataFrameWidths df

valueCols : {k: Nat} -> List (Vect k a) -> Vect k (List a)
valueCols xss = map toList $ transpose (fromList xss)

valueWidth : (s ** SQLValue s) -> Nat
valueWidth (_ ** v) = length $ show v

valueColWidth : List (s ** SQLValue s) -> Nat
valueColWidth xs = foldl maximum 0 $ map valueWidth xs

export
dataFrameWidths : (df : DataFrame) -> DataFrameWidths df
dataFrameWidths d @ (MkDataFrame schema names rows st) = let
    headerColWidths = map length names
    rows' = map (\r => rowValueToVect r) rows
    valueColWidths = map valueColWidth (valueCols rows')
    colWidths = map (\(a,b) => maximum a b) $ zip headerColWidths valueColWidths
    in DfWidths d colWidths Refl
