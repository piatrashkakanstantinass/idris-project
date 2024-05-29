module Proofs

import Types
import Data.Stream
import Data.Vect

%default total

adaptRowWorksForSimpleSchema : adaptRow (RowSchemaSeq (MkSQLSchema True SQLSString) RowSchemaEnd) [SQLQVString "hi"]
  = Just (RowValueSeq (NotNull (SQLVString "hi")) RowValueEnd)
adaptRowWorksForSimpleSchema = Refl

rowValueToListSqlQueryValue : {s : SQLRowSchema} -> (v : SQLRowValue s) -> List SQLQueryValue
rowValueToListSqlQueryValue RowValueEnd = []
rowValueToListSqlQueryValue (RowValueSeq (NotNull (SQLVString str)) y) = SQLQVString str :: rowValueToListSqlQueryValue y
rowValueToListSqlQueryValue (RowValueSeq (NotNull (SQLVInt i)) y) = SQLQVInt i :: rowValueToListSqlQueryValue y
rowValueToListSqlQueryValue (RowValueSeq (NotNull (SQLVBool x)) y) = SQLQVBool x :: rowValueToListSqlQueryValue y
rowValueToListSqlQueryValue (RowValueSeq Null y) = SQLQVNull :: rowValueToListSqlQueryValue y

adaptRowSeq :
  (x : SQLSchema) ->
  (z : SQLValue x) ->
  adaptRow y (rowValueToListSqlQueryValue w) = Just w ->
  adaptRow (RowSchemaSeq x y) (rowValueToListSqlQueryValue (RowValueSeq z w)) = Just (RowValueSeq z w)
adaptRowSeq (MkSQLSchema False SQLSString) (NotNull (SQLVString str)) prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema False SQLSInt) (NotNull (SQLVInt i)) prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema False SQLSBool) (NotNull (SQLVBool x)) prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema True SQLSString) (NotNull (SQLVString str)) prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema True SQLSString) Null prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema True SQLSInt) (NotNull (SQLVInt i)) prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema True SQLSInt) Null prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema True SQLSBool) (NotNull (SQLVBool x)) prf = rewrite prf in Refl
adaptRowSeq (MkSQLSchema True SQLSBool) Null prf = rewrite prf in Refl

adaptRowWorksInGeneralCase : (s : SQLRowSchema) -> (v : SQLRowValue s) -> adaptRow s (rowValueToListSqlQueryValue v) = Just v
adaptRowWorksInGeneralCase RowSchemaEnd RowValueEnd = Refl
adaptRowWorksInGeneralCase (RowSchemaSeq x y) (RowValueSeq z w) = adaptRowSeq x z (adaptRowWorksInGeneralCase y w)

dfInsertActuallyInserts : (df : DataFrame) -> (row : SQLRowValue df.schema) ->
  dfInsert df row = MkDataFrame df.schema df.names (df.rows ++ [(index 0 df.idStream,row)]) df.state (drop 1 df.idStream)
dfInsertActuallyInserts (MkDataFrame schema names rows state idStream) row = Refl

schemaSizeOfEnd : rowSchemaSize RowSchemaEnd = 0
schemaSizeOfEnd = Refl

schemaSizeOfSucc : rowSchemaSize (RowSchemaSeq _ s) = S (rowSchemaSize s)
schemaSizeOfSucc = Refl

-- rowValueToVect : {s : SQLRowSchema} -> SQLRowValue s -> Vect (rowSchemaSize s) (ss ** SQLValue ss)
rowValueToVectWithEmpty : rowValueToVect RowValueEnd = []
rowValueToVectWithEmpty = Refl

rowValueToVectSeq : rowValueToVect {s = RowSchemaSeq ss ns} (RowValueSeq val nv) = ((ss ** val) :: rowValueToVect nv)
rowValueToVectSeq = Refl
