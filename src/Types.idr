module Types

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

public export
data Query = Select SQLName
