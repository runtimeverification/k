abbrev SortBool : Type := Int
abbrev SortBytes: Type := ByteArray
abbrev SortId : Type := String
abbrev SortInt : Type := Int
abbrev SortString : Type := String
abbrev SortStringBuffer : Type := String

abbrev ListHook (E : Type) : Type := List E
abbrev MapHook (K : Type) (V : Type) : Type := List (K × V)
abbrev SetHook (E : Type) : Type := List E
