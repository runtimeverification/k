abbrev SortBool : Type := Int
abbrev SortBytes: Type := ByteArray
abbrev SortId : Type := String
abbrev SortInt : Type := Int
abbrev SortString : Type := String
abbrev SortStringBuffer : Type := String

class Inj (From To : Type) : Type where
  inj (x : From) : To

def inj {From To : Type} [inst : Inj From To] := inst.inj
