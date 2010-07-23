(** Whether to split structs *)
val splitStructs : bool ref

(** Whether to simplify inside of Mem *)
val simpleMem : bool ref

(** Whether to simplify inside of AddrOf *)
val simplAddrOf : bool ref

val onlyVariableBasics : bool ref
val noStringConstantsBasics : bool ref

(** Simplify a given global *)
val doGlobal : Cil.global -> unit

val feature : Cil.featureDescr
