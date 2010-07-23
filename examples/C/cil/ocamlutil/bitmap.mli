                              (* Imperative bitmaps *)

type t
                                        (* Create a bitmap given the number 
                                         * of bits *)
val  make : int -> t
val  init : int -> (int -> bool) -> t   (* Also initialize it *)

val  size : t -> int                    (* How much space it is reserved *)

                                        (* The cardinality of a set *)
val  card  : t -> int

                                        (* Make a copy of a bitmap *)
val  clone : t -> t 

val  cloneEmpty : t -> t                (* An empty set with the same 
                                         * dimensions *)

                                        (* Set the bit *)
val  setTo : t -> int -> bool -> unit
val  test : t -> int -> bool

val  testAndSetTo: t -> int -> bool -> bool  (** Set the value and return the old 
                                        * value *)

                                        (** destructive union. The first 
                                         * element is updated. Returns true 
                                         * if any change was actually 
                                         * necessary  *)
val  union  : t -> t -> bool

                                        (* union_except livein liveout def. 
                                         * Does liveIn += (liveout - def). 
                                         * Return true if the first set was 
                                         * changed.  *)
val  union_except : t -> t -> t -> bool

                                        (* Copy the second argument onto the 
                                         * first *)
val  assign : t -> t -> unit


val  inters : t -> t -> unit
val  diff   : t -> t -> unit


val  empty  : t -> bool

val  equal  : t -> t -> bool

val  toList : t -> int list

val  iter   : (int -> unit) -> t -> unit
val  fold   : ('a -> int -> 'a) -> t -> 'a -> 'a 

