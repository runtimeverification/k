/-
K Prelude in Lean 4

Functions with the `hook` attribute need to have a manual implementation in the backends.
This file contains the Lean 4 definitions of the hooked functions in `domains.md`.

Currently we translate hooked functions as uninterpreted functions together with axioms asserting their behavior.
The current definition can be put into three levels:

1. Signature Level:
The signature of the hooks, this includes aliases for Sorts and function symbols for hooked functions.

2. Rule Level:
The behavior of the uninterpreted symbols can be asserted through axioms or theorems.
Inconsistencies can arise from them, so it falls under the user to make sure axioms are consistent and/or theorems provable.

3. Simplification Level:
With the theory defined through function rules, simplifications can be stated as theorems.
These theorems should be provable directly from the function rules and the semantics of the Sorts.
 -/

-- Basic K types
abbrev SortBool         : Type := Int
abbrev SortBytes        : Type := ByteArray
abbrev SortId           : Type := String
abbrev SortInt          : Type := Int
abbrev SortString       : Type := String
abbrev SortStringBuffer : Type := String

namespace MapHookDef
/-
The `Map` sort represents a generalized associative array.
Each key can be paired with an arbitrary value, and can be used to reference its associated value.
Multiple bindings for the same key are not allowed.
Note that both keys and values will always be KItems.
 -/

-- Signature to be instantiated by map implementations
structure MapHookSig (K V : Type) where
  map        : Type -- Carrier, such as List (KItem × KItem)
  unit       : map
  cons       : K → V → map → map
  lookup     : map → K → Option V
  lookup?    : map → K → V -- lookup with default
  update     : K → V → map → map
  delete     : map → K → map
  concat     : map → map → Option map
  difference : map → map → map
  updateMap  : map → map → map
  removeAll  : map → List K → map
  keys       : map → List K
  in_keys    : map → K → Bool
  values     : map → List V
  size       : map → Nat
  includes   : map → map → Bool -- map inclusion
  choice     : map → K -- arbitrary key from a map
  nodup      : forall al : map, List.Nodup (keys al)

-- We use axioms to have uninterpreted functions
variable (K V : Type)
axiom mapCAx       : Type -- Map Carrier
axiom unitAx       : mapCAx
axiom consAx       : K → V → mapCAx → mapCAx
axiom lookupAx     : mapCAx → K → Option V
axiom lookupAx?    : mapCAx → K → V -- lookup with default
axiom updateAx     : K → V → mapCAx → mapCAx
axiom deleteAx     : mapCAx → K → mapCAx
axiom concatAx     : mapCAx → mapCAx → Option mapCAx
axiom differenceAx : mapCAx → mapCAx → mapCAx
axiom updateMapAx  : mapCAx → mapCAx → mapCAx
axiom removeAllAx  : mapCAx → List K → mapCAx
axiom keysAx       : mapCAx → List K
axiom in_keysAx    : mapCAx → K → Bool
axiom valuesAx     : mapCAx → List V
axiom sizeAx       : mapCAx → Nat
axiom includesAx   : mapCAx → mapCAx → Bool -- map inclusion
axiom choiceAx     : mapCAx → K -- arbitrary key from a map
axiom nodupAx      : forall m, List.Nodup (keysAx K m)

-- Uninterpreted Map implementation
noncomputable def MapHook (K V : Type) : MapHookSig K V :=
  { map        := mapCAx,
    unit       := unitAx,
    cons       := consAx K V,
    lookup     := lookupAx K V,
    lookup?    := lookupAx? K V,
    update     := updateAx K V,
    delete     := deleteAx K,
    concat     := concatAx,
    difference := differenceAx,
    updateMap  := updateMapAx,
    removeAll  := removeAllAx K,
    keys       := keysAx K,
    in_keys    := in_keysAx K,
    values     := valuesAx V,
    size       := sizeAx,
    includes   := includesAx,
    choice     := choiceAx K,
    nodup      := nodupAx K }

end MapHookDef

namespace SetHookDef
/-
Implementation of immutable, associative, commutative sets of `KItem`.
The sets are nilpotent, i.e., the concatenation of two sets containing elements in common is `#False` (note however, this may be silently allowed during concrete execution).
If you intend to add an element to a set that might already be present in the set, use the `|Set` operator instead.
 -/

structure SetHookSig (T : Type) where
  set : Type -- Carrier, such as `T → Prop`
  unit : set
  concat : set → set → Option set
  setItem : T → set
  union : set → set → set
  intersection : set → set → set
  difference : set → set → set
  inSet : T → set → Bool
  inclusion : set → set → Bool
  size : set → Int
  choice : set → T

variable (T : Type)
axiom setCAx         : Type
axiom unitAx         : setCAx
axiom concatAx       : setCAx → setCAx → Option setCAx
axiom setItemAx      : T → setCAx
axiom unionAx        : setCAx → setCAx → setCAx
axiom intersectionAx : setCAx → setCAx → setCAx
axiom differenceAx   : setCAx → setCAx → setCAx
axiom inSetAx        : T → setCAx → Bool
axiom inclusionAx    : setCAx → setCAx → Bool
axiom sizeAx         : setCAx → Int
axiom choiceAx       : setCAx → T

noncomputable def SetHook (T : Type) : SetHookSig T :=
  { set          := setCAx,
    unit         := unitAx,
    concat       := concatAx,
    setItem      := setItemAx T,
    union        := unionAx,
    intersection := intersectionAx,
    difference   := differenceAx,
    inSet        := inSetAx T,
    inclusion    := inclusionAx,
    size         := sizeAx,
    choice       := choiceAx T }

end SetHookDef

class Inj (From To : Type) : Type where
  inj (x : From) : To

def inj {From To : Type} [inst : Inj From To] := inst.inj
