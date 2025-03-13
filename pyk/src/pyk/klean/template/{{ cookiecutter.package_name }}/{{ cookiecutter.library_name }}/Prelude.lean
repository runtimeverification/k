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
abbrev SortBool         : Type := Bool
abbrev SortBytes        : Type := ByteArray
abbrev SortId           : Type := String
abbrev SortInt          : Type := Int
abbrev SortString       : Type := String
abbrev SortStringBuffer : Type := String

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
namespace MapHookDef
  variable (K V : Type)
  def mapCAx        := List (K × V) -- Map Carrier
  axiom unitAx       : mapCAx K V
  axiom consAx       : K → V → mapCAx K V → mapCAx K V
  axiom lookupAx     : mapCAx K V → K → Option V
  axiom lookupAx?    : mapCAx K V → K → V -- lookup with default
  axiom updateAx     : K → V → mapCAx K V → mapCAx K V
  axiom deleteAx     : mapCAx K V → K → mapCAx K V
  axiom concatAx     : mapCAx K V → mapCAx K V → Option (mapCAx K V)
  axiom differenceAx : mapCAx K V → mapCAx K V → mapCAx K V
  axiom updateMapAx  : mapCAx K V → mapCAx K V → mapCAx K V
  axiom removeAllAx  : mapCAx K V → List K → mapCAx K V
  axiom keysAx       : mapCAx K V → List K
  axiom in_keysAx    : mapCAx K V → K → Bool
  axiom valuesAx     : mapCAx K V → List V
  axiom sizeAx       : mapCAx K V → Nat
  axiom includesAx   : mapCAx K V → mapCAx K V → Bool -- map inclusion
  axiom choiceAx     : mapCAx K V → K -- arbitrary key from a map
  axiom nodupAx      : forall m, List.Nodup (keysAx K V m)
end MapHookDef

-- Uninterpreted Map implementation
noncomputable def MapHook (K V : Type) : MapHookSig K V :=
  { map        := MapHookDef.mapCAx K V,
    unit       := MapHookDef.unitAx K V,
    cons       := MapHookDef.consAx K V,
    lookup     := MapHookDef.lookupAx K V,
    lookup?    := MapHookDef.lookupAx? K V,
    update     := MapHookDef.updateAx K V,
    delete     := MapHookDef.deleteAx K V,
    concat     := MapHookDef.concatAx K V,
    difference := MapHookDef.differenceAx K V,
    updateMap  := MapHookDef.updateMapAx K V,
    removeAll  := MapHookDef.removeAllAx K V,
    keys       := MapHookDef.keysAx K V,
    in_keys    := MapHookDef.in_keysAx K V,
    values     := MapHookDef.valuesAx K V,
    size       := MapHookDef.sizeAx K V,
    includes   := MapHookDef.includesAx K V,
    choice     := MapHookDef.choiceAx K V,
    nodup      := MapHookDef.nodupAx K V}

instance {K V : Type} [BEq K] [BEq V]: BEq (MapHook K V).map where
  beq := List.beq

/-
Implementation of immutable, associative, commutative sets of `KItem`.
The sets are nilpotent, i.e., the concatenation of two sets containing elements in common is `#False` (note however, this may be silently allowed during concrete execution).
If you intend to add an element to a set that might already be present in the set, use the `|Set` operator instead.
 -/

structure SetHookSig (T : Type) where
  set          : Type -- Carrier, such as `T → Prop`
  unit         : set
  concat       : set → set → Option set
  element      : T → set
  union        : set → set → set
  intersection : set → set → set
  difference   : set → set → set
  inSet        : T → set → Bool
  inclusion    : set → set → Bool
  size         : set → Int
  choice       : set → T

namespace SetHookDef
  variable (T : Type)
  axiom setCAx         : Type
  axiom unitAx         : setCAx
  axiom concatAx       : setCAx → setCAx → Option setCAx
  axiom elementAx      : T → setCAx
  axiom unionAx        : setCAx → setCAx → setCAx
  axiom intersectionAx : setCAx → setCAx → setCAx
  axiom differenceAx   : setCAx → setCAx → setCAx
  axiom inSetAx        : T → setCAx → Bool
  axiom inclusionAx    : setCAx → setCAx → Bool
  axiom sizeAx         : setCAx → Int
  axiom choiceAx       : setCAx → T
end SetHookDef

noncomputable def SetHook (T : Type) : SetHookSig T :=
  { set          := SetHookDef.setCAx,
    unit         := SetHookDef.unitAx,
    concat       := SetHookDef.concatAx,
    element      := SetHookDef.elementAx T,
    union        := SetHookDef.unionAx,
    intersection := SetHookDef.intersectionAx,
    difference   := SetHookDef.differenceAx,
    inSet        := SetHookDef.inSetAx T,
    inclusion    := SetHookDef.inclusionAx,
    size         := SetHookDef.sizeAx,
    choice       := SetHookDef.choiceAx T }

/-
The `List` sort is an ordered collection that may contain duplicate elements.
 -/

structure listHookSig (T : Type) where
  list      : Type -- Carrier, such as `T → Prop`
  unit      : list
  concat    : list → list → Option list
  element   : T → list
  push      : T → list → list
  get       : Int → list → Option T
  updte     : Int → T → list → Option list
  -- create a list with `length` elements, each containing  `value`. `Option` return type from `Int` parameter
  make      : Int → T → Option list
  -- create a new `List` which is equal to `dest` except the  `N` elements starting at `index` are replaced with the   contents of `src`
  -- Having `index + size(src) > size(dest)` is undefined
  -- updateList(dest: List, index: Int, src: List)
  updateAll : list → Int → list → Option list
  -- create a new `List` where the `length` elements starting   at `index` are replaced with `value`
  fill      : list → Int → T → Option list
  -- compute a new `List` by removing `fromFront` elements from   the front of the list and `fromBack` elements from the back   of the list
  -- range(List, fromFront: Int, fromBack: Int)
  range     : list → Int → Int → Option list
  -- compute whether an element is in a list
  -- the hook is `in`, but clashes with Lean syntax
  inList    : T → list → Bool
  size      : list → Int

namespace ListHookDef
  variable (T : Type)
  def listCAx       := List T
  axiom unitAx      : listCAx T
  axiom concatAx    : listCAx T → listCAx T → Option (listCAx T)
  axiom elementAx   : T → listCAx T
  axiom pushAx      : T → listCAx T → listCAx T
  axiom getAx       : Int → listCAx T → Option T
  axiom updteAx     : Int → T → listCAx T → Option (listCAx T)
  axiom makeAx      : Int → T → Option (listCAx T)
  axiom updateAllAx : listCAx T → Int → listCAx T → Option (listCAx T)
  axiom fillAx      : listCAx T → Int → T → Option (listCAx T)
  axiom rangeAx     : listCAx T → Int → Int → Option (listCAx T)
  axiom inListAx    : T → listCAx T → Bool
  axiom sizeAx      : listCAx T → Int
end ListHookDef

noncomputable def ListHook (T : Type) : listHookSig T :=
  { list      := ListHookDef.listCAx T,
    unit      := ListHookDef.unitAx T,
    concat    := ListHookDef.concatAx T,
    element   := ListHookDef.elementAx T,
    push      := ListHookDef.pushAx T,
    get       := ListHookDef.getAx T,
    updte     := ListHookDef.updteAx T,
    make      := ListHookDef.makeAx T,
    updateAll := ListHookDef.updateAllAx T,
    fill      := ListHookDef.fillAx T,
    range     := ListHookDef.rangeAx T,
    inList    := ListHookDef.inListAx T,
    size      := ListHookDef.sizeAx T }

class Inj (From To : Type) : Type where
  inj (x : From) : To

def inj {From To : Type} [inst : Inj From To] := inst.inj

def «_+Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt := some (x0 + x1)
def «_-Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt := some (x0 - x1)
def «_*Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt := some (x0 * x1)
def «_<=Int_» (x0 : SortInt) (x1 : SortInt) : Option SortBool := some (x0 <= x1)
