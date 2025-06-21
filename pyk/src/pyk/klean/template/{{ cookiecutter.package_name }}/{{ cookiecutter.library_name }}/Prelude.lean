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
  unit       : List (K × V)
  cons       : K → V → List (K × V) → List (K × V)
  lookup     : List (K × V) → K → Option V
  lookup?    : List (K × V) → K → V -- lookup with default
  update     : K → V → List (K × V) → List (K × V)
  delete     : List (K × V) → K → List (K × V)
  concat     : List (K × V) → List (K × V) → Option (List (K × V))
  difference : List (K × V) → List (K × V) → List (K × V)
  updateMap  : List (K × V) → List (K × V) → List (K × V)
  removeAll  : List (K × V) → List K → List (K × V)
  keys       : List (K × V) → List K
  in_keys    : List (K × V) → K → Bool
  values     : List (K × V) → List V
  size       : List (K × V) → Nat
  includes   : List (K × V) → List (K × V) → Bool -- List (K × V) inclusion
  choice     : List (K × V) → K -- arbitrary key from a List (K × V)
  -- nodup is not satisfiable in the current implementation with `List (K × V)`
  -- nodup      : forall al : List (K × V), List.Nodup (keys al)
  split      : List (K × V) → List K → Option (List V × List (K × V))

-- We use axioms to have uninterpreted functions
namespace MapHookDef
  variable (K V : Type)
  axiom unitAx       : List (K × V)
  axiom consAx       : K → V → List (K × V) → List (K × V)
  axiom lookupAx     : List (K × V) → K → Option V
  axiom lookupAx?    : List (K × V) → K → V -- lookup with default
  axiom updateAx     : K → V → List (K × V) → List (K × V)
  axiom deleteAx     : List (K × V) → K → List (K × V)
  axiom concatAx     : List (K × V) → List (K × V) → Option (List (K × V))
  axiom differenceAx : List (K × V) → List (K × V) → List (K × V)
  axiom updateMapAx  : List (K × V) → List (K × V) → List (K × V)
  axiom removeAllAx  : List (K × V) → List K → List (K × V)
  axiom keysAx       : List (K × V) → List K
  axiom in_keysAx    : List (K × V) → K → Bool
  axiom valuesAx     : List (K × V) → List V
  axiom sizeAx       : List (K × V) → Nat
  axiom includesAx   : List (K × V) → List (K × V) → Bool -- map inclusion
  axiom choiceAx     : List (K × V) → K -- arbitrary key from a map
  -- axiom nodupAx      : forall m, List.Nodup (keysAx K V m)
  axiom splitAx      : List (K × V) → List K → Option (List V × List (K × V))
end MapHookDef

-- Uninterpreted Map implementation
noncomputable def MapHook (K V : Type) : MapHookSig K V :=
  { unit       := MapHookDef.unitAx K V,
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
    -- nodup      := MapHookDef.nodupAx K V,
    split      := MapHookDef.splitAx K V }

/-
Implementation of immutable, associative, commutative sets of `KItem`.
The sets are nilpotent, i.e., the concatenation of two sets containing elements in common is `#False` (note however, this may be silently allowed during concrete execution).
If you intend to add an element to a set that might already be present in the set, use the `|Set` operator instead.
 -/

structure SetHookSig (T : Type) where
  unit         : List T
  concat       : List T → List T → Option (List T)
  element      : T → List T
  union        : List T → List T → List T
  intersection : List T → List T → List T
  difference   : List T → List T → List T
  inSet        : T → List T → Bool
  inclusion    : List T → List T → Bool
  size         : List T → Int
  choice       : List T → T
  split        : List T → List T → Option (List T)

namespace SetHookDef
  variable (T : Type)
  axiom unitAx         : List T
  axiom concatAx       : List T → List T → Option (List T)
  axiom elementAx      : T → List T
  axiom unionAx        : List T → List T → List T
  axiom intersectionAx : List T → List T → List T
  axiom differenceAx   : List T → List T → List T
  axiom inSetAx        : T → List T → Bool
  axiom inclusionAx    : List T → List T → Bool
  axiom sizeAx         : List T → Int
  axiom choiceAx       : List T → T
  axiom splitAx        : List T → List T → Option (List T)
end SetHookDef

noncomputable def SetHook (T : Type) : SetHookSig T :=
  { unit         := SetHookDef.unitAx T,
    concat       := SetHookDef.concatAx T,
    element      := SetHookDef.elementAx T,
    union        := SetHookDef.unionAx T,
    intersection := SetHookDef.intersectionAx T,
    difference   := SetHookDef.differenceAx T,
    inSet        := SetHookDef.inSetAx T,
    inclusion    := SetHookDef.inclusionAx T,
    size         := SetHookDef.sizeAx T,
    choice       := SetHookDef.choiceAx T,
    split        := SetHookDef.splitAx T }

/-
The `List` sort is an ordered collection that may contain duplicate elements.
 -/

structure listHookSig (T : Type) where
  unit      : List T
  concat    : List T → List T → Option (List T)
  element   : T → List T
  push      : T → List T → List T
  get       : Int → List T → Option T
  updte     : Int → T → List T → Option (List T)
  -- create a List T with `length` elements, each containing  `value`. `Option` return type from `Int` parameter
  make      : Int → T → Option (List T)
  -- create a new `List T` which is equal to `dest` except the  `N` elements starting at `index` are replaced with the   contents of `src`
  -- Having `index + size(src) > size(dest)` is undefined
  -- updateList(dest: List T, index: Int, src: List T)
  updateAll : List T → Int → List T → Option (List T)
  -- create a new `List T` where the `length` elements starting   at `index` are replaced with `value`
  fill      : List T → Int → T → Option (List T)
  -- compute a new `List T` by removing `fromFront` elements from   the front of the list and `fromBack` elements from the back   of the List T
  -- range(List T, fromFront: Int, fromBack: Int)
  range     : List T → Int → Int → Option (List T)
  -- compute whether an element is in a List T
  -- the hook is `in`, but clashes with Lean syntax
  inList    : T → List T → Bool
  size      : List T → Int
  -- split list into prefix, middle and postfix, given prefix and postfix length
  split     : List T → Nat → Nat → Option (List T × List T × List T)

namespace ListHookDef
  variable (T : Type)
  axiom unitAx      : List T
  axiom concatAx    : List T → List T → Option (List T)
  axiom elementAx   : T → List T
  axiom pushAx      : T → List T → List T
  axiom getAx       : Int → List T → Option T
  axiom updteAx     : Int → T → List T → Option (List T)
  axiom makeAx      : Int → T → Option (List T)
  axiom updateAllAx : List T → Int → List T → Option (List T)
  axiom fillAx      : List T → Int → T → Option (List T)
  axiom rangeAx     : List T → Int → Int → Option (List T)
  axiom inListAx    : T → List T → Bool
  axiom sizeAx      : List T → Int
  axiom splitAx     : List T → Nat → Nat → Option (List T × List T × List T)
end ListHookDef

noncomputable def ListHook (T : Type) : listHookSig T :=
  { unit      := ListHookDef.unitAx T,
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
    size      := ListHookDef.sizeAx T,
    split     := ListHookDef.splitAx T }

class Inj (From To : Type) : Type where
  inj (x : From) : To
  retr (x : To) : Option From

def inj {From To : Type} [inst : Inj From To] := inst.inj
def retr {From To : Type} [inst : Inj From To] := inst.retr

-- Instances

instance: BEq UInt8 where
  beq a b := decide (Eq a b)

instance: BEq SortBytes where
  beq a b := (ByteArray.toList a) == (ByteArray.toList b)

def ByteArray.decEq (a b : ByteArray) : Decidable (Eq a b) :=
  match a, b with
  | ⟨⟨al⟩⟩, ⟨⟨bl⟩⟩ => match List.hasDecEq al bl with
    | isTrue t => isTrue (by rw [t])
    | isFalse f => isFalse (by simp [f])

instance: DecidableEq SortBytes := ByteArray.decEq

/-! ### Function Implementations -/

-- `SortInt`

-- Operations
def «_+Int_» (x0 x1 : SortInt) : Option SortInt := some (x0 + x1)
def «_-Int_» (x0 x1 : SortInt) : Option SortInt := some (x0 - x1)
def «_*Int_» (x0 x1 : SortInt) : Option SortInt := some (x0 * x1)
def «_/Int_» (x0 x1 : SortInt) : Option SortInt :=
  ite (x1 == 0) none (Int.tdiv x0 x1)
def _modInt_ (x0 x1 : SortInt) : Option SortInt :=
  ite (x1 == 0) none (Int.emod x0 x1)
def «_^%Int__» (x0 x1 x2 : SortInt) : Option SortInt :=
   if x2 == 0 then none else
   match x1 with -- TODO: Revisit this implementation
   | .ofNat n => some (Int.emod (Int.pow x0 n) x2)
   | _ => none
def «maxInt(_,_)_INT-COMMON_Int_Int_Int» (x0 x1 : SortInt) :=
  some (ite (x0 < x1) x1 x0)
def «log2Int(_)_INT-COMMON_Int_Int» (x0 : SortInt) : Option SortInt :=
  ite (0 < x0) ((Nat.log2 x0.toNat) : Int) none
def «~Int_» (x0 : SortInt) : Option SortInt := some (.not x0)

-- Comparisons
def «_<=Int_» (x0 x1 : SortInt) : Option SortBool := some (x0 <= x1)
def «_>=Int_» (x0 x1 : SortInt) : Option SortBool := some (x0 >= x1)
def «_<Int_» (x0 x1 : SortInt) : Option SortBool := some (x0 < x1)
def «_>Int_» (x0 x1 : SortInt) : Option SortBool := some (x0 > x1)
def «_==Int_» (x0 x1 : SortInt) : Option SortBool := some (x0 == x1)

-- `SortBytes`

inductive SortEndianness : Type where
  | bigEndianBytes : SortEndianness
  | littleEndianBytes : SortEndianness
  deriving BEq, DecidableEq

inductive SortSignedness : Type where
  | signedBytes : SortSignedness
  | unsignedBytes : SortSignedness
  deriving BEq, DecidableEq

def «.Bytes_BYTES-HOOKED_Bytes» : Option SortBytes := some .empty

-- Adapted from https://github.com/runtimeverification/haskell-backend/blob/362dab30d6435ec117862fea722be67373572034/kore/src/Kore/Builtin/InternalBytes.hs#L496-L511
def «Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness» (x0 x1 : SortInt) (x2 : SortEndianness) : Option SortBytes :=
  match x2 with
  | .littleEndianBytes => some littleEndian.toByteArray
  | .bigEndianBytes => some littleEndian.reverse.toByteArray
  where
  littleEndian : List UInt8 :=
    let pad := ite (x1 < 0) 0xFF 0x00
    let rec bytes (len : Nat) (n : Int) : List UInt8 :=
      match len, n with
      | 0, _ => []
      | .succ l, 0 => pad :: bytes l 0
      | .succ l, n => ⟨(n % 256).toNat⟩ :: bytes l (n / 256)
    bytes x0.toNat x1

-- Adapted from
-- https://github.com/runtimeverification/haskell-backend/blob/362dab30d6435ec117862fea722be67373572034/kore/src/Kore/Builtin/InternalBytes.hs#L527-L543
-- Note that we use `List.foldl` and not `ByteArray.foldl` for ease of reasoning
def «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness» (bytes : SortBytes) (endian : SortEndianness) (sign : SortSignedness) : Option SortInt :=
  match sign with
  | .unsignedBytes => Int.ofNat unsigned
  | .signedBytes => if 2 * unsigned >= modulus then (Int.ofNat unsigned) - (Int.ofNat modulus)
                    else Int.ofNat unsigned
  where
  modulus : Nat := res.1
  unsigned : Nat := res.2
  res : Nat×Nat :=
    let littleEndian := match endian with
                        | .littleEndianBytes => bytes.toList
                            --match bytes with |⟨⟨l⟩⟩ => l
                        | .bigEndianBytes => bytes.toList.reverse
                            --match bytes with |⟨⟨l⟩⟩ => l.reverse
    let go (res : Nat×Nat) (b : UInt8) : Nat×Nat :=
      -- `place` is `res.1`
      -- `acc` is `res.2`
      let place := res.1 * 0x100
      let acc := res.2 + res.1 * b.toNat
      ⟨place, acc⟩
    List.foldl go (1, 0) littleEndian

/--
Pads to the right `len - b.length` bytes with specified `val` value
-/
def «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» (b : SortBytes) (len val : SortInt) : Option SortBytes :=
  if val < 0 ∨ 255 < val then none else
  some { data := (Array.rightpad len.toNat (⟨val.toNat⟩ : UInt8) b.data)}

/--
Pads to the left `len - b.length` bytes with specified `val` value
-/
def «padLeftBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» (b : SortBytes) (len val : SortInt) : Option SortBytes :=
  if val < 0 ∨ 255 < val then none else
  some { data := (Array.leftpad len.toNat (⟨val.toNat⟩ : UInt8) b.data)}

def «lengthBytes(_)_BYTES-HOOKED_Int_Bytes» (x0 : SortBytes) : Option SortInt :=
  Int.ofNat x0.size

/--
Replaces the contents of `dest` from index `index` with the contents of `src`
If `dest.size < index + src.size` the result is `none`
-/
def «replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes» (dest : SortBytes) (index : SortInt) (src : SortBytes) : Option SortBytes :=
  if index < 0 then none else
  if dest.size < index + src.size then none else
  let init := dest.data.extract 0 index.toNat
  let rem := dest.data.extract (index.toNat + src.size) dest.size
  some { data := init ++ src.data ++ rem }

/--
Get a new `Bytes` object containing a range of bytes from the input `Bytes`
-/
def «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» (b : SortBytes) (startIndex : SortInt) (endIndex : SortInt) : Option SortBytes :=
  if startIndex < 0 then none else
  if endIndex < startIndex then none else
  if b.size < endIndex then none else
  b.extract startIndex.toNat endIndex.toNat
