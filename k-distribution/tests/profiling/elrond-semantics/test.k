// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module WASM-DATA-SYNTAX
  imports public WASM-DATA-COMMON-SYNTAX
endmodule

module WASM-DATA-COMMON-SYNTAX
  imports public INT-SYNTAX
  imports public FLOAT-SYNTAX
  syntax IdentifierToken [token]
  syntax WasmIntToken [token]
  syntax #Layout [token]
  syntax WasmStringToken [token]
  syntax Identifier  ::=
    IdentifierToken
  syntax OptionalId  ::=
    "" [klabel(.Identifier), symbol]
  | Identifier
  syntax WasmString  ::=
    ".WasmString"
  | WasmStringToken
  syntax String  ::=
    "#parseWasmString" "(" WasmStringToken ")" [function, hook(STRING.token2string), klabel(#parseWasmString), total]
  syntax DataString  ::=
    List{WasmString,""} [symbol(listWasmString)]
  syntax Index  ::=
    WasmInt
  syntax ElemSegment  ::=
    List{Index,""} [symbol(listIndex)]
  syntax IValType  ::=
    "i32" [klabel(i32), symbol]
  | "i64" [klabel(i64), symbol]
  syntax FValType  ::=
    "f32" [klabel(f32), symbol]
  | "f64" [klabel(f64), symbol]
  syntax ValType  ::=
    IValType
  | FValType
  syntax ValTypes  ::=
    List{ValType,""} [symbol(listValTypes)]
  syntax WasmInt  ::=
    Int
  syntax Mut  ::=
    "const" [klabel(mutConst), symbol]
  | "var" [klabel(mutVar), symbol]
  syntax Number  ::=
    Int
  | Float
  syntax AllocatedKind  ::=
    "func"
  | "table"
  | "memory"
  | "global"
  syntax Externval  ::=
    AllocatedKind Index
endmodule

module WASM-DATA-COMMON
  imports public WASM-DATA-COMMON-SYNTAX
  imports public INT
  imports public BOOL
  imports public STRING
  imports public LIST
  imports public MAP
  imports public FLOAT
  imports public BYTES
  imports public K-EQUAL
  syntax Identifier  ::=
    "#freshId" "(" Int ")" [klabel(#freshId)]
  syntax Map  ::=
    "#saveId" "(" Map "," OptionalId "," Int ")" [function, klabel(#saveId)]
  rule #saveId (MAP, ID:OptionalId, _)   => MAP             requires notBool isIdentifier(ID)
  rule #saveId (MAP, ID:Identifier, IDX) => MAP [ID <- IDX]
  syntax Int  ::=
    "#ContextLookup" "(" Map "," Index ")" [function, klabel(#ContextLookup)]
  rule #ContextLookup(_IDS:Map, I:Int) => I
  syntax Ints  ::=
    List{Int,""} [symbol(listInt)]
  syntax Int  ::=
    "#lenElemSegment" "(" ElemSegment ")" [function, klabel(#lenElemSegment)]
  syntax Index  ::=
    "#getElemSegment" "(" ElemSegment "," Int ")" [function, klabel(#getElemSegment)]
  syntax Int  ::=
    "#lenInts" "(" Ints ")" [function, klabel(#lenInts)]
  syntax Int  ::=
    "#getInts" "(" Ints "," Int ")" [function, klabel(#getInts)]
  rule #lenElemSegment(.ElemSegment) => 0
  rule #lenElemSegment(_TFIDX    ES) => 1 +Int #lenElemSegment(ES)
  rule #getElemSegment(E _ES, 0) => E
  rule #getElemSegment(_E ES, I) => #getElemSegment(ES, I -Int 1) requires I >Int 0
  rule #lenInts(.Ints) => 0
  rule #lenInts(_TFIDX    ES) => 1 +Int #lenInts(ES)
  rule #getInts(E _ES, 0) => E
  rule #getInts(_E ES, I) => #getInts(ES, I -Int 1) requires I >Int 0
  syntax Ints  ::=
    "elemSegment2Ints" "(" ElemSegment ")" [function, klabel(elemSegment2Ints)]
  rule elemSegment2Ints(.ElemSegment) => .Ints
  rule elemSegment2Ints(E:Int ES)     => E elemSegment2Ints(ES)
  syntax OptionalInt  ::=
    Int
  | ".Int" [klabel(.Int), symbol]
  syntax Limits  ::=
    "#limitsMin" "(" Int ")" [klabel(limitsMin), symbol]
  | "#limits" "(" Int "," Int ")" [klabel(limitsMinMax), symbol]
  syntax VecType  ::=
    "[" ValTypes "]" [klabel(aVecType), symbol]
  syntax FuncType  ::=
    VecType "->" VecType [klabel(aFuncType), symbol]
  syntax Int  ::=
    "lengthValTypes" "(" ValTypes ")" [function, klabel(lengthValTypes), total]
  rule lengthValTypes(.ValTypes) => 0
  rule lengthValTypes(_V VS)     => 1 +Int lengthValTypes(VS)
  syntax Type  ::=
    ".Type"
  | ValType
  | VecType
  | FuncType
  syntax ValTypes  ::=
    ValTypes "+" ValTypes [function, total]
  rule .ValTypes   + VTYPES' => VTYPES'
  rule (VT VTYPES) + VTYPES' => VT (VTYPES + VTYPES')
  syntax ValTypes  ::=
    "#revt" "(" ValTypes ")" [function, klabel(#revt), total]
  | "#revt" "(" ValTypes "," ValTypes ")" [function, klabel(#revtAux), total]
  rule #revt(VT) => #revt(VT, .ValTypes)
  rule #revt(.ValTypes, VT') => VT'
  rule #revt(V VT     , VT') => #revt(VT, V VT')
  syntax Int  ::=
    "#width" "(" IValType ")" [function, klabel(#width), total]
  syntax Int  ::=
    "#numBytes" "(" IValType ")" [function, klabel(#numBytes), smtlib(numBytes), total]
  rule #width(i32) => 32
  rule #width(i64) => 64
  rule #numBytes(ITYPE) => #width(ITYPE) /Int 8  [concrete]
  syntax Int  ::=
    "#pow" "(" IValType ")" [function, klabel(#pow), smtlib(pow ), total]
  | "#pow1" "(" IValType ")" [function, klabel(#pow1), smtlib(pow1), total]
  rule #pow1(i32) => 2147483648
  rule #pow (i32) => 4294967296
  rule #pow1(i64) => 9223372036854775808
  rule #pow (i64) => 18446744073709551616
  syntax Mut  ::=
    ".Mut"
  syntax IVal  ::=
    "<" IValType ">" Int [klabel(<_>_)]
  syntax FVal  ::=
    "<" FValType ">" Float [klabel(<_>_)]
  syntax Val  ::=
    "<" ValType ">" Number [klabel(<_>_)]
  | IVal
  | FVal
  syntax Val  ::=
    "undefined"
  syntax IVal  ::=
    "#chop" "(" IVal ")" [function, klabel(#chop), total]
  rule #chop(< ITYPE > N) => < ITYPE > (N modInt #pow(ITYPE))
  syntax Int  ::=
    "#wrap" "(" Int "," Int ")" [function, klabel(#wrap), total]
  rule #wrap(WIDTH, _N) => 0      requires notBool 0 <Int WIDTH
  syntax Int  ::=
    "#get" "(" IVal ")" [function, klabel(#get), total]
  rule #get(< _ > N) => N
  syntax FVal  ::=
    "#round" "(" FValType "," Number ")" [function, klabel(#round)]
  rule #round(f64 , N:Float) => < f64 > roundFloat(N, 53, 11)  [concrete]
  rule #round(f32 , N:Float) => < f32 > roundFloat(N, 24, 8)   [concrete]
  rule #round(f64 , N:Int  ) => < f64 >  Int2Float(N, 53, 11)  [concrete]
  rule #round(f32 , N:Int  ) => < f32 >  Int2Float(N, 24, 8)   [concrete]
  syntax Int  ::=
    "#signed" "(" IValType "," Int ")" [function, klabel(#signed)]
  | "#unsigned" "(" IValType "," Int ")" [function, klabel(#unsigned)]
  | "#signedWidth" "(" Int "," Int ")" [function, klabel(#signedWidth)]
  rule #signed(ITYPE, N) => N                  requires 0            <=Int N andBool N <Int #pow1(ITYPE)
  rule #signed(ITYPE, N) => N -Int #pow(ITYPE) requires #pow1(ITYPE) <=Int N andBool N <Int #pow (ITYPE)
  rule #unsigned( ITYPE, N) => N +Int #pow(ITYPE) requires N  <Int 0
  rule #unsigned(_ITYPE, N) => N                  requires 0 <=Int N
  rule #signedWidth(1, N) => N            requires 0     <=Int N andBool N <Int 128
  rule #signedWidth(1, N) => N -Int 256   requires 128   <=Int N andBool N <Int 256
  rule #signedWidth(2, N) => N            requires 0     <=Int N andBool N <Int 32768
  rule #signedWidth(2, N) => N -Int 65536 requires 32768 <=Int N andBool N <Int 65536
  rule #signedWidth(4, N) => #signed(i32, N)
  syntax Int  ::=
    "#bool" "(" Bool ")" [function, klabel(#bool), total]
  rule #bool( B:Bool ) => 1 requires         B
  rule #bool( B:Bool ) => 0 requires notBool B
  syntax ValStack  ::=
    ".ValStack" [klabel(.ValStack), symbol]
  | Val ":" ValStack [klabel(concatValStack), symbol]
  | ValStack "++" ValStack [function, total]
  rule .ValStack       ++ VALSTACK' => VALSTACK'
  rule (SI : VALSTACK) ++ VALSTACK' => SI : (VALSTACK ++ VALSTACK')
  syntax ValStack  ::=
    "#zero" "(" ValTypes ")" [function, klabel(#zero), total]
  | "#take" "(" Int "," ValStack ")" [function, klabel(#take), total]
  | "#drop" "(" Int "," ValStack ")" [function, klabel(#drop), total]
  | "#revs" "(" ValStack ")" [function, klabel(#revs), total]
  | "#revs" "(" ValStack "," ValStack ")" [function, klabel(#revsAux), total]
  rule #zero(.ValTypes)             => .ValStack
  rule #zero(ITYPE:IValType VTYPES) => < ITYPE > 0   : #zero(VTYPES)
  rule #zero(FTYPE:FValType VTYPES) => < FTYPE > 0.0 : #zero(VTYPES)
  rule #take(N, _)         => .ValStack               requires notBool N >Int 0
  rule #take(N, .ValStack) => .ValStack               requires         N >Int 0
  rule #take(N, V : VS)    => V : #take(N -Int 1, VS) requires         N >Int 0
  rule #drop(N, VS)        => VS                  requires notBool N >Int 0
  rule #drop(N, .ValStack) => .ValStack           requires         N >Int 0
  rule #drop(N, _ : VS)    => #drop(N -Int 1, VS) requires         N >Int 0
  rule #revs(VS) => #revs(VS, .ValStack)
  rule #revs(.ValStack, VS') => VS'
  rule #revs(V : VS   , VS') => #revs(VS, V : VS')
  syntax String  ::=
    "unescape" "(" String ")" [function, klabel(unescape)]
  | "unescape" "(" String "," Int "," String ")" [function, klabel(unescapeAux)]
  rule unescape(S         ) => unescape(S, 1, "")
  rule unescape(S, IDX, SB) => SB                 requires IDX ==Int lengthString(S) -Int 1
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 1, SB +String substrString(S, IDX, IDX +Int 1))
      requires IDX <Int lengthString(S) -Int 1
       andBool substrString(S, IDX, IDX +Int 1) =/=K "\\"
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 3, SB +String chrChar(String2Base(substrString(S, IDX +Int 1, IDX +Int 3), 16)))
      requires IDX <Int lengthString(S) -Int 3
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool (findChar("0123456789abcdefABCDEF", substrString(S, IDX +Int 1, IDX +Int 2), 0) =/=Int -1 )
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 2, SB +String chrChar(String2Base("09", 16)))
      requires IDX <Int lengthString(S) -Int 2
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "t"
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 2, SB +String chrChar(String2Base("0A", 16)))
      requires IDX <Int lengthString(S) -Int 2
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "n"
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 2, SB +String chrChar(String2Base("0D", 16)))
      requires IDX <Int lengthString(S) -Int 2
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "r"
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 2, SB +String chrChar(String2Base("22", 16)))
      requires IDX <Int lengthString(S) -Int 2
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "\""
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 2, SB +String chrChar(String2Base("27", 16)))
      requires IDX <Int lengthString(S) -Int 2
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "'"
  rule unescape(S, IDX, SB) => unescape(S, IDX +Int 2, SB +String chrChar(String2Base("5C", 16)))
      requires IDX <Int lengthString(S) -Int 2
       andBool substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "\\"
  syntax Int  ::=
    "#idxCloseBracket" "(" String "," Int ")" [function, klabel(#idxCloseBracket)]
  rule #idxCloseBracket ( S, I ) => I                                requires substrString(S, I, I +Int 1)  ==String "}"
  rule #idxCloseBracket ( S, I ) => #idxCloseBracket ( S, I +Int 1 ) requires substrString(S, I, I +Int 1) =/=String "}"
  syntax Bytes  ::=
    "#encodeUTF8" "(" Int ")" [function, klabel(#encodeUTF8)]
  rule #encodeUTF8 (I) => Int2Bytes(I, BE, Unsigned) requires I <=Int 127
  rule #encodeUTF8 (I) => Int2Bytes(((((I &Int 1984) >>Int 6) +Int 192) <<Int 8) +Int ((I &Int 63) +Int 128), BE, Unsigned)
      requires I >=Int 128   andBool I <=Int 2047
  rule #encodeUTF8 (I) => Int2Bytes(((((I &Int 61440) >>Int 12) +Int 224) <<Int 16) +Int ((((I &Int 4032) >>Int 6) +Int 128) <<Int 8) +Int ((I &Int 63) +Int 128), BE, Unsigned)
      requires I >=Int 2048  andBool I <=Int 65535
  rule #encodeUTF8 (I) => Int2Bytes(((((I &Int 1835008) >>Int 18) +Int 240) <<Int 24) +Int ((((I &Int 258048) >>Int 12) +Int 128) <<Int 16) +Int ((((I &Int 4032) >>Int6) +Int 128) <<Int 8) +Int ((I &Int 63) +Int 128), BE, Unsigned)
      requires I >=Int 65536 andBool I <=Int 1114111
  rule unescape(S, IDX, SB) => unescape(S, #idxCloseBracket(S, IDX) +Int 1, SB +String Bytes2String(#encodeUTF8(String2Base(substrString(S, IDX +Int 3, #idxCloseBracket(S, IDX +Int 3)), 16))))
      requires substrString(S, IDX, IDX +Int 1) ==K "\\"
       andBool substrString(S, IDX +Int 1, IDX +Int 2) ==K "u"
  syntax String  ::=
    "#concatDS" "(" DataString ")" [function, klabel(#concatDS)]
  | "#concatDS" "(" DataString "," String ")" [function, klabel(#concatDSAux)]
  rule #concatDS ( DS ) => #concatDS ( DS, "" )
  rule #concatDS ( .DataString            , S ) => S
  rule #concatDS (  WS:WasmStringToken DS , S ) => #concatDS ( DS , S +String unescape(#parseWasmString(WS)) )
  syntax Bytes  ::=
    "#DS2Bytes" "(" DataString ")" [function, klabel(#DS2Bytes)]
  rule #DS2Bytes(DS) => String2Bytes(#concatDS(DS))
  syntax Bytes  ::=
    "#setBytesRange" "(" Bytes "," Int "," Bytes ")" [function, klabel(#setBytesRange), total]
  rule #setBytesRange(BM, START, BS) => replaceAtBytes(padRightBytes(BM, START +Int lengthBytes(BS), 0), START, BS)
      requires          0 <=Int START
  rule #setBytesRange(_, START, _ ) => .Bytes
      requires notBool (0 <=Int START)
  syntax Bytes  ::=
    "#setRange" "(" Bytes "," Int "," Int "," Int ")" [function, klabel(#setRange), smtlib(setRange), total]
  rule #setRange(BM, ADDR, VAL, WIDTH) => BM
      requires notBool (0 <Int WIDTH andBool 0 <=Int VAL andBool 0 <=Int ADDR)
  syntax Bytes  ::=
    "#getBytesRange" "(" Bytes "," Int "," Int ")" [function, klabel(#getBytesRange), total]
  rule #getBytesRange(_, START, WIDTH) => .Bytes
      requires notBool (0 <=Int START andBool 0 <=Int WIDTH)
  rule #getBytesRange(BM, START, WIDTH) => substrBytes(padRightBytes(BM, START +Int WIDTH, 0), START, START +Int WIDTH)
      requires         (0 <=Int START andBool 0 <=Int WIDTH)
       andBool         START <Int lengthBytes(BM)
  rule #getBytesRange(BM, START, WIDTH) => padRightBytes(.Bytes, WIDTH, 0)
      requires         (0 <=Int START andBool 0 <=Int WIDTH)
       andBool notBool (START <Int lengthBytes(BM))
  syntax Int  ::=
    "#getRange" "(" Bytes "," Int "," Int ")" [function, klabel(#getRange), smtlib(getRange), total]
  rule #getRange( _, ADDR, WIDTH) => 0
      requires notBool (0 <Int WIDTH andBool 0 <=Int ADDR)
endmodule

module WASM-DATA-CONCRETE [concrete]
  imports public WASM-DATA-COMMON
  rule [wrap-Positive]: #wrap(WIDTH,  N) => N &Int ((1 <<Int (WIDTH *Int 8)) -Int 1)
      requires 0 <Int WIDTH
  rule [setRange-Positive]: #setRange(BM, ADDR, VAL, WIDTH)
      => #setBytesRange(BM, ADDR, Int2Bytes(WIDTH, VAL, LE))
      requires 0 <Int WIDTH andBool 0 <=Int VAL andBool 0 <=Int ADDR
  rule [getRange-Positive]: #getRange(BM, ADDR, WIDTH)
      => Bytes2Int(#getBytesRange(BM, ADDR, WIDTH), LE, Unsigned)
      requires 0 <Int WIDTH andBool 0 <=Int ADDR
endmodule

module WASM-DATA-SYMBOLIC [symbolic]
  imports public WASM-DATA-COMMON
  rule [wrap-Positive]: #wrap(WIDTH,  N) => N &Int ((1 <<Int (WIDTH *Int 8)) -Int 1)
      requires 0 <Int WIDTH
       [concrete, simplification]
  rule [setRange-Positive]: #setRange(BM, ADDR, VAL, WIDTH)
      => #setBytesRange(BM, ADDR, Int2Bytes(WIDTH, VAL, LE))
      requires 0 <Int WIDTH andBool 0 <=Int VAL andBool 0 <=Int ADDR
       [concrete, simplification]
  rule [getRange-Positive]: #getRange(BM, ADDR, WIDTH)
      => Bytes2Int(#getBytesRange(BM, ADDR, WIDTH), LE, Unsigned)
      requires 0 <Int WIDTH andBool 0 <=Int ADDR
       [concrete, simplification]
endmodule

module WASM-DATA
  imports public WASM-DATA-CONCRETE
  imports public WASM-DATA-SYMBOLIC
endmodule

module WASM-NUMERIC-SYNTAX
  syntax IUnOp  ::=
    "clz" [klabel(aClz), symbol]
  | "ctz" [klabel(aCtz), symbol]
  | "popcnt" [klabel(aPopcnt), symbol]
  syntax FUnOp  ::=
    "abs" [klabel(aAbs), symbol]
  | "neg" [klabel(aNeg), symbol]
  | "sqrt" [klabel(aSqrt), symbol]
  | "floor" [klabel(aFloor), symbol]
  | "ceil" [klabel(aCeil), symbol]
  | "trunc" [klabel(aTrunc), symbol]
  | "nearest" [klabel(aNearest), symbol]
  syntax IBinOp  ::=
    "add" [klabel(intAdd), symbol]
  | "sub" [klabel(intSub), symbol]
  | "mul" [klabel(intMul), symbol]
  | "div_u" [klabel(intDiv_u), symbol]
  | "rem_u" [klabel(intRem_u), symbol]
  | "div_s" [klabel(intDiv_s), symbol]
  | "rem_s" [klabel(intRem_s), symbol]
  | "and" [klabel(intAnd), symbol]
  | "or" [klabel(intOr), symbol]
  | "xor" [klabel(intXor), symbol]
  | "shl" [klabel(intShl), symbol]
  | "shr_u" [klabel(intShr_u), symbol]
  | "shr_s" [klabel(intShr_s), symbol]
  | "rotl" [klabel(intRotl), symbol]
  | "rotr" [klabel(intRotr), symbol]
  syntax FBinOp  ::=
    "add" [klabel(floatAdd), symbol]
  | "sub" [klabel(floatSub), symbol]
  | "mul" [klabel(floatMul), symbol]
  | "div" [klabel(floatDiv), symbol]
  | "min" [klabel(floatMin), symbol]
  | "max" [klabel(floatMax), symbol]
  | "copysign" [klabel(floatCopysign), symbol]
  syntax TestOp  ::=
    "eqz" [klabel(aEqz), symbol]
  syntax IRelOp  ::=
    "eq" [klabel(intEq), symbol]
  | "ne" [klabel(intNe), symbol]
  | "lt_u" [klabel(intLt_u), symbol]
  | "gt_u" [klabel(intGt_u), symbol]
  | "lt_s" [klabel(intLt_s), symbol]
  | "gt_s" [klabel(intGt_s), symbol]
  | "le_u" [klabel(intLe_u), symbol]
  | "ge_u" [klabel(intGe_u), symbol]
  | "le_s" [klabel(intLe_s), symbol]
  | "ge_s" [klabel(intGe_s), symbol]
  syntax FRelOp  ::=
    "lt" [klabel(floatLt), symbol]
  | "gt" [klabel(floatGt), symbol]
  | "le" [klabel(floatLe), symbol]
  | "ge" [klabel(floatGe), symbol]
  | "eq" [klabel(floatEq), symbol]
  | "ne" [klabel(floatNe), symbol]
  syntax CvtOp  ::=
    Cvti32Op
  | Cvti64Op
  | Cvtf32Op
  | Cvtf64Op
  syntax Cvti32Op  ::=
    "extend_i32_u" [klabel(aExtend_i32_u), symbol]
  | "extend_i32_s" [klabel(aExtend_i32_s), symbol]
  | "convert_i32_s" [klabel(aConvert_i32_s), symbol]
  | "convert_i32_u" [klabel(aConvert_i32_u), symbol]
  syntax Cvti64Op  ::=
    "wrap_i64" [klabel(aWrap_i64), symbol]
  | "convert_i64_s" [klabel(aConvert_i64_s), symbol]
  | "convert_i64_u" [klabel(aConvert_i64_u), symbol]
  syntax Cvtf32Op  ::=
    "promote_f32" [klabel(aPromote_f32), symbol]
  | "trunc_f32_s" [klabel(aTrunc_f32_s), symbol]
  | "trunc_f32_u" [klabel(aTrunc_f32_u), symbol]
  syntax Cvtf64Op  ::=
    "demote_f64" [klabel(aDemote_f64), symbol]
  | "trunc_f64_s" [klabel(aTrunc_f64_s), symbol]
  | "trunc_f64_u" [klabel(aTrunc_f64_u), symbol]
endmodule

module WASM-NUMERIC
  imports public WASM-NUMERIC-SYNTAX
  imports public WASM-DATA
  syntax Val  ::=
    IValType "." IUnOp Int [function, klabel(intUnOp)]
  | FValType "." FUnOp Float [function, klabel(floatUnOp)]
  rule ITYPE . clz    I1 => < ITYPE > #width(ITYPE) -Int #minWidth(I1)
  rule ITYPE . ctz    I1 => < ITYPE > #if I1 ==Int 0 #then #width(ITYPE) #else #ctz(I1) #fi
  rule ITYPE . popcnt I1 => < ITYPE > #popcnt(I1)
  syntax Int  ::=
    "#minWidth" "(" Int ")" [function, klabel(#minWidth)]
  | "#ctz" "(" Int ")" [function, klabel(#ctz)]
  | "#popcnt" "(" Int ")" [function, klabel(#popcnt)]
  rule #minWidth(0) => 0
  rule #minWidth(N) => 1 +Int #minWidth(N >>Int 1)                                 requires N =/=Int 0
  rule #ctz(0) => 0
  rule #ctz(N) => #if N modInt 2 ==Int 1 #then 0 #else 1 +Int #ctz(N >>Int 1) #fi  requires N =/=Int 0
  rule #popcnt(0) => 0
  rule #popcnt(N) => #bool(N modInt 2 ==Int 1) +Int #popcnt(N >>Int 1)             requires N =/=Int 0
  syntax Bool  ::=
    "#isInfinityOrNaN" "(" Float ")" [function, klabel(#isInfinityOrNaN)]
  rule #isInfinityOrNaN ( F ) => (isNaN(F) orBool isInfinite(F))
  rule FTYPE . abs     F => < FTYPE >   absFloat (F)
  rule FTYPE . neg     F => < FTYPE >    --Float  F
  rule FTYPE . sqrt    F => < FTYPE >  sqrtFloat (F)
  rule FTYPE . floor   F => < FTYPE > floorFloat (F)
  rule FTYPE . ceil    F => < FTYPE >  ceilFloat (F)
  rule FTYPE . trunc   F => < FTYPE > truncFloat (F)
  rule FTYPE . nearest F => < FTYPE >  F                requires          #isInfinityOrNaN (F)
  rule FTYPE . nearest F => #round(FTYPE, Float2Int(F)) requires (notBool #isInfinityOrNaN (F)) andBool notBool (Float2Int(F) ==Int 0 andBool signFloat(F))
  rule FTYPE . nearest F => < FTYPE > -0.0              requires (notBool #isInfinityOrNaN (F)) andBool          Float2Int(F) ==Int 0 andBool signFloat(F)
  syntax Val  ::=
    IValType "." IBinOp Int Int [function, klabel(intBinOp)]
  | FValType "." FBinOp Float Float [function, klabel(floatBinOp)]
  rule ITYPE:IValType . add I1 I2 => #chop(< ITYPE > I1 +Int I2)
  rule ITYPE:IValType . sub I1 I2 => #chop(< ITYPE > I1 -Int I2)
  rule ITYPE:IValType . mul I1 I2 => #chop(< ITYPE > I1 *Int I2)
  rule ITYPE . div_u  I1 I2 => < ITYPE > I1 /Int I2 requires I2 =/=Int 0
  rule _ITYPE . div_u _I1 I2 => undefined            requires I2  ==Int 0
  rule ITYPE . rem_u  I1 I2 => < ITYPE > I1 %Int I2 requires I2 =/=Int 0
  rule _ITYPE . rem_u _I1 I2 => undefined            requires I2  ==Int 0
  rule ITYPE . div_s I1 I2 => < ITYPE > #unsigned(ITYPE, #signed(ITYPE, I1) /Int #signed(ITYPE, I2))
      requires I2 =/=Int 0
       andBool #signed(ITYPE, I1) /Int #signed(ITYPE, I2) =/=Int #pow1(ITYPE)
  rule _ITYPE . div_s _I1 I2 => undefined
      requires I2 ==Int 0
  rule ITYPE . div_s I1 I2 => undefined
      requires I2 =/=Int 0
       andBool #signed(ITYPE, I1) /Int #signed(ITYPE, I2) ==Int #pow1(ITYPE)
  rule ITYPE . rem_s I1 I2 => < ITYPE > #unsigned(ITYPE, #signed(ITYPE, I1) %Int #signed(ITYPE, I2))
      requires I2 =/=Int 0
  rule _ITYPE . rem_s _I1 I2 => undefined
      requires I2 ==Int 0
  rule ITYPE . and I1 I2 =>       < ITYPE > I1 &Int   I2
  rule ITYPE . or  I1 I2 => #chop(< ITYPE > I1 |Int   I2)
  rule ITYPE . xor I1 I2 => #chop(< ITYPE > I1 xorInt I2)
  rule ITYPE . shl   I1 I2 => #chop(< ITYPE > I1 <<Int (I2 %Int #width(ITYPE)))
  rule ITYPE . shr_u I1 I2 =>       < ITYPE > I1 >>Int (I2 %Int #width(ITYPE))
  rule ITYPE . shr_s I1 I2 => < ITYPE > #unsigned(ITYPE, #signed(ITYPE, I1) >>Int (I2 %Int #width(ITYPE)))
  rule ITYPE . rotl I1 I2 => #chop(< ITYPE > (I1 <<Int (I2 %Int #width(ITYPE))) +Int (I1 >>Int (#width(ITYPE) -Int (I2 %Int #width(ITYPE)))))
  rule ITYPE . rotr I1 I2 => #chop(< ITYPE > (I1 >>Int (I2 %Int #width(ITYPE))) +Int (I1 <<Int (#width(ITYPE) -Int (I2 %Int #width(ITYPE)))))
  rule FTYPE:FValType . add      F1 F2 => < FTYPE > F1 +Float F2
  rule FTYPE:FValType . sub      F1 F2 => < FTYPE > F1 -Float F2
  rule FTYPE:FValType . mul      F1 F2 => < FTYPE > F1 *Float F2
  rule FTYPE          . div      F1 F2 => < FTYPE > F1 /Float F2
  rule FTYPE          . min      F1 F2 => < FTYPE > minFloat (F1, F2)
  rule FTYPE          . max      F1 F2 => < FTYPE > maxFloat (F1, F2)
  rule FTYPE          . copysign F1 F2 => < FTYPE > F1                requires signFloat (F1) ==Bool  signFloat (F2)
  rule FTYPE          . copysign F1 F2 => < FTYPE > --Float  F1       requires signFloat (F1) =/=Bool signFloat (F2)
  syntax Val  ::=
    IValType "." TestOp Int [function, klabel(intTestOp)]
  rule _ . eqz I => < i32 > #bool(I ==Int 0)
  syntax Val  ::=
    IValType "." IRelOp Int Int [function, klabel(intRelOp)]
  | FValType "." FRelOp Float Float [function, klabel(floatRelOp)]
  rule _:IValType . eq I1 I2 => < i32 > #bool(I1 ==Int  I2)
  rule _:IValType . ne I1 I2 => < i32 > #bool(I1 =/=Int I2)
  rule _     . lt_u I1 I2 => < i32 > #bool(I1 <Int I2)
  rule _     . gt_u I1 I2 => < i32 > #bool(I1 >Int I2)
  rule ITYPE . lt_s I1 I2 => < i32 > #bool(#signed(ITYPE, I1) <Int #signed(ITYPE, I2))
  rule ITYPE . gt_s I1 I2 => < i32 > #bool(#signed(ITYPE, I1) >Int #signed(ITYPE, I2))
  rule _     . le_u I1 I2 => < i32 > #bool(I1 <=Int I2)
  rule _     . ge_u I1 I2 => < i32 > #bool(I1 >=Int I2)
  rule ITYPE . le_s I1 I2 => < i32 > #bool(#signed(ITYPE, I1) <=Int #signed(ITYPE, I2))
  rule ITYPE . ge_s I1 I2 => < i32 > #bool(#signed(ITYPE, I1) >=Int #signed(ITYPE, I2))
  rule _          . lt F1 F2 => < i32 > #bool(F1 <Float   F2)
  rule _          . gt F1 F2 => < i32 > #bool(F1 >Float   F2)
  rule _          . le F1 F2 => < i32 > #bool(F1 <=Float  F2)
  rule _          . ge F1 F2 => < i32 > #bool(F1 >=Float  F2)
  rule _:FValType . eq F1 F2 => < i32 > #bool(F1 ==Float  F2)
  rule _:FValType . ne F1 F2 => < i32 > #bool(F1 =/=Float F2)
  syntax Val  ::=
    ValType "." CvtOp Number [function, klabel(numberCvtOp)]
  rule i32 . wrap_i64 I => #chop(< i32 > I)
  rule i64 . extend_i32_u I:Int => < i64 > I
  rule i64 . extend_i32_s I:Int => < i64 > #unsigned(i64, #signed(i32, I))
  rule FTYPE . convert_i32_s I:Int => #round( FTYPE , #signed(i32, I) )
  rule FTYPE . convert_i32_u I:Int => #round( FTYPE , I )
  rule FTYPE . convert_i64_s I:Int => #round( FTYPE , #signed(i64, I) )
  rule FTYPE . convert_i64_u I:Int => #round( FTYPE , I )
  rule f64 . promote_f32 F => #round( f64 , F )
  rule f32 . demote_f64  F => #round( f32 , F )
  rule ITYPE . trunc_f32_s F => undefined
      requires #isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow1(ITYPE)) orBool (0 -Int Float2Int(truncFloat(F)) >Int #pow1 (ITYPE))
  rule ITYPE . trunc_f32_u F => undefined
      requires #isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow (ITYPE)) orBool (Float2Int(truncFloat(F)) <Int 0)
  rule ITYPE . trunc_f32_s F => <ITYPE> #unsigned(ITYPE, Float2Int(truncFloat(F)))
      requires notBool (#isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow1(ITYPE)) orBool (0 -Int Float2Int(truncFloat(F)) >Int #pow1 (ITYPE)))
  rule ITYPE . trunc_f32_u F => <ITYPE> Float2Int(truncFloat(F))
      requires notBool (#isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow (ITYPE)) orBool (Float2Int(truncFloat(F)) <Int 0))
  rule ITYPE . trunc_f64_s F => undefined
      requires #isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow1(ITYPE)) orBool (0 -Int Float2Int(truncFloat(F)) >Int #pow1 (ITYPE))
  rule ITYPE . trunc_f64_u F => undefined
      requires #isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow (ITYPE)) orBool (Float2Int(truncFloat(F)) <Int 0)
  rule ITYPE . trunc_f64_s F => <ITYPE> #unsigned(ITYPE, Float2Int(truncFloat(F)))
      requires notBool (#isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow1(ITYPE)) orBool (0 -Int Float2Int(truncFloat(F)) >Int #pow1 (ITYPE)))
  rule ITYPE . trunc_f64_u F => <ITYPE> Float2Int(truncFloat(F))
      requires notBool (#isInfinityOrNaN (F) orBool (Float2Int(truncFloat(F)) >=Int #pow (ITYPE)) orBool (Float2Int(truncFloat(F)) <Int 0))
endmodule

module WASM-SYNTAX
  imports public WASM-DATA-SYNTAX
  imports public WASM-COMMON-SYNTAX
  imports public WASM-NUMERIC-SYNTAX
endmodule

module WASM-COMMON-SYNTAX
  imports public WASM-DATA-COMMON-SYNTAX
  imports public WASM-NUMERIC
  syntax Instr  ::=
    PlainInstr
  syntax EmptyStmt
  syntax Instr  ::=
    EmptyStmt
  syntax Defn  ::=
    EmptyStmt
  syntax Stmt  ::=
    Instr
  | Defn
  syntax EmptyStmts  ::=
    List{EmptyStmt,""} [overload(listStmt), symbol(listStmt)]
  syntax Instrs  ::=
    List{Instr,""} [overload(listStmt)]
  syntax Defns  ::=
    List{Defn,""} [overload(listStmt)]
  syntax Stmts  ::=
    List{Stmt,""} [overload(listStmt)]
  syntax Instrs  ::=
    EmptyStmts
  syntax Defns  ::=
    EmptyStmts
  syntax Stmts  ::=
    Instrs
  | Defns
  syntax PlainInstr  ::=
    IValType "." "const" WasmInt [klabel(aIConst), symbol]
  | FValType "." "const" Number [klabel(aFConst), symbol]
  | IValType "." IUnOp [klabel(aIUnOp), symbol]
  | FValType "." FUnOp [klabel(aFUnOp), symbol]
  | IValType "." IBinOp [klabel(aIBinOp), symbol]
  | FValType "." FBinOp [klabel(aFBinOp), symbol]
  | IValType "." TestOp [klabel(aTestOp), symbol]
  | IValType "." IRelOp [klabel(aIRelOp), symbol]
  | FValType "." FRelOp [klabel(aFRelOp), symbol]
  | ValType "." CvtOp [klabel(aCvtOp), symbol]
  | "drop" [klabel(aDrop), symbol]
  | "select" [klabel(aSelect), symbol]
  | "nop" [klabel(aNop), symbol]
  | "unreachable" [klabel(aUnreachable), symbol]
  | "return" [klabel(aReturn), symbol]
  | "memory.size" [klabel(aSize), symbol]
  | "memory.grow" [klabel(aGrow), symbol]
  syntax PlainInstr  ::=
    "call_indirect" TypeUse
  syntax TypeUse  ::=
    TypeDecls
  | "(type" Index ")" [prefer]
  | "(type" Index ")" TypeDecls
  syntax TypeKeyWord  ::=
    "param"
  | "result"
  syntax TypeDecl  ::=
    "(" TypeDecl ")" [bracket]
  | TypeKeyWord ValTypes
  | "param" Identifier ValType
  syntax TypeDecls  ::=
    List{TypeDecl,""} [symbol(listTypeDecl)]
  syntax StoreOp  ::=
    "store" [klabel(storeOpStore), symbol]
  | "store8" [klabel(storeOpStore8), symbol]
  | "store16" [klabel(storeOpStore16), symbol]
  | "store32" [klabel(storeOpStore32), symbol]
  syntax LoadOp  ::=
    "load" [klabel(loadOpLoad), symbol]
  | "load8_u" [klabel(loadOpLoad8_u), symbol]
  | "load16_u" [klabel(loadOpLoad16_u), symbol]
  | "load32_u" [klabel(loadOpLoad32_u), symbol]
  | "load8_s" [klabel(loadOpLoad8_s), symbol]
  | "load16_s" [klabel(loadOpLoad16_s), symbol]
  | "load32_s" [klabel(loadOpLoad32_s), symbol]
  syntax Defn  ::=
    TypeDefn
  | GlobalDefn
  | FuncDefn
  | TableDefn
  | MemoryDefn
  | ElemDefn
  | DataDefn
  | StartDefn
  | ExportDefn
  | ImportDefn
  syntax TypeDefn
  syntax GlobalDefn
  syntax FuncDefn
  syntax TableDefn
  syntax MemoryDefn
  syntax ElemDefn
  syntax DataDefn
  syntax StartDefn
  syntax ImportDefn
  syntax ExportDefn
endmodule

module WASM
  imports public WASM-COMMON-SYNTAX
  imports public WASM-DATA
  imports public WASM-NUMERIC
  configuration <wasm>
        <instrs> .K </instrs>
        <valstack> .ValStack </valstack>
        <curFrame>
          <locals>    .Map </locals>
          <curModIdx> .Int </curModIdx>
        </curFrame>
        <moduleRegistry> .Map </moduleRegistry>
        <moduleIds> .Map </moduleIds>
        <moduleInstances>
          <moduleInst multiplicity="*" type="Map">
            <modIdx>      0    </modIdx>
            <exports>     .Map </exports>
            <types>       .Map </types>
            <nextTypeIdx> 0    </nextTypeIdx>
            <funcAddrs>   .Map </funcAddrs>
            <nextFuncIdx> 0    </nextFuncIdx>
            <tabIds>      .Map </tabIds>
            <tabAddrs>    .Map </tabAddrs>
            <memIds>      .Map </memIds>
            <memAddrs>    .Map </memAddrs>
            <globIds>     .Map </globIds>
            <globalAddrs> .Map </globalAddrs>
            <nextGlobIdx> 0    </nextGlobIdx>
            <moduleMetadata>
              <moduleFileName> .String </moduleFileName>
              <moduleId>              </moduleId>
              <funcIds>        .Map   </funcIds>
              <typeIds>        .Map   </typeIds>
            </moduleMetadata>
          </moduleInst>
        </moduleInstances>
        <nextModuleIdx> 0 </nextModuleIdx>
        <mainStore>
          <funcs>
            <funcDef multiplicity="*" type="Map">
              <fAddr>    0              </fAddr>
              <fCode>    .Instrs:Instrs </fCode>
              <fType>    .Type          </fType>
              <fLocal>   .Type          </fLocal>
              <fModInst> 0              </fModInst>
              <funcMetadata>
                <funcId> </funcId>
                <localIds> .Map </localIds>
              </funcMetadata>
            </funcDef>
          </funcs>
          <nextFuncAddr> 0 </nextFuncAddr>
          <tabs>
            <tabInst multiplicity="*" type="Map">
              <tAddr> 0    </tAddr>
              <tmax>  .Int </tmax>
              <tsize> 0    </tsize>
              <tdata> .Map </tdata>
            </tabInst>
          </tabs>
          <nextTabAddr> 0 </nextTabAddr>
          <mems>
            <memInst multiplicity="*" type="Map">
              <mAddr> 0      </mAddr>
              <mmax>  .Int   </mmax>
              <msize> 0      </msize>
              <mdata> .Bytes </mdata>
            </memInst>
          </mems>
          <nextMemAddr> 0 </nextMemAddr>
          <globals>
            <globalInst multiplicity="*" type="Map">
              <gAddr>  0         </gAddr>
              <gValue> undefined </gValue>
              <gMut>   .Mut      </gMut>
            </globalInst>
          </globals>
          <nextGlobAddr> 0 </nextGlobAddr>
        </mainStore>
        <deterministicMemoryGrowth> true </deterministicMemoryGrowth>
      </wasm>
  syntax Stmts  ::=
    "text2abstract" "(" Stmts ")" [function, klabel(text2abstract)]
  syntax K  ::=
    "sequenceStmts" "(" Stmts ")" [function, klabel(sequenceStmts)]
  | "sequenceDefns" "(" Defns ")" [function, klabel(sequenceDefns)]
  | "sequenceInstrs" "(" Instrs ")" [function, klabel(sequenceInstrs)]
  rule sequenceStmts(.Stmts) => .
  rule sequenceStmts(S SS  ) => S ~> sequenceStmts(SS)
  rule sequenceDefns(.Defns) => .
  rule sequenceDefns(D DS  ) => D ~> sequenceDefns(DS)
  rule sequenceInstrs(.Instrs) => .
  rule sequenceInstrs(I IS   ) => I ~> sequenceInstrs(IS)
  syntax Instr  ::=
    "trap"
  rule <instrs> trap ~> (_L:Label => .) ... </instrs>
  rule <instrs> trap ~> (_F:Frame => .) ... </instrs>
  rule <instrs> trap ~> (_I:Instr => .) ... </instrs>
  rule <instrs> trap ~> (_D:Defn  => .) ... </instrs>
  rule <instrs> undefined => trap ... </instrs>
  rule <instrs>   V:Val    => .        ... </instrs>
         <valstack> VALSTACK => V : VALSTACK </valstack>
      requires V =/=K undefined
  rule <instrs> ITYPE:IValType . const VAL => #chop (< ITYPE > VAL) ... </instrs>
  rule <instrs> FTYPE:FValType . const VAL => #round(  FTYPE , VAL) ... </instrs>
  rule <instrs> ITYPE . UOP:IUnOp => ITYPE . UOP C1 ... </instrs>
         <valstack> < ITYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> FTYPE . UOP:FUnOp => FTYPE . UOP C1 ... </instrs>
         <valstack> < FTYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> ITYPE . BOP:IBinOp => ITYPE . BOP C1 C2 ... </instrs>
         <valstack> < ITYPE > C2 : < ITYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> FTYPE . BOP:FBinOp => FTYPE . BOP C1 C2 ... </instrs>
         <valstack> < FTYPE > C2 : < FTYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> TYPE . TOP:TestOp => TYPE . TOP C1 ... </instrs>
         <valstack> < TYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> ITYPE . ROP:IRelOp => ITYPE . ROP C1 C2 ... </instrs>
         <valstack> < ITYPE > C2 : < ITYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> FTYPE . ROP:FRelOp => FTYPE . ROP C1 C2 ... </instrs>
         <valstack> < FTYPE > C2 : < FTYPE > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> TYPE:ValType . CVTOP:Cvti32Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < i32 > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> TYPE:ValType . CVTOP:Cvti64Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < i64 > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> TYPE:ValType . CVTOP:Cvtf32Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < f32 > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> TYPE:ValType . CVTOP:Cvtf64Op => TYPE . CVTOP C1  ... </instrs>
         <valstack> < f64 > C1 : VALSTACK => VALSTACK </valstack>
  rule <instrs> drop => . ... </instrs>
         <valstack> _ : VALSTACK => VALSTACK </valstack>
  rule <instrs> select => . ... </instrs>
         <valstack>
           < i32 > C : < TYPE > V2:Number : < TYPE > V1:Number : VALSTACK
      =>   < TYPE > #if C =/=Int 0 #then V1 #else V2 #fi       : VALSTACK
         </valstack>
  rule <instrs> nop => . ... </instrs>
  rule <instrs> unreachable => trap ... </instrs>
  syntax Label  ::=
    "label" VecType "{" Instrs "}" ValStack
  rule <instrs> label [ TYPES ] { _ } VALSTACK' => . ... </instrs>
         <valstack> VALSTACK => #take(lengthValTypes(TYPES), VALSTACK) ++ VALSTACK' </valstack>
  syntax BlockMetaData  ::=
    OptionalInt
  syntax Instr  ::=
    "#block" "(" VecType "," Instrs "," BlockMetaData ")" [klabel(aBlock), symbol]
  rule <instrs> #block(VECTYP, IS, _) => sequenceInstrs(IS) ~> label VECTYP { .Instrs } VALSTACK ... </instrs>
         <valstack> VALSTACK => .ValStack </valstack>
  syntax Instr  ::=
    "#br" "(" Int ")" [klabel(aBr), symbol]
  rule <instrs> #br(_IDX) ~> (_S:Stmt => .) ... </instrs>
  rule <instrs> #br(0   ) ~> label [ TYPES ] { IS } VALSTACK' => sequenceInstrs(IS) ... </instrs>
         <valstack> VALSTACK => #take(lengthValTypes(TYPES), VALSTACK) ++ VALSTACK' </valstack>
  rule <instrs> #br(N:Int) ~> _L:Label => #br(N -Int 1) ... </instrs>
      requires N >Int 0
  syntax Instr  ::=
    "#br_if" "(" Int ")" [klabel(aBr_if), symbol]
  rule <instrs> #br_if(IDX) => #br(IDX) ... </instrs>
         <valstack> < _TYPE > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL =/=Int 0
  rule <instrs> #br_if(_IDX) => .    ... </instrs>
         <valstack> < _TYPE > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL  ==Int 0
  syntax Instr  ::=
    "#br_table" "(" Ints ")" [klabel(aBr_table), symbol]
  rule <instrs> #br_table(ES) => #br(#getInts(ES, minInt(VAL, #lenInts(ES) -Int 1))) ... </instrs>
         <valstack> < _TYPE > VAL : VALSTACK => VALSTACK </valstack>
  syntax Instr  ::=
    "#if" "(" VecType "," then: Instrs "," else: Instrs "," blockInfo: BlockMetaData ")" [klabel(aIf), symbol]
  rule <instrs> #if(VECTYP, IS, _, _)  => sequenceInstrs(IS) ~> label VECTYP { .Instrs } VALSTACK ... </instrs>
         <valstack> < i32 > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL =/=Int 0
  rule <instrs> #if(VECTYP, _, IS, _) => sequenceInstrs(IS) ~> label VECTYP { .Instrs } VALSTACK ... </instrs>
         <valstack> < i32 > VAL : VALSTACK => VALSTACK </valstack>
      requires VAL ==Int 0
  syntax Instr  ::=
    "#loop" "(" VecType "," Instrs "," BlockMetaData ")" [klabel(aLoop), symbol]
  rule <instrs> #loop(VECTYP, IS, BLOCKMETA) => sequenceInstrs(IS) ~> label VECTYP { #loop(VECTYP, IS, BLOCKMETA) } VALSTACK ... </instrs>
         <valstack> VALSTACK => .ValStack </valstack>
  syntax Instr  ::=
    "init_local" Int Val
  | "init_locals" ValStack
  | "#init_locals" Int ValStack
  rule <instrs> init_local INDEX VALUE => . ... </instrs>
         <locals> LOCALS => LOCALS [ INDEX <- VALUE ] </locals>
  rule <instrs> init_locals VALUES => #init_locals 0 VALUES ... </instrs>
  rule <instrs> #init_locals _ .ValStack => . ... </instrs>
  rule <instrs> #init_locals N (VALUE : VALSTACK)
               => init_local N VALUE
               ~> #init_locals (N +Int 1) VALSTACK
               ...
          </instrs>
  syntax Instr  ::=
    "#local.get" "(" Int ")" [klabel(aLocal.get), symbol]
  | "#local.set" "(" Int ")" [klabel(aLocal.set), symbol]
  | "#local.tee" "(" Int ")" [klabel(aLocal.tee), symbol]
  rule <instrs> #local.get(I) => . ... </instrs>
         <valstack> VALSTACK => VALUE : VALSTACK </valstack>
         <locals> ... I |-> VALUE ... </locals>
  rule <instrs> #local.set(I) => . ... </instrs>
         <valstack> VALUE : VALSTACK => VALSTACK </valstack>
         <locals> ... I |-> (_ => VALUE) ... </locals>
  rule <instrs> #local.tee(I) => . ... </instrs>
         <valstack> VALUE : _VALSTACK </valstack>
         <locals> ... I |-> (_ => VALUE) ... </locals>
  syntax GlobalType  ::=
    Mut ValType [klabel(aGlobalType), symbol]
  syntax GlobalDefn  ::=
    "#global" "(" type: GlobalType "," init: Instrs "," metadata: OptionalId ")" [klabel(aGlobalDefn), symbol]
  syntax Alloc  ::=
    "allocglobal" "(" OptionalId "," GlobalType ")" [klabel(allocglobal)]
  rule <instrs> #global(... type: TYP, init: IS, metadata: OID) => sequenceInstrs(IS) ~> allocglobal(OID, TYP) ... </instrs>
  rule <instrs> allocglobal(OID:OptionalId, MUT:Mut TYP:ValType) => . ... </instrs>
         <valstack> < TYP > VAL : STACK => STACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS => #saveId(IDS, OID, NEXTIDX) </globIds>
           <nextGlobIdx> NEXTIDX => NEXTIDX +Int 1                </nextGlobIdx>
           <globalAddrs> GLOBS   => GLOBS [ NEXTIDX <- NEXTADDR ] </globalAddrs>
           ...
         </moduleInst>
         <nextGlobAddr> NEXTADDR => NEXTADDR +Int 1 </nextGlobAddr>
         <globals>
           ( .Bag
          => <globalInst>
               <gAddr>  NEXTADDR  </gAddr>
               <gValue> <TYP> VAL </gValue>
               <gMut>   MUT       </gMut>
             </globalInst>
           )
           ...
         </globals>
  syntax Instr  ::=
    "#global.get" "(" Int ")" [klabel(aGlobal.get), symbol]
  | "#global.set" "(" Int ")" [klabel(aGlobal.set), symbol]
  rule <instrs> #global.get(IDX) => . ... </instrs>
         <valstack> VALSTACK => VALUE : VALSTACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globalAddrs> ... IDX |-> GADDR ... </globalAddrs>
           ...
         </moduleInst>
         <globalInst>
           <gAddr>  GADDR </gAddr>
           <gValue> VALUE </gValue>
           ...
         </globalInst>
  rule <instrs> #global.set(IDX) => . ... </instrs>
         <valstack> VALUE : VALSTACK => VALSTACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globalAddrs> ... IDX |-> GADDR ... </globalAddrs>
           ...
         </moduleInst>
         <globalInst>
           <gAddr>  GADDR      </gAddr>
           <gValue> _ => VALUE </gValue>
           ...
         </globalInst>
  syntax VecType  ::=
    "gatherTypes" "(" TypeKeyWord "," TypeDecls ")" [function, klabel(gatherTypes)]
  | "#gatherTypes" "(" TypeKeyWord "," TypeDecls "," ValTypes ")" [function, klabel(#gatherTypes)]
  rule gatherTypes(TKW , TDECLS:TypeDecls) => #gatherTypes(TKW, TDECLS, .ValTypes)
  rule #gatherTypes( _  ,                                   .TypeDecls , TYPES) => [ TYPES ]
  rule #gatherTypes(TKW , TKW':TypeKeyWord _:ValTypes TDECLS:TypeDecls , TYPES) => #gatherTypes(TKW, TDECLS, TYPES) requires TKW =/=K TKW'
  rule #gatherTypes(TKW , TKW         TYPES':ValTypes TDECLS:TypeDecls , TYPES)
      => #gatherTypes(TKW ,                             TDECLS:TypeDecls , TYPES + TYPES')
  rule #gatherTypes(result , param _ID:Identifier     _:ValType TDECLS:TypeDecls , TYPES) => #gatherTypes(result , TDECLS , TYPES)
  rule #gatherTypes(param  , param _ID:Identifier VTYPE:ValType TDECLS:TypeDecls , TYPES) => #gatherTypes(param  , TDECLS , TYPES + VTYPE .ValTypes)
  syntax FuncType  ::=
    "asFuncType" "(" TypeDecls ")" [function, klabel(TypeDeclsAsFuncType)]
  | "asFuncType" "(" Map "," Map "," TypeUse ")" [function, klabel(TypeUseAsFuncType)]
  rule asFuncType(TDECLS:TypeDecls)                       => gatherTypes(param, TDECLS) -> gatherTypes(result, TDECLS)
  rule asFuncType(   _   ,   _  , TDECLS:TypeDecls)       => asFuncType(TDECLS)
  rule asFuncType(TYPEIDS, TYPES, (type TFIDX ))          => {TYPES[#ContextLookup(TYPEIDS ,TFIDX)]}:>FuncType
  rule asFuncType(TYPEIDS, TYPES, (type TFIDX ) TDECLS )  => asFuncType(TDECLS)
      requires TYPES[#ContextLookup(TYPEIDS, TFIDX)] ==K asFuncType(TDECLS)
  syntax TypeDefn  ::=
    "#type" "(" type: FuncType "," metadata: OptionalId ")" [klabel(aTypeDefn), symbol]
  syntax Alloc  ::=
    "alloctype" "(" OptionalId "," FuncType ")" [klabel(alloctype)]
  rule <instrs> #type(... type: TYPE, metadata: OID) => alloctype(OID, TYPE) ... </instrs>
  rule <instrs> alloctype(OID, TYPE) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <typeIds> IDS => #saveId(IDS, OID, NEXTIDX) </typeIds>
           <nextTypeIdx> NEXTIDX => NEXTIDX +Int 1 </nextTypeIdx>
           <types> TYPES => TYPES [NEXTIDX <- TYPE] </types>
           ...
         </moduleInst>
  syntax FuncDefn  ::=
    "#func" "(" type: Int "," locals: VecType "," body: Instrs "," metadata: FuncMetadata ")" [klabel(aFuncDefn), symbol]
  syntax Alloc  ::=
    "allocfunc" "(" Int "," Int "," FuncType "," VecType "," Instrs "," FuncMetadata ")" [klabel(allocfunc)]
  rule <instrs> #func(... type: TYPIDX, locals: LOCALS, body: INSTRS, metadata: META) => allocfunc(CUR, NEXTADDR, TYPE, LOCALS, INSTRS, META) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types>  ... TYPIDX |-> TYPE ... </types>
           <nextFuncIdx> NEXTIDX => NEXTIDX +Int 1 </nextFuncIdx>
           <funcAddrs> ADDRS => ADDRS [ NEXTIDX <- NEXTADDR ] </funcAddrs>
           ...
         </moduleInst>
         <nextFuncAddr> NEXTADDR => NEXTADDR +Int 1 </nextFuncAddr>
  rule <instrs> allocfunc(MOD, ADDR, TYPE, LOCALS, INSTRS, #meta(... id: OID, localIds: LIDS)) => . ... </instrs>
         <funcs>
           ( .Bag
          => <funcDef>
               <fAddr>    ADDR </fAddr>
               <fCode>    INSTRS   </fCode>
               <fType>    TYPE     </fType>
               <fLocal>   LOCALS   </fLocal>
               <fModInst> MOD      </fModInst>
               <funcMetadata>
                 <funcId> OID </funcId>
                 <localIds> LIDS </localIds>
                 ...
               </funcMetadata>
             </funcDef>
           )
           ...
         </funcs>
  syntax FuncMetadata  ::=
    "#meta" "(" id: OptionalId "," localIds: Map ")" [klabel(funcMeta), symbol]
  syntax Frame  ::=
    "frame" Int ValTypes ValStack Map
  rule <instrs> frame MODIDX' TRANGE VALSTACK' LOCAL' => . ... </instrs>
         <valstack> VALSTACK => #take(lengthValTypes(TRANGE), VALSTACK) ++ VALSTACK' </valstack>
         <locals> _ => LOCAL' </locals>
         <curModIdx> _ => MODIDX' </curModIdx>
  syntax Instr  ::=
    "(" "invoke" Int ")"
  rule <instrs> ( invoke FADDR )
               => init_locals #revs(#take(lengthValTypes(TDOMAIN), VALSTACK)) ++ #zero(TLOCALS)
               ~> #block([TRANGE], INSTRS, .Int)
               ~> frame MODIDX TRANGE #drop(lengthValTypes(TDOMAIN), VALSTACK) LOCAL
               ...
         </instrs>
         <valstack>  VALSTACK => .ValStack </valstack>
         <locals> LOCAL => .Map </locals>
         <curModIdx> MODIDX => MODIDX' </curModIdx>
         <funcDef>
           <fAddr>    FADDR                     </fAddr>
           <fCode>    INSTRS                    </fCode>
           <fType>    [ TDOMAIN ] -> [ TRANGE ] </fType>
           <fLocal>   [ TLOCALS ]               </fLocal>
           <fModInst> MODIDX'                   </fModInst>
           ...
         </funcDef>
  rule <instrs> return ~> (_S:Stmt  => .)  ... </instrs>
  rule <instrs> return ~> (_L:Label => .)  ... </instrs>
  rule <instrs> (return => .) ~> _FR:Frame ... </instrs>
  syntax Instr  ::=
    "#call" "(" Int ")" [klabel(aCall), symbol]
  rule <instrs> #call(IDX) => ( invoke FADDR ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <funcAddrs> ... IDX |-> FADDR ... </funcAddrs>
           ...
         </moduleInst>
  syntax Instr  ::=
    "#call_indirect" "(" Int ")" [klabel(aCall_indirect), symbol]
  rule <instrs> #call_indirect(I) => call_indirect (type I) ... </instrs>
  rule <instrs> call_indirect TUSE:TypeUse => ( invoke FADDR ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <typeIds> TYPEIDS </typeIds>
           <types> TYPES </types>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tdata> ... IDX |-> FADDR ... </tdata>
           ...
         </tabInst>
         <funcDef>
           <fAddr> FADDR </fAddr>
           <fType> FTYPE </fType>
           ...
         </funcDef>
      requires asFuncType(TYPEIDS, TYPES, TUSE) ==K FTYPE
  rule <instrs> call_indirect TUSE:TypeUse => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <typeIds> TYPEIDS </typeIds>
           <types> TYPES </types>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tdata> ... IDX |-> FADDR ... </tdata>
           ...
         </tabInst>
         <funcDef>
           <fAddr> FADDR </fAddr>
           <fType> FTYPE </fType>
           ...
         </funcDef>
      requires asFuncType(TYPEIDS, TYPES, TUSE) =/=K FTYPE
  rule <instrs> call_indirect _TUSE:TypeUse => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR  </tAddr>
           <tdata> TDATA </tdata>
           ...
         </tabInst>
      requires notBool IDX in_keys(TDATA)
  syntax TableDefn  ::=
    "#table" "(" limits: Limits "," metadata: OptionalId ")" [klabel(aTableDefn), symbol]
  syntax Alloc  ::=
    "alloctable" "(" OptionalId "," Int "," OptionalInt ")" [klabel(alloctable)]
  rule <instrs> #table(... limits: #limitsMin(MIN), metadata: OID)   => alloctable(OID, MIN, .Int) ... </instrs>
      requires MIN <=Int #maxTableSize()
  rule <instrs> #table(... limits: #limits(MIN, MAX), metadata: OID) => alloctable(OID, MIN, MAX) ... </instrs>
      requires MIN <=Int #maxTableSize()
       andBool MAX <=Int #maxTableSize()
  rule <instrs> alloctable(ID, MIN, MAX) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabIds> IDS => #saveId(IDS, ID, 0) </tabIds>
           <tabAddrs> .Map => (0 |-> NEXTADDR) </tabAddrs>
           ...
         </moduleInst>
         <nextTabAddr> NEXTADDR => NEXTADDR +Int 1 </nextTabAddr>
         <tabs>
           ( .Bag
          => <tabInst>
               <tAddr>   NEXTADDR </tAddr>
               <tmax>    MAX      </tmax>
               <tsize>   MIN      </tsize>
               <tdata>   .Map     </tdata>
             </tabInst>
           )
           ...
         </tabs>
  syntax MemoryDefn  ::=
    "#memory" "(" limits: Limits "," metadata: OptionalId ")" [klabel(aMemoryDefn), symbol]
  syntax Alloc  ::=
    "allocmemory" "(" OptionalId "," Int "," OptionalInt ")" [klabel(allocmemory)]
  rule <instrs> #memory(... limits: #limitsMin(MIN),   metadata: OID) => allocmemory(OID, MIN, .Int) ... </instrs>
      requires MIN <=Int #maxMemorySize()
  rule <instrs> #memory(... limits: #limits(MIN, MAX), metadata: OID) => allocmemory(OID, MIN, MAX)  ... </instrs>
      requires MIN <=Int #maxMemorySize()
       andBool MAX <=Int #maxMemorySize()
  rule <instrs> allocmemory(ID, MIN, MAX) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memIds> IDS => #saveId(IDS, ID, 0) </memIds>
           <memAddrs> .Map => (0 |-> NEXTADDR) </memAddrs>
           ...
         </moduleInst>
         <nextMemAddr> NEXTADDR => NEXTADDR +Int 1 </nextMemAddr>
         <mems>
           ( .Bag
          => <memInst>
               <mAddr>   NEXTADDR </mAddr>
               <mmax>    MAX      </mmax>
               <msize>   MIN      </msize>
               ...
             </memInst>
           )
           ...
         </mems>
  syntax Instr  ::=
    "#store" "(" ValType "," StoreOp "," offset: Int ")" [klabel(aStore), symbol]
  | IValType "." StoreOp Int Int
  | "store" "{" Int Int Number "}"
  rule <instrs> #store(ITYPE:IValType, SOP, OFFSET) => ITYPE . SOP (IDX +Int OFFSET) VAL ... </instrs>
         <valstack> < ITYPE > VAL : < i32 > IDX : VALSTACK => VALSTACK </valstack>
  rule <instrs> store { WIDTH EA VAL } => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           <mdata>   DATA => #setRange(DATA, EA, VAL, WIDTH) </mdata>
           ...
         </memInst>
         requires (EA +Int WIDTH) <=Int (SIZE *Int #pageSize())
  rule <instrs> store { WIDTH  EA  _ } => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           ...
         </memInst>
         requires (EA +Int WIDTH) >Int (SIZE *Int #pageSize())
  rule <instrs> ITYPE . store   EA VAL => store { #numBytes(ITYPE) EA VAL           } ... </instrs>
  rule <instrs> _     . store8  EA VAL => store { 1                EA #wrap(1, VAL) } ... </instrs>
  rule <instrs> _     . store16 EA VAL => store { 2                EA #wrap(2, VAL) } ... </instrs>
  rule <instrs> i64   . store32 EA VAL => store { 4                EA #wrap(4, VAL) } ... </instrs>
  syntax Instr  ::=
    "#load" "(" ValType "," LoadOp "," offset: Int ")" [klabel(aLoad), symbol]
  | "load" "{" IValType Int Int Signedness "}"
  | "load" "{" IValType Int Int Signedness Bytes "}"
  | "load" "{" IValType Int Int Signedness "}"
  | IValType "." LoadOp Int
  rule <instrs> #load(ITYPE:IValType, LOP, OFFSET) => ITYPE . LOP (IDX +Int OFFSET)  ... </instrs>
         <valstack> < i32 > IDX : VALSTACK => VALSTACK </valstack>
  rule <instrs> ITYPE . load     EA:Int => load { ITYPE #numBytes(ITYPE) EA Unsigned } ... </instrs>
  rule <instrs> ITYPE . load8_u  EA:Int => load { ITYPE 1                EA Unsigned } ... </instrs>
  rule <instrs> ITYPE . load16_u EA:Int => load { ITYPE 2                EA Unsigned } ... </instrs>
  rule <instrs> i64   . load32_u EA:Int => load { i64   4                EA Unsigned } ... </instrs>
  rule <instrs> ITYPE . load8_s  EA:Int => load { ITYPE 1                EA Signed   } ... </instrs>
  rule <instrs> ITYPE . load16_s EA:Int => load { ITYPE 2                EA Signed   } ... </instrs>
  rule <instrs> i64   . load32_s EA:Int => load { i64   4                EA Signed   } ... </instrs>
  rule <instrs> load { ITYPE WIDTH EA SIGN } => load { ITYPE WIDTH EA SIGN DATA } ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           <mdata>   DATA </mdata>
           ...
         </memInst>
      requires (EA +Int WIDTH) <=Int (SIZE *Int #pageSize())
  rule <instrs> load { _ WIDTH EA _ } => trap ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           ...
         </memInst>
      requires (EA +Int WIDTH) >Int (SIZE *Int #pageSize())
  rule <instrs> load { ITYPE WIDTH EA   Signed DATA } => #chop(< ITYPE > #signedWidth(WIDTH, #getRange(DATA, EA, WIDTH))) ... </instrs>
  rule <instrs> load { ITYPE WIDTH EA Unsigned DATA } => < ITYPE > #getRange(DATA, EA, WIDTH) ... </instrs>
  rule <instrs> memory.size => < i32 > SIZE ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <msize>   SIZE </msize>
           ...
         </memInst>
  syntax Instr  ::=
    "grow" Int
  rule <instrs> memory.grow => grow N ... </instrs>
         <valstack> < i32 > N : VALSTACK => VALSTACK </valstack>
  rule <instrs> grow N => < i32 > SIZE ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <mmax>    MAX  </mmax>
           <msize>   SIZE => SIZE +Int N </msize>
           ...
         </memInst>
      requires #growthAllowed(SIZE +Int N, MAX)
  rule <instrs> grow N => < i32 > #unsigned(i32, -1) ... </instrs>
         <deterministicMemoryGrowth> DET:Bool </deterministicMemoryGrowth>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr>   ADDR </mAddr>
           <mmax>    MAX  </mmax>
           <msize>   SIZE </msize>
           ...
         </memInst>
      requires notBool DET
        orBool notBool #growthAllowed(SIZE +Int N, MAX)
  syntax Bool  ::=
    "#growthAllowed" "(" Int "," OptionalInt ")" [function, klabel(#growthAllowed)]
  rule #growthAllowed(SIZE, .Int ) => SIZE <=Int #maxMemorySize()
  rule #growthAllowed(SIZE, I:Int) => #growthAllowed(SIZE, .Int) andBool SIZE <=Int I
  syntax Int  ::=
    "#pageSize" "(" ")" [function, klabel(#pageSize)]
  syntax Int  ::=
    "#maxMemorySize" "(" ")" [function, klabel(#maxMemorySize)]
  syntax Int  ::=
    "#maxTableSize" "(" ")" [function, klabel(#maxTableSize)]
  rule #pageSize()      => 65536
  rule #maxMemorySize() => 65536
  rule #maxTableSize()  => 4294967296
  syntax ElemDefn  ::=
    "#elem" "(" index: Int "," offset: Instrs "," elemSegment: Ints ")" [klabel(aElemDefn), symbol]
  | "elem" "{" Int Ints "}"
  syntax Stmt  ::=
    "#initElements" "(" Int "," Int "," Map "," Ints ")" [klabel(#initElements)]
  rule <instrs> #elem(TABIDX, IS, ELEMSEGMENT ) => sequenceInstrs(IS) ~> elem { TABIDX ELEMSEGMENT } ... </instrs>
  rule <instrs> elem { TABIDX ELEMSEGMENT } => #initElements ( ADDR, OFFSET, FADDRS, ELEMSEGMENT ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <valstack> < i32 > OFFSET : STACK => STACK </valstack>
         <moduleInst>
           <modIdx> CUR  </modIdx>
           <funcAddrs> FADDRS </funcAddrs>
           <tabAddrs> TABIDX |-> ADDR </tabAddrs>
           ...
         </moduleInst>
  rule <instrs> #initElements (    _,      _,      _, .Ints ) => . ... </instrs>
  rule <instrs> #initElements ( ADDR, OFFSET, FADDRS,  E:Int ES    ) => #initElements ( ADDR, OFFSET +Int 1, FADDRS, ES ) ... </instrs>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tdata> DATA => DATA [ OFFSET <- FADDRS[E] ] </tdata>
           ...
         </tabInst>
  syntax DataDefn  ::=
    "#data" "(" index: Int "," offset: Instrs "," data: Bytes ")" [klabel(aDataDefn), symbol]
  | "data" "{" Int Bytes "}"
  rule <instrs> #data(IDX, IS, DATA) => sequenceInstrs(IS) ~> data { IDX DATA } ... </instrs>
  rule <instrs> data { MEMIDX DSBYTES } => . ... </instrs>
         <valstack> < i32 > OFFSET : STACK => STACK </valstack>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memAddrs> MEMIDX |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> ADDR </mAddr>
           <mdata> DATA => #setRange(DATA, OFFSET, Bytes2Int(DSBYTES, LE, Unsigned), lengthBytes(DSBYTES)) </mdata>
           ...
         </memInst>
  syntax Int  ::=
    Int "up/Int" Int [function]
  rule I1 up/Int I2 => (I1 +Int (I2 -Int 1)) /Int I2 requires I2 >Int 0
  syntax StartDefn  ::=
    "#start" "(" Int ")" [klabel(aStartDefn), symbol]
  rule <instrs> #start(IDX) => ( invoke FADDR ) ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <funcAddrs> ... IDX |-> FADDR ... </funcAddrs>
           ...
         </moduleInst>
  syntax ExportDefn  ::=
    "#export" "(" name: WasmString "," index: Int ")" [klabel(aExportDefn), symbol]
  syntax Alloc  ::=
    ExportDefn
  rule <instrs> #export(ENAME, IDX) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <exports> EXPORTS => EXPORTS [ ENAME <- IDX ] </exports>
           ...
         </moduleInst>
  syntax ImportDefn  ::=
    "#import" "(" mod: WasmString "," name: WasmString "," ImportDesc ")" [klabel(aImportDefn), symbol]
  syntax ImportDesc  ::=
    "#funcDesc" "(" id: OptionalId "," type: Int ")" [klabel(aFuncDesc), symbol]
  | "#globalDesc" "(" id: OptionalId "," type: GlobalType ")" [klabel(aGlobalDesc), symbol]
  | "#tableDesc" "(" id: OptionalId "," type: Limits ")" [klabel(aTableDesc), symbol]
  | "#memoryDesc" "(" id: OptionalId "," type: Limits ")" [klabel(aMemoryDesc), symbol]
  syntax Alloc  ::=
    ImportDefn
  rule <instrs> #import(MOD, NAME, #funcDesc(... type: TIDX) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types> TYPES </types>
           <funcAddrs> FS => FS [NEXT <- ADDR] </funcAddrs>
           <nextFuncIdx> NEXT => NEXT +Int 1 </nextFuncIdx>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <funcAddrs> ... IDX |-> ADDR ... </funcAddrs>
           <exports>   ... NAME |-> IDX ... </exports>
           ...
         </moduleInst>
         <funcDef>
           <fAddr> ADDR </fAddr>
           <fType> FTYPE </fType>
           ...
         </funcDef>
      requires FTYPE ==K TYPES[TIDX]
  rule <instrs> #import(MOD, NAME, #tableDesc(... id: OID, type: LIM) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabIds> IDS => #saveId(IDS, OID, 0) </tabIds>
           <tabAddrs> .Map => 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <tabIds> IDS' </tabIds>
           <tabAddrs> ... #ContextLookup(IDS' , TFIDX) |-> ADDR ... </tabAddrs>
           <exports>  ... NAME |-> TFIDX                        ... </exports>
           ...
         </moduleInst>
         <tabInst>
           <tAddr> ADDR </tAddr>
           <tmax>  MAX  </tmax>
           <tsize> SIZE </tsize>
           ...
         </tabInst>
       requires #limitsMatchImport(SIZE, MAX, LIM)
  rule <instrs> #import(MOD, NAME, #memoryDesc(... id: OID, type: LIM) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memIds> IDS => #saveId(IDS, OID, 0) </memIds>
           <memAddrs> .Map => 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memIds> IDS' </memIds>
           <memAddrs> ... #ContextLookup(IDS' , TFIDX) |-> ADDR ... </memAddrs>
           <exports>  ... NAME |-> TFIDX                        ... </exports>
           ...
         </moduleInst>
         <memInst>
           <mAddr> ADDR </mAddr>
           <mmax>  MAX  </mmax>
           <msize> SIZE </msize>
           ...
         </memInst>
       requires #limitsMatchImport(SIZE, MAX, LIM)
  rule <instrs> #import(MOD, NAME, #globalDesc(... id: OID, type: MUT TYP) ) => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS => #saveId(IDS, OID, NEXT) </globIds>
           <globalAddrs> GS => GS [NEXT <- ADDR] </globalAddrs>
           <nextGlobIdx> NEXT => NEXT +Int 1 </nextGlobIdx>
           ...
         </moduleInst>
         <moduleRegistry> ... MOD |-> MODIDX ... </moduleRegistry>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <globIds> IDS' </globIds>
           <globalAddrs> ... #ContextLookup(IDS' , TFIDX) |-> ADDR ... </globalAddrs>
           <exports>     ... NAME |-> TFIDX                        ... </exports>
           ...
         </moduleInst>
         <globalInst>
           <gAddr>  ADDR    </gAddr>
           <gValue> <TYP> _ </gValue>
           <gMut>   MUT     </gMut>
         </globalInst>
  syntax Bool  ::=
    "#limitsMatchImport" "(" Int "," OptionalInt "," Limits ")" [function, klabel(#limitsMatchImport)]
  rule #limitsMatchImport(L1,      _, #limitsMin(L2:Int )) => L1 >=Int L2
  rule #limitsMatchImport( _,   .Int, #limits( _:Int,  _)) => false
  rule #limitsMatchImport(L1, U1:Int, #limits(L2:Int, U2)) => L1 >=Int L2 andBool U1 <=Int U2
  syntax ModuleDecl  ::=
    "#module" "(" types: Defns "," funcs: Defns "," tables: Defns "," mems: Defns "," globals: Defns "," elem: Defns "," data: Defns "," start: Defns "," importDefns: Defns "," exports: Defns "," metadata: ModuleMetadata ")" [klabel(aModuleDecl), symbol]
  syntax ModuleDecl  ::=
    "#emptyModule" "(" OptionalId ")" [function, klabel(#emptyModule), total]
  rule #emptyModule(OID) =>  #module (... types: .Defns, funcs: .Defns, tables: .Defns, mems: .Defns, globals: .Defns, elem: .Defns, data: .Defns, start: .Defns, importDefns: .Defns, exports: .Defns, metadata: #meta(... id: OID, funcIds: .Map, filename: .String))
  syntax ModuleMetadata  ::=
    "#meta" "(" id: OptionalId "," funcIds: Map "," filename: OptionalString ")" [klabel(moduleMeta), symbol]
  syntax OptionalString  ::=
    ".String" [klabel(.String), symbol]
  | String
  rule <instrs> #module(... types: TS, funcs: FS, tables: TABS, mems: MS, globals: GS, elem: EL, data: DAT, start: S,  importDefns: IS, exports: ES,
                         metadata: #meta(... id: OID, funcIds: FIDS, filename: FILE))
               => sequenceDefns(TS)
               ~> sequenceDefns(IS)
               ~> sequenceDefns(FS)
               ~> sequenceDefns(GS)
               ~> sequenceDefns(MS)
               ~> sequenceDefns(TABS)
               ~> sequenceDefns(ES)
               ~> sequenceDefns(EL)
               ~> sequenceDefns(DAT)
               ~> sequenceDefns(S)
               ...
         </instrs>
         <curModIdx> _ => NEXT </curModIdx>
         <nextModuleIdx> NEXT => NEXT +Int 1 </nextModuleIdx>
         <moduleIds> IDS => #saveId(IDS, OID, NEXT) </moduleIds>
         <moduleInstances>
           ( .Bag
          => <moduleInst>
               <modIdx> NEXT </modIdx>
               <moduleMetadata>
                 <moduleFileName> FILE </moduleFileName>
                 <moduleId> OID </moduleId>
                 <funcIds> FIDS </funcIds>
                 ...
               </moduleMetadata>
               ...
             </moduleInst>
           )
           ...
         </moduleInstances>
endmodule

module WASM-TEXT-SYNTAX
  imports public WASM-TEXT
  imports public WASM-SYNTAX
  imports public WASM-TOKEN-SYNTAX
endmodule

module WASM-TOKEN-SYNTAX
  syntax WasmStringToken  ::=
    r"\\\"(([^\\\"\\\\])|(\\\\[0-9a-fA-F]{2})|(\\\\t)|(\\\\n)|(\\\\r)|(\\\\\\\")|(\\\\')|(\\\\\\\\)|(\\\\u\\{[0-9a-fA-F]{1,6}\\}))*\\\"" [token]
  syntax IdentifierToken  ::=
    r"\\$[0-9a-zA-Z!$%&'*+/<>?_`|~=:\\@\\^.\\-]+" [token]
  syntax WasmIntToken  ::=
    r"[\\+\\-]?[0-9]+(_[0-9]+)*" [token]
  | r"[\\+\\-]?0x[0-9a-fA-F]+(_[0-9a-fA-F]+)*" [token]
  syntax #Layout  ::=
    r"\\(;([^;]|(;+([^;\\)])))*;\\)" [token]
  | r";;[^\\n\\r]*" [token]
  | r"[\\ \\n\\r\\t]" [token]
endmodule

module WASM-TEXT-COMMON-SYNTAX
  imports public WASM-COMMON-SYNTAX
  syntax WasmInt  ::=
    Int
  syntax WasmInt  ::=
    WasmIntToken [avoid, function, klabel(WasmInt), symbol]
  syntax Index  ::=
    Identifier
  syntax PlainInstr  ::=
    "br" Index
  | "br_if" Index
  | "br_table" ElemSegment
  | "call" Index
  | "global.get" Index
  | "global.set" Index
  | "local.get" Index
  | "local.set" Index
  | "local.tee" Index
  syntax PlainInstr  ::=
    IValType "." StoreOpM
  | FValType "." StoreOpM
  | IValType "." LoadOpM
  | FValType "." LoadOpM
  syntax StoreOpM  ::=
    StoreOp
  | StoreOp MemArg
  syntax LoadOpM  ::=
    LoadOp
  | LoadOp MemArg
  syntax MemArg  ::=
    OffsetArg
  | AlignArg
  | OffsetArg AlignArg
  syntax OffsetArg  ::=
    "offset=" WasmInt
  syntax AlignArg  ::=
    "align=" WasmInt
  syntax Instr  ::=
    BlockInstr
  syntax BlockInstr  ::=
    "block" OptionalId TypeDecls Instrs "end" OptionalId
  | "loop" OptionalId TypeDecls Instrs "end" OptionalId
  | "if" OptionalId TypeDecls Instrs "else" OptionalId Instrs "end" OptionalId
  | "if" OptionalId TypeDecls Instrs "end" OptionalId
  syntax Instr  ::=
    FoldedInstr
  syntax FoldedInstr  ::=
    "(" PlainInstr Instrs ")"
  | "(" PlainInstr ")" [prefer]
  syntax FoldedInstr  ::=
    "(" "block" OptionalId TypeDecls Instrs ")"
  | "(" "loop" OptionalId TypeDecls Instrs ")"
  | "(" "if" OptionalId TypeDecls Instrs "(" "then" Instrs ")" ")"
  | "(" "if" OptionalId TypeDecls Instrs "(" "then" Instrs ")" "(" "else" Instrs ")" ")"
  syntax TypeDefn  ::=
    "(type" OptionalId "(" "func" TypeDecls ")" ")"
  syntax TextLimits  ::=
    Int
  | Int Int
  syntax ExportDefn  ::=
    "(" "export" WasmString "(" Externval ")" ")"
  syntax InlineExport  ::=
    "(" "export" WasmString ")"
  syntax ImportDefn  ::=
    "(" "import" WasmString WasmString ImportDesc ")"
  syntax InlineImport  ::=
    "(" "import" WasmString WasmString ")"
  syntax ImportDesc  ::=
    "(" "func" OptionalId TypeUse ")" [klabel(funcImportDesc)]
  | "(" "global" OptionalId TextFormatGlobalType ")" [klabel(globImportDesc)]
  | "(" "table" OptionalId TableType ")" [klabel( tabImportDesc)]
  | "(" "memory" OptionalId MemType ")" [klabel( memImportDesc)]
  syntax FuncDefn  ::=
    "(" "func" OptionalId FuncSpec ")"
  syntax FuncSpec  ::=
    TypeUse LocalDecls Instrs
  | InlineImport TypeUse
  | InlineExport FuncSpec
  syntax LocalDecl  ::=
    "(" LocalDecl ")" [bracket]
  | "local" ValTypes
  | "local" Identifier ValType
  syntax LocalDecls  ::=
    List{LocalDecl,""} [symbol(listLocalDecl)]
  syntax TableDefn  ::=
    "(" "table" OptionalId TableSpec ")"
  syntax TableSpec  ::=
    TableType
  | TableElemType "(" "elem" ElemSegment ")"
  | InlineImport TableType
  | InlineExport TableSpec
  syntax TableType  ::=
    TextLimits TableElemType
  syntax TableElemType  ::=
    "funcref"
  syntax MemoryDefn  ::=
    "(" "memory" OptionalId MemorySpec ")"
  syntax MemorySpec  ::=
    MemType
  syntax MemorySpec  ::=
    "(" "data" DataString ")"
  | InlineImport MemType
  | InlineExport MemorySpec
  syntax MemType  ::=
    TextLimits
  syntax GlobalDefn  ::=
    "(" "global" OptionalId GlobalSpec ")"
  syntax GlobalSpec  ::=
    TextFormatGlobalType Instr
  | InlineImport TextFormatGlobalType
  | InlineExport GlobalSpec
  syntax TextFormatGlobalType  ::=
    ValType
  | "(" "mut" ValType ")"
  syntax Offset  ::=
    "(" "offset" Instrs ")"
  syntax Offset  ::=
    Instrs
  syntax ElemDefn  ::=
    "(" "elem" Index Offset ElemSegment ")"
  | "(" "elem" Offset ElemSegment ")"
  | "(" "elem" Offset "func" ElemSegment ")"
  syntax DataDefn  ::=
    "(" "data" Index Offset DataString ")"
  | "(" "data" Offset DataString ")"
  syntax StartDefn  ::=
    "(" "start" Index ")"
  syntax Stmt  ::=
    ModuleDecl
  syntax ModuleDecl  ::=
    "(" "module" OptionalId Defns ")"
endmodule

module WASM-TEXT
  imports public WASM-TEXT-COMMON-SYNTAX
  imports public WASM
  rule `WasmInt`(VAL) => WasmIntToken2Int(VAL)
  syntax String  ::=
    "WasmIntToken2String" "(" WasmIntToken ")" [function, hook(STRING.token2string), klabel(WasmIntToken2String), total]
  syntax Int  ::=
    "WasmIntTokenString2Int" "(" String ")" [function, klabel(WasmIntTokenString2Int)]
  | "WasmIntToken2Int" "(" WasmIntToken ")" [function, klabel(WasmIntToken2Int)]
  rule WasmIntTokenString2Int(S)  => String2Base(replaceFirst(S, "0x", ""), 16) requires findString(S, "0x", 0) =/=Int -1
  rule WasmIntTokenString2Int(S)  => String2Base(                        S, 10) requires findString(S, "0x", 0)  ==Int -1
  rule WasmIntToken2Int(VAL) => WasmIntTokenString2Int(replaceAll(WasmIntToken2String(VAL), "_", ""))
  syntax IdentifierToken  ::=
    "String2Identifier" "(" String ")" [function, hook(STRING.string2token), klabel(String2Identifier), total]
  rule #ContextLookup(IDS:Map, ID:Identifier) => {IDS [ ID ]}:>Int
      requires ID in_keys(IDS)
  syntax Stmts  ::=
    "unfoldStmts" "(" Stmts ")" [function, klabel(unfoldStmts)]
  syntax Defns  ::=
    "unfoldDefns" "(" Defns ")" [function, klabel(unfoldDefns)]
  | "#unfoldDefns" "(" Defns "," Int "," TypesInfo ")" [function, klabel(#unfoldDefns)]
  rule unfoldStmts(( module OID:OptionalId DS) SS) => ( module OID unfoldDefns(DS) ) unfoldStmts(SS)
  rule unfoldStmts(.Stmts) => .Stmts
  rule unfoldStmts(S SS) => S unfoldStmts(SS)  [owise]
  rule unfoldDefns(DS) => #unfoldDefns(DS, 0, types2indices(DS))
  rule #unfoldDefns(.Defns, _, _) => .Defns
  rule #unfoldDefns(D:Defn DS, I, TI) => D #unfoldDefns(DS, I, TI)  [owise]
  syntax Defns  ::=
    Defns "appendDefn" Defn [function]
  rule (D DS) appendDefn D' => D (DS appendDefn D')
  rule .Defns appendDefn D' => D' .Defns
  rule #unfoldDefns(( func _OID:OptionalId (TDECLS:TypeDecls => (type {M [asFuncType(TDECLS)]}:>Int) TDECLS) _LOCALS:LocalDecls _BODY:Instrs ) _DS
                    , _I
                    , #ti(... t2i: M))
      requires         asFuncType(TDECLS) in_keys(M)
  rule #unfoldDefns(( func _OID:OptionalId (TDECLS:TypeDecls => (type N) TDECLS) _LOCALS:LocalDecls _BODY:Instrs ) (DS => DS appendDefn  (type (func TDECLS)))
                   , _I
                   , #ti(... t2i: M => M [ asFuncType(TDECLS) <- N ], count: N => N +Int 1))
      requires notBool asFuncType(TDECLS) in_keys(M)
  rule #unfoldDefns(( func OID:OptionalId TUSE:TypeUse LOCALS:LocalDecls    BODY)   DS, I, TI)
      => (( func OID            TUSE         LOCALS unfoldInstrs(BODY)))
         #unfoldDefns(DS, I, TI)
      requires notBool isTypeDecls(TUSE)
  rule #unfoldDefns(( import MOD NAME (func OID:OptionalId TDECLS:TypeDecls )) DS, I, #ti(... t2i: M) #as TI)
      => (import MOD NAME (func OID (type {M [asFuncType(TDECLS)]}:>Int) TDECLS ))
         #unfoldDefns(DS, I, TI)
      requires         asFuncType(TDECLS) in_keys(M)
  rule #unfoldDefns(( import MOD NAME (func OID:OptionalId TDECLS:TypeDecls)) DS, I, #ti(... t2i: M, count: N))
      => (import MOD NAME (func OID (type N) TDECLS))
         #unfoldDefns(DS appendDefn (type (func TDECLS)), I, #ti(... t2i: M [asFuncType(TDECLS) <- N], count: N +Int 1))
      requires notBool asFuncType(TDECLS) in_keys(M)
  syntax TypesInfo  ::=
    "#ti" "(" t2i: Map "," count: Int ")" [klabel(#ti)]
  syntax TypesInfo  ::=
    "types2indices" "(" Defns ")" [function, klabel(types2indices)]
  | "#types2indices" "(" Defns "," TypesInfo ")" [function, klabel(#types2indices)]
  rule types2indices(DS) => #types2indices(DS, #ti(... t2i: .Map, count: 0))
  rule #types2indices(.Defns, TI) => TI
  rule #types2indices((type _OID (func TDECLS)) DS, #ti(... t2i: M, count: N))
      => #types2indices(DS, #ti(... t2i: M [ asFuncType(TDECLS) <- (M [ asFuncType(TDECLS) ] orDefault N) ], count: N +Int 1))
  rule #types2indices(_D DS, M) => #types2indices(DS, M)  [owise]
  rule #unfoldDefns(( func OID:OptionalId (import MOD NAME) TUSE) DS, I, M)
      => #unfoldDefns(( import MOD NAME (func OID TUSE) ) DS, I, M)
  rule #unfoldDefns(( func EXPO:InlineExport SPEC:FuncSpec ) DS, I, M)
      => #unfoldDefns(( func #freshId(I) EXPO  SPEC) DS, I +Int 1, M)
  rule #unfoldDefns(( func ID:Identifier ( export ENAME ) SPEC:FuncSpec ) DS, I, M)
      => ( export ENAME ( func ID ) ) #unfoldDefns(( func ID SPEC ) DS, I, M)
  rule #unfoldDefns(( table funcref ( elem ELEM ) ) DS, I, M)
      => #unfoldDefns(( table #freshId(I) funcref ( elem ELEM ) ) DS, I +Int 1, M)
  rule #unfoldDefns(( table ID:Identifier funcref ( elem ELEM ) ) DS, I, M)
      => ( table ID #lenElemSegment(ELEM) #lenElemSegment(ELEM) funcref ):TableDefn
         ( elem  ID (offset (i32.const 0) .Instrs) ELEM )
         #unfoldDefns(DS, I, M)
  rule #unfoldDefns(( table OID:OptionalId (import MOD NAME) TT:TableType ) DS, I, M)
      => #unfoldDefns(( import MOD NAME (table OID TT) ) DS, I, M)
  rule #unfoldDefns(( table EXPO:InlineExport SPEC:TableSpec ) DS, I, M)
      => #unfoldDefns(( table #freshId(I) EXPO SPEC ) DS, I +Int 1, M)
  rule #unfoldDefns(( table ID:Identifier ( export ENAME ) SPEC:TableSpec ) DS, I, M)
      => ( export ENAME ( table ID ) ) #unfoldDefns(( table ID SPEC ) DS, I, M)
  rule #unfoldDefns(( memory ( data DATA ) ) DS, I, M)
      => #unfoldDefns(( memory #freshId(I) ( data DATA ) ) DS, I +Int 1, M)
  rule #unfoldDefns(( memory ID:Identifier ( data DATA ) ) DS, I, M)
      => ( memory ID #lengthDataPages(DATA) #lengthDataPages(DATA) ):MemoryDefn
         ( data   ID (offset (i32.const 0) .Instrs) DATA )
         #unfoldDefns(DS, I, M)
  rule #unfoldDefns(( memory OID:OptionalId (import MOD NAME) MT:MemType ) DS, I, M)
      => #unfoldDefns(( import MOD NAME (memory OID MT  ) ) DS, I, M)
  rule #unfoldDefns(( memory EXPO:InlineExport SPEC:MemorySpec ) DS, I, M)
      => #unfoldDefns(( memory #freshId(I:Int) EXPO SPEC ) DS, I +Int 1, M)
  rule #unfoldDefns(( memory ID:Identifier ( export ENAME ) SPEC:MemorySpec ) DS, I, M)
      => ( export ENAME ( memory ID ) ) #unfoldDefns( ( memory ID SPEC ) DS, I, M)
  syntax Int  ::=
    "#lengthDataPages" "(" DataString ")" [function, klabel(#lengthDataPages)]
  rule #lengthDataPages(DS:DataString) => lengthBytes(#DS2Bytes(DS)) up/Int #pageSize()
  syntax GlobalType  ::=
    "asGMut" "(" TextFormatGlobalType ")" [function, klabel(asGMut)]
  rule asGMut ( (mut T:ValType ) ) => var   T
  rule asGMut (      T:ValType   ) => const T
  rule #unfoldDefns((( global OID TYP:TextFormatGlobalType IS:Instr) => #global(... type: asGMut(TYP), init: unfoldInstrs(IS .Instrs), metadata: OID)) _DS, _I, _M)
  rule #unfoldDefns(( global OID:OptionalId (import MOD NAME) TYP ) DS, I, M)
      => #unfoldDefns(( import MOD NAME (global OID TYP ) ) DS, I, M)
  rule #unfoldDefns(( global EXPO:InlineExport SPEC:GlobalSpec ) DS, I, M)
      => #unfoldDefns(( global #freshId(I) EXPO SPEC ) DS, I +Int 1, M)
  rule #unfoldDefns(( global ID:Identifier ( export ENAME ) SPEC:GlobalSpec ) DS, I, M)
      => ( export ENAME ( global ID ) ) #unfoldDefns(( global ID SPEC ) DS, I, M)
  rule #unfoldDefns(((elem OFFSET func ES) => (elem OFFSET ES)) _DS, _I, _M)
  rule #unfoldDefns(((elem OFFSET:Offset ES ) => ( elem 0 OFFSET ES )) _DS, _I, _M)
  rule #unfoldDefns(((elem IDX OFFSET:Instrs ES ) => ( elem IDX ( offset OFFSET ) ES )) _DS, _I, _M)
  rule #unfoldDefns((elem IDX (offset IS) ES) DS, I, M) => (elem IDX (offset unfoldInstrs(IS)) ES) #unfoldDefns(DS, I, M)
  rule #unfoldDefns(((data OFFSET:Offset DATA ) => ( data 0 OFFSET DATA )) _DS, _I, _M)
  rule #unfoldDefns(((data IDX OFFSET:Instrs DATA ) => ( data IDX ( offset OFFSET ) DATA )) _DS, _I, _M)
  rule #unfoldDefns((data IDX (offset IS) DATA) DS, I, M) => (data IDX (offset unfoldInstrs(IS)) DATA) #unfoldDefns(DS, I, M)
  syntax Instrs  ::=
    "unfoldInstrs" "(" Instrs ")" [function, klabel(unfoldInstrs)]
  | "#unfoldInstrs" "(" Instrs "," Int "," Map ")" [function, klabel(#unfoldInstrs)]
  rule unfoldInstrs(IS) => #unfoldInstrs(IS, 0, .Map)
  rule #unfoldInstrs(.Instrs, _, _) => .Instrs
  rule #unfoldInstrs(I IS, DEPTH, M) => I #unfoldInstrs(IS, DEPTH, M)  [owise]
  syntax Instrs  ::=
    Instrs "appendInstrs" Instrs [function]
  | "#appendInstrs" "(" Instrs "," Instrs ")" [function, klabel(#appendInstrs)]
  | "#reverseInstrs" "(" Instrs "," Instrs ")" [function, klabel(#reverseInstrs)]
  rule IS appendInstrs IS' => #appendInstrs(#reverseInstrs(IS, .Instrs), IS')
  rule #appendInstrs(I IS => IS, IS' => I IS')
  rule #appendInstrs(.Instrs   , IS') => IS'
  rule #reverseInstrs(.Instrs, ACC) => ACC
  rule #reverseInstrs(I IS => IS, ACC => I ACC)
  rule #unfoldInstrs(br       ID:Identifier  IS, DEPTH, M) => br      DEPTH -Int {M [ ID ]}:>Int -Int 1 #unfoldInstrs(IS, DEPTH, M)
  rule #unfoldInstrs(br_if    ID:Identifier  IS, DEPTH, M) => br_if   DEPTH -Int {M [ ID ]}:>Int -Int 1 #unfoldInstrs(IS, DEPTH, M)
  rule #unfoldInstrs(br_table ES:ElemSegment IS, DEPTH, M) => br_table elemSegment2Indices(ES, DEPTH, M) #unfoldInstrs(IS, DEPTH, M)
  syntax ElemSegment  ::=
    "elemSegment2Indices" "(" ElemSegment "," Int "," Map ")" [function, klabel(elemSegment2Indices)]
  rule elemSegment2Indices(.ElemSegment    , _DEPTH, _M) => .ElemSegment
  rule elemSegment2Indices(ID:Identifier ES,  DEPTH,  M) => DEPTH -Int {M [ ID ]}:>Int -Int 1 elemSegment2Indices(ES, DEPTH, M)
  rule elemSegment2Indices(E             ES,  DEPTH,  M) => E                                 elemSegment2Indices(ES, DEPTH, M)  [owise]
  rule #unfoldInstrs( (block ID:Identifier TDS IS end _OID' => block    TDS IS end) _IS',  DEPTH,  M => M [ ID <- DEPTH ])
  rule #unfoldInstrs(block TDS:TypeDecls IS end IS', DEPTH, M) => block TDS #unfoldInstrs(IS, DEPTH +Int 1, M) end #unfoldInstrs(IS', DEPTH, M)
  rule #unfoldInstrs( (loop ID:Identifier TDS IS end _OID' => loop    TDS IS end) _IS',  DEPTH,  M => M [ ID <- DEPTH ])
  rule #unfoldInstrs(loop TDS:TypeDecls IS end IS', DEPTH, M) => loop TDS #unfoldInstrs(IS, DEPTH +Int 1, M) end #unfoldInstrs(IS', DEPTH, M)
  rule #unfoldInstrs( (if ID:Identifier  TDS      IS                                   end _OID'' => if  ID TDS IS else .Instrs end) _IS'', _DEPTH, _M)
  rule #unfoldInstrs( (if                TDS      IS                                   end _OID'' => if     TDS IS else .Instrs end) _IS'', _DEPTH, _M)
  rule #unfoldInstrs( (if ID:Identifier  TDS      IS         else _OID':OptionalId IS' end _OID'' => if     TDS IS else IS'     end) _IS'',  DEPTH,  M => M [ ID <- DEPTH ])
  rule #unfoldInstrs(if TDS IS else IS' end IS'', DEPTH, M) => if TDS #unfoldInstrs(IS, DEPTH +Int 1, M) else #unfoldInstrs(IS', DEPTH +Int 1, M) end #unfoldInstrs(IS'', DEPTH, M)
  rule #unfoldInstrs(( PI:PlainInstr  IS:Instrs ):FoldedInstr IS', DEPTH, M)
      =>             (#unfoldInstrs(IS        , DEPTH, M)
         appendInstrs #unfoldInstrs(PI .Instrs, DEPTH, M))
         appendInstrs #unfoldInstrs(IS'       , DEPTH, M)
  rule #unfoldInstrs(( PI:PlainInstr            ):FoldedInstr IS', DEPTH, M)
      =>              #unfoldInstrs(PI .Instrs, DEPTH, M)
         appendInstrs #unfoldInstrs(IS'       , DEPTH, M)
  rule #unfoldInstrs(((block ID:Identifier TDS IS)          => block ID TDS IS end) _IS', _DEPTH, _M)
  rule #unfoldInstrs(((block               TDS IS)          => block    TDS IS end) _IS', _DEPTH, _M)
  rule #unfoldInstrs(((loop ID:Identifier TDS IS)          => loop ID TDS IS end) _IS', _DEPTH, _M)
  rule #unfoldInstrs(((loop               TDS IS)          => loop    TDS IS end) _IS', _DEPTH, _M)
  rule #unfoldInstrs(((if OID:OptionalId TDS COND (then IS)) => (if OID TDS COND (then IS) (else .Instrs))) _IS'', _DEPTH, _M)
  rule #unfoldInstrs(((if ID:Identifier  TDS COND (then IS) (else IS')) IS'':Instrs) => (COND appendInstrs if ID TDS IS else IS' end IS''), _DEPTH, _M)
  rule #unfoldInstrs(((if                TDS COND (then IS) (else IS')) IS'':Instrs) => (COND appendInstrs if    TDS IS else IS' end IS''), _DEPTH, _M)
  syntax Stmts  ::=
    "structureModules" "(" Stmts ")" [function, klabel(structureModules)]
  rule structureModules((module OID:OptionalId DS) SS) => structureModule(DS, OID) structureModules(SS)
  rule structureModules(.Stmts) => .Stmts
  rule structureModules(S SS) => S structureModules(SS)  [owise]
  syntax ModuleDecl  ::=
    "structureModule" "(" Defns "," OptionalId ")" [function, klabel(structureModule)]
  | "#structureModule" "(" Defns "," ModuleDecl ")" [function, klabel(#structureModule)]
  rule structureModule(DEFNS, OID) => #structureModule(#reverseDefns(DEFNS, .Defns), #emptyModule(OID))
  rule #structureModule(.Defns, SORTED_MODULE) => SORTED_MODULE
  rule #structureModule((T:TypeDefn   DS:Defns => DS), #module(... types:       TS => T TS))
  rule #structureModule((I:ImportDefn DS:Defns => DS), #module(... importDefns: IS => I IS))
  rule #structureModule((X:FuncDefn   DS:Defns => DS), #module(... funcs:       FS => X FS))
  rule #structureModule((X:GlobalDefn DS:Defns => DS), #module(... globals:     GS => X GS))
  rule #structureModule((T:TableDefn  DS:Defns => DS), #module(... tables:      TS => T TS))
  rule #structureModule((M:MemoryDefn DS:Defns => DS), #module(... mems:        MS => M MS))
  rule #structureModule((E:ExportDefn DS:Defns => DS), #module(... exports:     ES => E ES))
  rule #structureModule((I:DataDefn   DS:Defns => DS), #module(... data:        IS => I IS))
  rule #structureModule((I:ElemDefn   DS:Defns => DS), #module(... elem:        IS => I IS))
  rule #structureModule((S:StartDefn  DS:Defns => DS), #module(... start:   .Defns => S .Defns))
  syntax Defns  ::=
    "#reverseDefns" "(" Defns "," Defns ")" [function, klabel(#reverseDefns)]
  rule #reverseDefns(       .Defns  , ACC) => ACC
  rule #reverseDefns(D:Defn DS:Defns, ACC) => #reverseDefns(DS, D ACC)
  syntax Context  ::=
    "ctx" "(" localIds: Map "," globalIds: Map "," funcIds: Map "," typeIds: Map ")" [klabel(ctx)]
  | "#freshCtx" "(" ")" [function, klabel(#freshCtx), total]
  | "#updateLocalIds" "(" Context "," Map ")" [function, klabel(#updateLocalIds), total]
  | "#updateLocalIdsAux" "(" Context "," Map "," Bool ")" [function, klabel(#updateLocalIdsAux), total]
  | "#updateFuncIds" "(" Context "," Map ")" [function, klabel(#updateFuncIds), total]
  | "#updateFuncIdsAux" "(" Context "," Map "," Bool ")" [function, klabel(#updateFuncIdsAux), total]
  rule #freshCtx ( ) => ctx(... localIds: .Map, globalIds: .Map, funcIds: .Map, typeIds: .Map)
  rule #updateLocalIds(C, M) => #updateLocalIdsAux(C, M, false)
  rule #updateLocalIdsAux(ctx(... localIds: (_ => M)), M, false => true)
  rule #updateLocalIdsAux(C, _, true) => C
  rule #updateFuncIds(C, M) => #updateFuncIdsAux(C, M, false)
  rule #updateFuncIdsAux(ctx(... funcIds: (_ => M)), M, false => true)
  rule #updateFuncIdsAux(C, _, true) => C
  syntax Stmt  ::=
    "#t2aStmt" "<" Context ">" "(" Stmt ")" [function]
  syntax ModuleDecl  ::=
    "#t2aModuleDecl" "<" Context ">" "(" ModuleDecl ")" [function]
  syntax ModuleDecl  ::=
    "#t2aModule" "<" Context ">" "(" ModuleDecl ")" [function]
  syntax Defn  ::=
    "#t2aDefn" "<" Context ">" "(" Defn ")" [function]
  rule text2abstract(DS:Defns) => text2abstract(( module DS ) .Stmts)
  rule text2abstract(SS)       => #t2aStmts<#freshCtx()>(structureModules(unfoldStmts(SS)))  [owise]
  rule #t2aStmt<C>(M:ModuleDecl) => #t2aModuleDecl<C>(M)
  rule #t2aStmt<C>(D:Defn)  => #t2aDefn<C>(D)
  rule #t2aStmt<C>(I:Instr) => #t2aInstr<C>(I)
  rule #t2aStmt<_>(S) => S  [owise]
  rule #t2aModuleDecl<_>(#module(... types: TS, funcs: FS, globals: GS, importDefns: IS) #as M) => #t2aModule<ctx(... localIds: .Map, globalIds: #idcGlobals(IS, GS), funcIds: #idcFuncs(IS, FS), typeIds: #idcTypes(TS))>(M)
  rule #t2aModule<ctx(... funcIds: FIDS) #as C>(#module(... types: TS, funcs: FS, tables: TABS, mems: MS, globals: GS, elem: EL, data: DAT, start: S, importDefns: IS, exports: ES, metadata: #meta(... id: OID)))
      => #module( ... types: #t2aDefns<C>(TS)
                    , funcs: #t2aDefns<C>(FS)
                    , tables: #t2aDefns<C>(TABS)
                    , mems: #t2aDefns<C>(MS)
                    , globals: #t2aDefns<C>(GS)
                    , elem: #t2aDefns<C>(EL)
                    , data: #t2aDefns<C>(DAT)
                    , start: #t2aDefns<C>(S)
                    , importDefns: #t2aDefns<C>(IS)
                    , exports: #t2aDefns<C>(ES)
                    , metadata: #meta(... id: OID, funcIds: FIDS, filename: .String)
                )
  rule #t2aDefn<_>((type OID (func TDECLS))) => #type(... type: asFuncType(TDECLS), metadata: OID)
  rule #t2aDefn<ctx(... typeIds: TIDS)>(( import MOD NAME (func   OID:OptionalId (type ID:Identifier)            ))) => #import(MOD, NAME, #funcDesc(... id: OID:OptionalId, type: {TIDS[ID]}:>Int))
  rule #t2aDefn<ctx(... typeIds: TIDS)>(( import MOD NAME (func   OID:OptionalId (type ID:Identifier) _:TypeDecls))) => #import(MOD, NAME, #funcDesc(... id: OID:OptionalId, type: {TIDS[ID]}:>Int))
  rule #t2aDefn<_                     >(( import MOD NAME (func   OID:OptionalId (type IDX:Int)                  ))) => #import(MOD, NAME, #funcDesc(... id: OID:OptionalId, type: IDX))
  rule #t2aDefn<_                     >(( import MOD NAME (func   OID:OptionalId (type IDX:Int      ) _:TypeDecls))) => #import(MOD, NAME, #funcDesc(... id: OID:OptionalId, type: IDX))
  rule #t2aDefn<_                     >(( import MOD NAME (global OID:OptionalId TYP:TextFormatGlobalType)))         => #import(MOD, NAME, #globalDesc(... id: OID:OptionalId, type: asGMut(TYP)))
  rule #t2aDefn<_                     >(( import MOD NAME (table  OID:OptionalId LIM:TextLimits funcref)))           => #import(MOD, NAME, #tableDesc(...  id: OID:OptionalId, type: t2aLimits(LIM)))
  rule #t2aDefn<_                     >(( import MOD NAME (memory OID:OptionalId LIM:TextLimits        )))           => #import(MOD, NAME, #memoryDesc(... id: OID:OptionalId, type: t2aLimits(LIM)))
  rule #t2aDefn<C>(#global(... type: GTYP, init: IS, metadata: OID)) => #global(... type: GTYP, init: #t2aInstrs<C>(IS), metadata: OID)
  rule #t2aDefn<ctx(... typeIds: TIDS) #as C>(( func OID:OptionalId T:TypeUse LS:LocalDecls IS:Instrs ))
      => #func(... type: typeUse2typeIdx(T, TIDS)
                 , locals: locals2vectype(LS)
                 , body: #t2aInstrs <#updateLocalIds(C, #ids2Idxs(T, LS))>(IS)
                 , metadata: #meta(... id: OID, localIds: #ids2Idxs(T, LS))
              )
  syntax Int  ::=
    "typeUse2typeIdx" "(" TypeUse "," Map ")" [function, klabel(typeUse2typeIdx)]
  rule typeUse2typeIdx( (type IDX ) _:TypeDecls => (type IDX), _TIDS )
  rule typeUse2typeIdx( (type ID:Identifier )  ,  TIDS ) => {TIDS [ ID ]}:>Int
  rule typeUse2typeIdx( (type IDX:Int       )  , _TIDS ) => IDX
  syntax VecType  ::=
    "locals2vectype" "(" LocalDecls ")" [function, klabel(locals2vectype)]
  | "#locals2vectype" "(" LocalDecls "," ValTypes ")" [function, klabel(#locals2vectype)]
  rule locals2vectype(LDECLS) => #locals2vectype(LDECLS, .ValTypes)
  rule #locals2vectype(.LocalDecls                                             , VTYPES) => [ VTYPES ]
  rule #locals2vectype(local                VTYPES':ValTypes LDECLS:LocalDecls , VTYPES) => #locals2vectype(LDECLS , VTYPES + VTYPES')
  rule #locals2vectype(local _ID:Identifier VTYPE:ValType    LDECLS:LocalDecls , VTYPES) => #locals2vectype(LDECLS , VTYPES + VTYPE .ValTypes)
  rule #t2aDefn<_>((table OID:OptionalId LIMITS:TextLimits funcref )) => #table(... limits: t2aLimits(LIMITS), metadata: OID)
  rule #t2aDefn<_>((memory OID:OptionalId LIMITS:TextLimits )) => #memory(... limits: t2aLimits(LIMITS), metadata: OID)
  syntax Limits  ::=
    "t2aLimits" "(" TextLimits ")" [function, klabel(t2aLimits), total]
  rule t2aLimits(MIN:Int) => #limitsMin(MIN)
  rule t2aLimits(MIN:Int MAX:Int) => #limits(MIN, MAX)
  rule #t2aDefn<ctx(... funcIds: FIDS)>(( start ID:Identifier )) => #start({FIDS[ID]}:>Int)
      requires ID in_keys(FIDS)
  rule #t2aDefn<_>(( start I:Int )) => #start(I)
  rule #t2aDefn<C>(( elem _:Index (offset IS) ES )) => #elem(0, #t2aInstrs<C>(IS), #t2aElemSegment<C>(ES) )
  syntax Ints  ::=
    "#t2aElemSegment" "<" Context ">" "(" ElemSegment ")" [function]
  rule #t2aElemSegment<ctx(... funcIds: FIDS) #as C>(ID:Identifier ES) => {FIDS[ID]}:>Int #t2aElemSegment<C>(ES)
      requires ID in_keys(FIDS)
  rule #t2aElemSegment<C>(I:Int ES) => I #t2aElemSegment<C>(ES)
  rule #t2aElemSegment<_C>(.ElemSegment) => .Ints
  rule #t2aDefn<C>(( data _:Index (offset IS) DS )) => #data(0, #t2aInstrs<C>(IS), #DS2Bytes(DS))
  rule #t2aDefn<ctx(...   funcIds: IDS)>(( export ENAME ( func   ID:Identifier ) )) => #export(ENAME, {IDS[ID]}:>Int) requires ID in_keys(IDS)
  rule #t2aDefn<ctx(... globalIds: IDS)>(( export ENAME ( global ID:Identifier ) )) => #export(ENAME, {IDS[ID]}:>Int) requires ID in_keys(IDS)
  rule #t2aDefn<_>(( export ENAME ( func   I:Int ) )) => #export(ENAME, I)
  rule #t2aDefn<_>(( export ENAME ( global I:Int ) )) => #export(ENAME, I)
  rule #t2aDefn<_>(( export ENAME ( table   _ ) )) => #export(ENAME, 0)
  rule #t2aDefn<_>(( export ENAME ( memory  _ ) )) => #export(ENAME, 0)
  rule #t2aDefn<_C>(D:Defn) => D  [owise]
  syntax Instr  ::=
    "#t2aInstr" "<" Context ">" "(" Instr ")" [function]
  rule #t2aInstr<C>(( PI:PlainInstr  IS:Instrs ):FoldedInstr) => ({#t2aInstr<C>(PI)}:>PlainInstr #t2aInstrs<C>(IS))
  rule #t2aInstr<C>(( PI:PlainInstr            ):FoldedInstr) =>  #t2aInstr<C>(PI)
  rule #t2aInstr<_>(unreachable) => unreachable
  rule #t2aInstr<_>(nop)         => nop
  rule #t2aInstr<_>(br L:Int)    => #br(L)
  rule #t2aInstr<_>(br_if L:Int) => #br_if(L)
  rule #t2aInstr<_>(br_table ES) => #br_table(elemSegment2Ints(ES))
  rule #t2aInstr<_>(return)      => return
  rule #t2aInstr<ctx(... funcIds: FIDS)>(call ID:Identifier) => #call({FIDS[ID]}:>Int)
      requires ID in_keys(FIDS)
  rule #t2aInstr<_>                     (call I:Int)         => #call(I)
  rule #t2aInstr<_>(call_indirect TU) => call_indirect TU
  rule #t2aInstr<_>(drop)   => drop
  rule #t2aInstr<_>(select) => select
  rule #t2aInstr<ctx(... localIds: LIDS)>(local.get ID:Identifier) => #local.get({LIDS[ID]}:>Int)
      requires ID in_keys(LIDS)
  rule #t2aInstr<ctx(... localIds: LIDS)>(local.set ID:Identifier) => #local.set({LIDS[ID]}:>Int)
      requires ID in_keys(LIDS)
  rule #t2aInstr<ctx(... localIds: LIDS)>(local.tee ID:Identifier) => #local.tee({LIDS[ID]}:>Int)
      requires ID in_keys(LIDS)
  rule #t2aInstr<_>(local.get I:Int) => #local.get(I)
  rule #t2aInstr<_>(local.set I:Int) => #local.set(I)
  rule #t2aInstr<_>(local.tee I:Int) => #local.tee(I)
  rule #t2aInstr<ctx(... globalIds: GIDS)>(global.get ID:Identifier) => #global.get({GIDS[ID]}:>Int)
      requires ID in_keys(GIDS)
  rule #t2aInstr<ctx(... globalIds: GIDS)>(global.set ID:Identifier) => #global.set({GIDS[ID]}:>Int)
      requires ID in_keys(GIDS)
  rule #t2aInstr<_>(global.get I:Int) => #global.get(I)
  rule #t2aInstr<_>(global.set I:Int) => #global.set(I)
  rule #t2aInstr<_>(ITYPE:IValType.OP:StoreOp)        => #store(ITYPE, OP, 0)
  rule #t2aInstr<_>(ITYPE:IValType.OP:StoreOp MemArg) => #store(ITYPE, OP, #getOffset(MemArg))
  rule #t2aInstr<_>(FTYPE:FValType.OP:StoreOp)        => #store(FTYPE, OP, 0)
  rule #t2aInstr<_>(FTYPE:FValType.OP:StoreOp MemArg) => #store(FTYPE, OP, #getOffset(MemArg))
  rule #t2aInstr<_>(ITYPE:IValType.OP:LoadOp)         => #load(ITYPE, OP, 0)
  rule #t2aInstr<_>(ITYPE:IValType.OP:LoadOp MemArg)  => #load(ITYPE, OP, #getOffset(MemArg))
  rule #t2aInstr<_>(FTYPE:FValType.OP:LoadOp)         => #load(FTYPE, OP, 0)
  rule #t2aInstr<_>(FTYPE:FValType.OP:LoadOp MemArg)  => #load(FTYPE, OP, #getOffset(MemArg))
  rule #t2aInstr<_>(memory.size)                => memory.size
  rule #t2aInstr<_>(memory.grow)                => memory.grow
  syntax Int  ::=
    "#getOffset" "(" MemArg ")" [function, klabel(#getOffset), total]
  rule #getOffset(           _:AlignArg) => 0
  rule #getOffset(offset= OS           ) => OS
  rule #getOffset(offset= OS _:AlignArg) => OS
  rule #t2aInstr<_>(ITYPE:IValType.const I) => ITYPE.const I
  rule #t2aInstr<_>(FTYPE:FValType.const N) => FTYPE.const N
  rule #t2aInstr<_>(ITYPE.OP:IUnOp)         => ITYPE.OP
  rule #t2aInstr<_>(FTYPE.OP:FUnOp)         => FTYPE.OP
  rule #t2aInstr<_>(ITYPE.OP:IBinOp)        => ITYPE.OP
  rule #t2aInstr<_>(FTYPE.OP:FBinOp)        => FTYPE.OP
  rule #t2aInstr<_>(ITYPE.OP:TestOp)        => ITYPE.OP
  rule #t2aInstr<_>(ITYPE.OP:IRelOp)        => ITYPE.OP
  rule #t2aInstr<_>(FTYPE.OP:FRelOp)        => FTYPE.OP
  rule #t2aInstr<_>(ATYPE.OP:CvtOp)         => ATYPE.OP
  rule #t2aInstr<C>( block _OID:OptionalId TDS:TypeDecls IS end _OID') => #block(gatherTypes(result, TDS), #t2aInstrs<C>(IS), .Int)
  rule #t2aInstr<C>( loop  _OID:OptionalId TDS IS end _OID') => #loop(gatherTypes(result, TDS), #t2aInstrs<C>(IS), .Int)
  rule #t2aInstr<C>( if    _OID:OptionalId TDS IS else _OID':OptionalId IS' end _OID'') => #if(gatherTypes(result, TDS), #t2aInstrs<C>(IS), #t2aInstrs<C>(IS'), .Int)
  rule #t2aInstr<_C>(trap) => trap
  rule #t2aInstr<C>(#block(VT:VecType, IS:Instrs, BLOCKINFO)) => #block(VT, #t2aInstrs<C>(IS), BLOCKINFO)
  rule #t2aInstr<_>(init_local I V) => init_local I V
  rule #t2aInstr<_>(init_locals VS) => init_locals VS
  syntax Stmts  ::=
    "#t2aStmts" "<" Context ">" "(" Stmts ")" [function]
  syntax Defns  ::=
    "#t2aDefns" "<" Context ">" "(" Defns ")" [function]
  syntax Instrs  ::=
    "#t2aInstrs" "<" Context ">" "(" Instrs ")" [function]
  rule #t2aStmts<C>(S:Stmt SS:Stmts) => #t2aStmt<C>(S) #t2aStmts<C>(SS)
  rule #t2aStmts<_>(.Stmts) => .Stmts
  rule #t2aDefns<C>(D:Defn DS:Defns) => #t2aDefn<C>(D) #t2aDefns<C>(DS)
  rule #t2aDefns<_>(.Defns) => .Defns
  rule #t2aInstrs<C>(I:Instr IS:Instrs) => #t2aInstr<C>(I) #t2aInstrs<C>(IS)
  rule #t2aInstrs<_>(.Instrs) => .Instrs
  syntax Map  ::=
    "#idcTypes" "(" Defns ")" [function, klabel(#idcTypes)]
  | "#idcTypesAux" "(" Defns "," Int "," Map ")" [function, klabel(#idcTypesAux)]
  rule #idcTypes(DEFNS) => #idcTypesAux(DEFNS, 0, .Map)
  rule #idcTypesAux((type ID:Identifier (func _)) TS => TS, IDX => IDX +Int 1,  ACC => ACC [ ID <- IDX ]) requires notBool ID in_keys(ACC)
  rule #idcTypesAux((type               (func _)) TS => TS, IDX => IDX +Int 1, _ACC)
  rule #idcTypesAux(.Defns, _, ACC) => ACC
  syntax Map  ::=
    "#idcFuncs" "(" Defns "," Defns ")" [function, klabel(#idcFuncs)]
  | "#idcFuncsAux" "(" Defns "," Defns "," Int "," Map ")" [function, klabel(#idcFuncsAux)]
  rule #idcFuncs(IMPORTS, DEFNS) => #idcFuncsAux(IMPORTS, DEFNS, 0, .Map)
  rule #idcFuncsAux((import _ _ (func ID:Identifier _)) IS => IS, _FS,  IDX => IDX +Int 1,  ACC => ACC [ ID <-IDX ]) requires notBool ID in_keys(ACC)
  rule #idcFuncsAux((import _ _ (func               _)) IS => IS, _FS,  IDX => IDX +Int 1, _ACC)
  rule #idcFuncsAux(_I                                  IS => IS, _FS, _IDX              , _ACC)  [owise]
  rule #idcFuncsAux(.Defns, (func ID:Identifier _) FS => FS, IDX => IDX +Int 1,  ACC => ACC [ ID <- IDX ]) requires notBool ID in_keys(ACC)
  rule #idcFuncsAux(.Defns, (func      _:FuncSpec) FS => FS, IDX => IDX +Int 1, _ACC)
  rule #idcFuncsAux(.Defns, .Defns, _, ACC) => ACC
  syntax Map  ::=
    "#idcGlobals" "(" Defns "," Defns ")" [function, klabel(#idcGlobals)]
  | "#idcGlobalsAux" "(" Defns "," Defns "," Int "," Map ")" [function, klabel(#idcGlobalsAux)]
  rule #idcGlobals(IMPORTS, DEFNS) => #idcGlobalsAux(IMPORTS, DEFNS, 0, .Map)
  rule #idcGlobalsAux((import _ _ (global ID:Identifier _)) IS => IS, _GS,  IDX => IDX +Int 1,  ACC => ACC [ ID <-IDX ]) requires notBool ID in_keys(ACC)
  rule #idcGlobalsAux((import _ _ (global               _)) IS => IS, _GS,  IDX => IDX +Int 1, _ACC)
  rule #idcGlobalsAux(_I                                    IS => IS, _GS, _IDX              , _ACC)  [owise]
  rule #idcGlobalsAux(.Defns, #global(... metadata: ID:Identifier) GS => GS, IDX => IDX +Int 1,  ACC => ACC [ ID <- IDX ]) requires notBool ID in_keys(ACC)
  rule #idcGlobalsAux(.Defns, #global(...) GS => GS, IDX => IDX +Int 1, _ACC)  [owise]
  rule #idcGlobalsAux(.Defns, .Defns, _, ACC) => ACC
  syntax Map  ::=
    "#ids2Idxs" "(" TypeUse "," LocalDecls ")" [function, klabel(#ids2Idxs), total]
  | "#ids2Idxs" "(" Int "," TypeUse "," LocalDecls ")" [function, klabel(#ids2Idxs), total]
  rule #ids2Idxs(TU, LDS) => #ids2Idxs(0, TU, LDS)
  rule #ids2Idxs(_, .TypeDecls, .LocalDecls) => .Map
  rule #ids2Idxs(N, (type _)    , LDS) => #ids2Idxs(N, .TypeDecls, LDS)
  rule #ids2Idxs(N, (type _) TDS, LDS) => #ids2Idxs(N, TDS       , LDS)
  rule #ids2Idxs(N, (param ID:Identifier _) TDS, LDS)
      => (ID |-> N) #ids2Idxs(N +Int 1, TDS, LDS)
  rule #ids2Idxs(N,  (param _)   TDS, LDS) => #ids2Idxs(N +Int 1, TDS, LDS)
  rule #ids2Idxs(N, _TD:TypeDecl TDS, LDS) => #ids2Idxs(N       , TDS, LDS)  [owise]
  rule #ids2Idxs(N, .TypeDecls, local ID:Identifier _ LDS:LocalDecls)
      => (ID |-> N) #ids2Idxs(N +Int 1, .TypeDecls, LDS)
  rule #ids2Idxs(N, .TypeDecls, _LD:LocalDecl LDS) => #ids2Idxs(N +Int 1, .TypeDecls, LDS)  [owise]
endmodule

module WASM-AUTO-ALLOCATE
  imports public WASM-TEXT
  syntax Stmt  ::=
    "newEmptyModule" WasmString
  rule <instrs> newEmptyModule MODNAME => . ... </instrs>
         <moduleRegistry> MR => MR [ MODNAME <- NEXT ] </moduleRegistry>
         <nextModuleIdx> NEXT => NEXT +Int 1 </nextModuleIdx>
         <moduleInstances> ( .Bag => <moduleInst> <modIdx> NEXT </modIdx> ... </moduleInst>) ... </moduleInstances>
  syntax Stmts  ::=
    "autoAllocModules" "(" ModuleDecl "," Map ")" [function, klabel(autoAllocModules)]
  | "#autoAllocModules" "(" Defns "," Map ")" [function, klabel(#autoAllocModules)]
  rule autoAllocModules(#module(... importDefns:IS), MR) => #autoAllocModules(IS, MR)
  rule #autoAllocModules(.Defns, _) => .Stmts
  rule #autoAllocModules((#import(MOD, _, _) DS) => DS, MR) requires MOD in_keys(MR)
  rule #autoAllocModules((#import(MOD, _, _) DS), MR)
      => newEmptyModule MOD #autoAllocModules(DS, MR [MOD <- -1])
      requires notBool MOD in_keys(MR)
  rule <instrs> MD:ModuleDecl
               => sequenceStmts(autoAllocModules(MD, MR))
               ~> MD
              ...
         </instrs>
         <moduleRegistry> MR </moduleRegistry>
      requires autoAllocModules(MD, MR) =/=K .Stmts
       [priority(10)]
  syntax Instr  ::=
    "hostCall" "(" String "," String "," FuncType ")" [klabel(hostCall)]
  rule <instrs> (. => allocfunc(HOSTMOD, NEXTADDR, TYPE, [ .ValTypes ], hostCall(wasmString2StringStripped(MOD), wasmString2StringStripped(NAME), TYPE) .Instrs, #meta(... id: String2Identifier("$auto-alloc:" +String #parseWasmString(MOD) +String ":" +String #parseWasmString(NAME) ), localIds: .Map )))
               ~> #import(MOD, NAME, #funcDesc(... type: TIDX))
              ...
         </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types> ... TIDX |-> TYPE ... </types>
           ...
        </moduleInst>
        <nextFuncAddr> NEXTADDR => NEXTADDR +Int 1 </nextFuncAddr>
        <moduleRegistry> ... MOD |-> HOSTMOD ... </moduleRegistry>
        <moduleInst>
          <modIdx> HOSTMOD </modIdx>
          <exports> EXPORTS => EXPORTS [NAME <- NEXTFUNC ] </exports>
          <funcAddrs> FS => FS [NEXTFUNC <- NEXTADDR] </funcAddrs>
          <nextFuncIdx> NEXTFUNC => NEXTFUNC +Int 1 </nextFuncIdx>
          <nextTypeIdx> NEXTTYPE => NEXTTYPE +Int 1 </nextTypeIdx>
          <types> TYPES => TYPES [ NEXTTYPE <- TYPE ] </types>
          ...
        </moduleInst>
      requires notBool NAME in_keys(EXPORTS)
  syntax String  ::=
    "wasmString2StringStripped" "(" WasmString ")" [function, klabel(wasmString2StringStripped)]
  | "#stripQuotes" "(" String ")" [function, klabel(#stripQuotes)]
  rule wasmString2StringStripped(WS) => #stripQuotes(#parseWasmString(WS))
  rule #stripQuotes(S) => replaceAll(S, "\"", "")
endmodule

module KRYPTO
  imports public STRING-SYNTAX
  imports public INT-SYNTAX
  imports public LIST
  syntax String  ::=
    "Keccak256" "(" String ")" [function, hook(KRYPTO.keccak256), klabel(Keccak256)]
  | "Sha256" "(" String ")" [function, hook(KRYPTO.sha256), klabel(Sha256)]
  | "Sha512" "(" String ")" [function, hook(KRYPTO.sha512), klabel(Sha512)]
  | "Sha512_256" "(" String ")" [function, hook(KRYPTO.sha512_256)]
  | "Sha3_256" "(" String ")" [function, hook(KRYPTO.sha3)]
  | "RipEmd160" "(" String ")" [function, hook(KRYPTO.ripemd160), klabel(RipEmd160)]
  | "Blake2Compress" "(" String ")" [function, hook(KRYPTO.blake2compress), klabel(Blake2Compress)]
  syntax String  ::=
    "Keccak256raw" "(" String ")" [function, hook(KRYPTO.keccak256raw), klabel(Keccak256raw)]
  | "Sha256raw" "(" String ")" [function, hook(KRYPTO.sha256raw), klabel(Sha256raw)]
  | "Sha512raw" "(" String ")" [function, hook(KRYPTO.sha512raw), klabel(Sha512raw)]
  | "Sha512_256raw" "(" String ")" [function, hook(KRYPTO.sha512_256raw)]
  | "Sha3_256raw" "(" String ")" [function, hook(KRYPTO.sha3raw)]
  | "RipEmd160raw" "(" String ")" [function, hook(KRYPTO.ripemd160raw), klabel(RipEmd160raw)]
  syntax String  ::=
    "ECDSARecover" "(" String "," Int "," String "," String ")" [function, hook(KRYPTO.ecdsaRecover), klabel(ECDSARecover)]
  | "ECDSASign" "(" String "," String ")" [function, hook(KRYPTO.ecdsaSign), klabel(ECDSASign)]
  | "ECDSAPubKey" "(" String ")" [function, hook(KRYPTO.ecdsaPubKey), klabel(ECDSAPubKey)]
  syntax G1Point  ::=
    "(" Int "," Int ")" [prefer]
  syntax G2Point  ::=
    "(" Int "x" Int "," Int "x" Int ")"
  syntax G1Point  ::=
    "BN128Add" "(" G1Point "," G1Point ")" [function, hook(KRYPTO.bn128add), klabel(BN128Add)]
  | "BN128Mul" "(" G1Point "," Int ")" [function, hook(KRYPTO.bn128mul), klabel(BN128Mul)]
  syntax Bool  ::=
    "BN128AtePairing" "(" List "," List ")" [function, hook(KRYPTO.bn128ate), klabel(BN128AtePairing)]
  syntax Bool  ::=
    "isValidPoint" "(" G1Point ")" [function, hook(KRYPTO.bn128valid), klabel(isValidPoint)]
  | "isValidPoint" "(" G2Point ")" [function, hook(KRYPTO.bn128g2valid), klabel(isValidG2Point)]
endmodule

module BYTES-TYPE
  imports public BYTES
  syntax WrappedBytes
  syntax BYTES
  syntax WrappedBytes  ::=
    "wrap" "(" Bytes ")" [klabel(wrapBytes), symbol]
  syntax Bytes  ::=
    "unwrap" "(" WrappedBytes ")" [function, injective, klabel(unwrapBytes), symbol, total]
  rule unwrap(wrap(A:Bytes)) => A
endmodule

module LIST-BYTES
  imports private INT-SYNTAX
  imports private BASIC-K
  imports public BYTES-TYPE
  syntax Bytes
  syntax ListBytes [hook(LIST.List)]
  syntax ListBytes  ::=
    ListBytes ListBytes [assoc, element(ListBytesItem), format(%1%n%2), function, hook(LIST.concat), klabel(_ListBytes_), left, smtlib(smt_seq_concat), symbol, total, unit(.ListBytes)]
  syntax ListBytes  ::=
    ".ListBytes" [function, hook(LIST.unit), klabel(.ListBytes), smtlib(smt_seq_nil), symbol, total]
  syntax ListBytes  ::=
    "ListItem" "(" WrappedBytes ")" [function, hook(LIST.element), klabel(ListBytesItem), smtlib(smt_seq_elem), symbol, total]
  syntax WrappedBytes  ::=
    ListBytes "[" Int "]" [function, hook(LIST.get), klabel(ListBytes:get), symbol]
  syntax ListBytes  ::=
    ListBytes "[" index: Int "<-" value: WrappedBytes "]" [function, hook(LIST.update), klabel(ListBytes:set), symbol]
  syntax ListBytes  ::=
    "makeListBytes" "(" length: Int "," value: WrappedBytes ")" [function, hook(LIST.make), klabel(makeListBytes)]
  syntax ListBytes  ::=
    "updateList" "(" dest: ListBytes "," index: Int "," src: ListBytes ")" [function, hook(LIST.updateAll), klabel(updateList)]
  syntax ListBytes  ::=
    "fillList" "(" ListBytes "," index: Int "," length: Int "," value: WrappedBytes ")" [function, hook(LIST.fill), klabel(fillList)]
  syntax ListBytes  ::=
    "range" "(" ListBytes "," fromFront: Int "," fromBack: Int ")" [function, hook(LIST.range), klabel(ListBytes:range), symbol]
  syntax Bool  ::=
    WrappedBytes "in" ListBytes [function, hook(LIST.in), klabel(_inListBytes_), symbol, total]
  syntax Int  ::=
    "size" "(" ListBytes ")" [function, hook(LIST.size), klabel(sizeListBytes), smtlib(smt_seq_len), symbol, total]
endmodule

module LIST-BYTES-EXTENSIONS
  imports public BOOL
  imports public INT
  imports public LIST-BYTES
  syntax WrappedBytes  ::=
    ListBytes "[" Int "]" "orDefault" WrappedBytes [function, klabel(ListBytes:getOrDefault), symbol, total]
  syntax Bytes  ::=
    ListBytes "{{" Int "}}" [function, klabel(ListBytes:primitiveLookup), symbol]
  rule L:ListBytes {{ I:Int }} => unwrap( L[ I ] )
  syntax Bytes  ::=
    ListBytes "{{" Int "}}" "orDefault" Bytes [function, klabel(ListBytes:primitiveLookupOrDefault), symbol, total]
  rule L:ListBytes {{ I:Int }} orDefault Value:Bytes
      => unwrap( L [I] orDefault wrap(Value) )
  rule ListItem(V:WrappedBytes) _:ListBytes [0] orDefault _:WrappedBytes
      => V
  rule _:ListBytes ListItem(V:WrappedBytes) [-1] orDefault _:WrappedBytes
      => V
  rule .ListBytes [_:Int] orDefault D:WrappedBytes => D
  rule ListItem(_:WrappedBytes) L:ListBytes [I:Int] orDefault D:WrappedBytes
      => L[I -Int 1] orDefault D
    requires 0 <Int I
  rule L:ListBytes ListItem(_:WrappedBytes) [I:Int] orDefault D:WrappedBytes
      => L[I +Int 1] orDefault D
    requires I <Int 0
  rule L:ListBytes[I:Int] orDefault D:WrappedBytes => D
    requires notBool (0 -Int size(L) <=Int I andBool I <Int size(L))
     [simplification]
  syntax ListBytes  ::=
    "ListItemWrap" "(" Bytes ")" [function, klabel(ListBytesItemWrap), symbol, total]
  rule ListItemWrap( B:Bytes ) => ListItem(wrap(B))
endmodule

module MAP-BYTES-TO-BYTES
  imports private BOOL-SYNTAX
  imports private INT-SYNTAX
  imports private LIST-BYTES
  imports private LIST-BYTES
  imports private SET
  imports public BYTES-TYPE
  imports public BYTES-TYPE
  syntax Bytes
  syntax Bytes
  syntax MapBytesToBytes [hook(MAP.Map)]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes MapBytesToBytes [assoc, comm, element(_Bytes2Bytes|->_), format(%1%n%2), function, hook(MAP.concat), index(0), klabel(_MapBytesToBytes_), left, symbol, unit(.MapBytesToBytes)]
  syntax MapBytesToBytes  ::=
    ".MapBytesToBytes" [function, hook(MAP.unit), klabel(.MapBytesToBytes), symbol, total]
  syntax MapBytesToBytes  ::=
    WrappedBytes "Bytes2Bytes|->" WrappedBytes [function, hook(MAP.element), injective, klabel(_Bytes2Bytes|->_), symbol, total]
  syntax priority _Bytes2Bytes|->_  > _MapBytesToBytes_ .MapBytesToBytes
  syntax non-assoc _Bytes2Bytes|->_
  syntax WrappedBytes  ::=
    MapBytesToBytes "[" WrappedBytes "]" [function, hook(MAP.lookup), klabel(MapBytesToBytes:lookup), symbol]
  syntax WrappedBytes  ::=
    MapBytesToBytes "[" WrappedBytes "]" "orDefault" WrappedBytes [function, hook(MAP.lookupOrDefault), klabel(MapBytesToBytes:lookupOrDefault), symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "[" key: WrappedBytes "<-" value: WrappedBytes "]" [function, hook(MAP.update), klabel(MapBytesToBytes:update), prefer, symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "[" WrappedBytes "<-" "undef" "]" [function, hook(MAP.remove), klabel(_MapBytesToBytes[_<-undef]), symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "-Map" MapBytesToBytes [function, hook(MAP.difference), total]
  syntax MapBytesToBytes  ::=
    "updateMap" "(" MapBytesToBytes "," MapBytesToBytes ")" [function, hook(MAP.updateAll), klabel(updateMap), total]
  syntax MapBytesToBytes  ::=
    "removeAll" "(" MapBytesToBytes "," Set ")" [function, hook(MAP.removeAll), klabel(removeAll), total]
  syntax Set  ::=
    "keys" "(" MapBytesToBytes ")" [function, hook(MAP.keys), klabel(keys), total]
  syntax ListBytes  ::=
    "keys_list" "(" MapBytesToBytes ")" [function, hook(MAP.keys_list)]
  syntax Bool  ::=
    WrappedBytes "in_keys" "(" MapBytesToBytes ")" [function, hook(MAP.in_keys), total]
  syntax ListBytes  ::=
    "values" "(" MapBytesToBytes ")" [function, hook(MAP.values), klabel(values)]
  syntax Int  ::=
    "size" "(" MapBytesToBytes ")" [function, hook(MAP.size), klabel(MapBytesToBytes.sizeMap), symbol, total]
  syntax Bool  ::=
    MapBytesToBytes "<=Map" MapBytesToBytes [function, hook(MAP.inclusion), total]
  syntax WrappedBytes  ::=
    "choice" "(" MapBytesToBytes ")" [function, hook(MAP.choice), klabel(MapBytesToBytes:choice), symbol]
endmodule

module MAP-BYTES-TO-BYTES-PRIMITIVE
  imports public MAP-BYTES-TO-BYTES-PRIMITIVE-CONCRETE
  imports public MAP-BYTES-TO-BYTES-PRIMITIVE-SYMBOLIC
endmodule

module MAP-BYTES-TO-BYTES-PRIMITIVE-CONCRETE [concrete]
  imports public BOOL
  imports private K-EQUAL
  imports public MAP-BYTES-TO-BYTES
  syntax Bytes  ::=
    MapBytesToBytes "{{" Bytes "}}" [function, klabel(MapBytesToBytes:primitiveLookup), symbol]
  syntax Bytes  ::=
    MapBytesToBytes "{{" Bytes "}}" "orDefault" Bytes [function, klabel(MapBytesToBytes:primitiveLookupOrDefault), symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "{{" key: Bytes "<-" value: Bytes "}}" [function, klabel(MapBytesToBytes:primitiveUpdate), prefer, symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "{{" Bytes "<-" "undef" "}}" [function, klabel(MapBytesToBytes:primitiveRemove), symbol, total]
  syntax Bool  ::=
    Bytes "in_keys" "{{" MapBytesToBytes "}}" [function, klabel(MapBytesToBytes:primitiveInKeys), symbol, total]
  rule (M:MapBytesToBytes {{ Key:Bytes }})
      => (unwrap( M[wrap(Key)] ))
  rule M:MapBytesToBytes {{ Key:Bytes }} orDefault Value:Bytes
      => unwrap( M[wrap(Key)] orDefault wrap(Value) )
  rule M:MapBytesToBytes {{ Key:Bytes <- Value:Bytes }}
      => M[wrap(Key) <- wrap(Value)]
  rule M:MapBytesToBytes {{ Key:Bytes <- undef }}
      => M[wrap(Key) <- undef]
  rule Key:Bytes in_keys {{ M:MapBytesToBytes }} => wrap(Key) in_keys(M)
endmodule

module MAP-BYTES-TO-BYTES-PRIMITIVE-SYMBOLIC [symbolic]
  imports public BOOL
  imports private K-EQUAL
  imports public MAP-BYTES-TO-BYTES
  imports private MAP-BYTES-TO-BYTES-KORE-SYMBOLIC
  syntax Bytes  ::=
    MapBytesToBytes "{{" Bytes "}}" [function, klabel(MapBytesToBytes:primitiveLookup), symbol]
  syntax Bytes  ::=
    MapBytesToBytes "{{" Bytes "}}" "orDefault" Bytes [function, klabel(MapBytesToBytes:primitiveLookupOrDefault), symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "{{" key: Bytes "<-" value: Bytes "}}" [function, klabel(MapBytesToBytes:primitiveUpdate), prefer, symbol, total]
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "{{" Bytes "<-" "undef" "}}" [function, klabel(MapBytesToBytes:primitiveRemove), symbol, total]
  syntax Bool  ::=
    Bytes "in_keys" "{{" MapBytesToBytes "}}" [function, klabel(MapBytesToBytes:primitiveInKeys), symbol, total]
  rule (wrap(Key) Bytes2Bytes|-> V:WrappedBytes M:MapBytesToBytes)
          {{ Key:Bytes }}
      => unwrap( V )
      ensures notBool Key in_keys {{ M }}
  rule (wrap(Key) Bytes2Bytes|-> V:WrappedBytes M:MapBytesToBytes)
          {{ Key:Bytes }} orDefault _:Bytes
      => unwrap( V )
      ensures notBool Key in_keys {{ M }}
  rule M:MapBytesToBytes {{ Key:Bytes }} orDefault V:Bytes
      => V
      requires notBool Key in_keys {{ M }}
  rule (wrap(Key) Bytes2Bytes|-> _:WrappedBytes M:MapBytesToBytes)
          {{ Key:Bytes <- Value:Bytes }}
      => (wrap(Key) Bytes2Bytes|-> wrap(Value)) M
  rule M:MapBytesToBytes {{ Key:Bytes <- Value:Bytes }}
      => (wrap(Key) Bytes2Bytes|-> wrap(Value)) M
      requires notBool Key in_keys {{ M }}
  rule (wrap(Key) Bytes2Bytes|-> _:WrappedBytes M:MapBytesToBytes)
          {{ Key:Bytes <- undef }}
      => M
      ensures notBool Key in_keys {{ M }}
  rule M:MapBytesToBytes {{ Key:Bytes <- undef }}
      => M
      requires notBool Key in_keys {{ M }}
  rule Key:Bytes in_keys
          {{wrap(Key) Bytes2Bytes|-> _:WrappedBytes M:MapBytesToBytes}}
      => true
      ensures notBool Key in_keys {{ M }}
  rule _Key:Bytes in_keys {{ .MapBytesToBytes }}
      => false
  rule Key:Bytes in_keys
          {{Key2:WrappedBytes Bytes2Bytes|-> _:WrappedBytes M:MapBytesToBytes}}
      => Key in_keys {{ M }}
      requires Key =/=K unwrap( Key2 )
      ensures notBool Key2 in_keys (M)
       [simplification]
  rule M:MapBytesToBytes[Key:WrappedBytes]
      => wrap(M{{unwrap( Key )}})
       [simplification, symbolic(M)]
  rule M:MapBytesToBytes[Key:WrappedBytes]
      => wrap(M{{unwrap( Key )}})
       [simplification, symbolic(Key)]
  rule M:MapBytesToBytes{{Key}}
      => unwrap( M[wrap(Key)] )
       [concrete, simplification]
  rule M:MapBytesToBytes [ Key:WrappedBytes ] orDefault Value:WrappedBytes
      => wrap(M {{ unwrap( Key ) }} orDefault unwrap( Value ))
       [simplification, symbolic(M)]
  rule M:MapBytesToBytes [ Key:WrappedBytes ] orDefault Value:WrappedBytes
      => wrap(M {{ unwrap( Key ) }} orDefault unwrap( Value ))
       [simplification, symbolic(Key)]
  rule M:MapBytesToBytes [ Key:WrappedBytes ] orDefault Value:WrappedBytes
      => wrap(M {{ unwrap( Key ) }} orDefault unwrap( Value ))
       [simplification, symbolic(Value)]
  rule M:MapBytesToBytes{{Key}} orDefault Value
      => unwrap( M[wrap(Key)] orDefault wrap(Value) )
       [concrete, simplification]
  rule M:MapBytesToBytes[Key:WrappedBytes <- Value:WrappedBytes]
      => M {{ unwrap( Key ) <- unwrap( Value ) }}
       [simplification, symbolic(M)]
  rule M:MapBytesToBytes[Key:WrappedBytes <- Value:WrappedBytes]
      => M {{ unwrap( Key ) <- unwrap( Value ) }}
       [simplification, symbolic(Key)]
  rule M:MapBytesToBytes[Key:WrappedBytes <- Value:WrappedBytes]
      => M {{ unwrap( Key ) <- unwrap( Value ) }}
       [simplification, symbolic(Value)]
  rule M:MapBytesToBytes{{Key <- Value}} => M[wrap(Key) <- wrap(Value) ]
       [concrete, simplification]
  rule M:MapBytesToBytes[Key:WrappedBytes <- undef]
      => M {{ unwrap( Key ) <- undef }}
       [simplification, symbolic(M)]
  rule M:MapBytesToBytes[Key:WrappedBytes <- undef]
      => M {{ unwrap( Key ) <- undef }}
       [simplification, symbolic(Key)]
  rule M:MapBytesToBytes{{Key <- undef}} => M[wrap(Key) <- undef]
       [concrete, simplification]
  rule Key:WrappedBytes in_keys (M:MapBytesToBytes)
      => unwrap( Key ) in_keys {{M}}
       [simplification, symbolic(M)]
  rule Key:WrappedBytes in_keys (M:MapBytesToBytes)
      => unwrap( Key ) in_keys {{M}}
       [simplification, symbolic(Key)]
  rule Key in_keys {{M:MapBytesToBytes}} => wrap(Key) in_keys(M)
       [concrete, simplification]
  syntax Bool  ::=
    "definedPrimitiveLookup" "(" MapBytesToBytes "," Bytes ")" [function, klabel(definedPrimitiveLookup), total]
  rule definedPrimitiveLookup(M:MapBytesToBytes, K:Bytes) => K in_keys{{M}}
  rule #Ceil(@M:MapBytesToBytes {{@K:Bytes}})
      => {definedPrimitiveLookup(@M, @K) #Equals true}
          #And #Ceil(@M) #And #Ceil(@K)
       [simplification]
  rule M:MapBytesToBytes {{ K <- _ }} {{ K <- V }} => M {{ K <- V }}  [simplification]
  rule (K1 Bytes2Bytes|-> V1 M:MapBytesToBytes) {{ K2 <- V2 }}
      => (K1 Bytes2Bytes|-> V1 (M {{ K2 <- V2 }}))
      requires unwrap( K1 ) =/=K K2
       [simplification]
  rule (K1 Bytes2Bytes|-> V1 M:MapBytesToBytes) {{ K2 <- undef }}
      => (K1 Bytes2Bytes|-> V1 (M {{ K2 <- undef }}))
      requires unwrap( K1 ) =/=K K2
       [simplification]
  rule (K1 Bytes2Bytes|-> _V M:MapBytesToBytes) {{ K2 }} => M {{K2}}
      requires unwrap( K1 ) =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapBytesToBytes {{ K  <-  V1 }}) {{ K }}  => V1  [simplification]
  rule ( MAP:MapBytesToBytes {{ K1 <- _V1 }}) {{ K2 }} => MAP {{ K2 }}
      requires K1 =/=K K2
       [simplification]
  rule (K1 Bytes2Bytes|-> _V M:MapBytesToBytes) {{ K2 }} orDefault D
      => M {{K2}} orDefault D
      requires unwrap( K1 ) =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapBytesToBytes {{ K  <-  V1 }}) {{ K }} orDefault _ => V1  [simplification]
  rule ( MAP:MapBytesToBytes {{ K1 <- _V1 }}) {{ K2 }} orDefault D
      => MAP {{ K2 }} orDefault D
      requires K1 =/=K K2
       [simplification]
  rule K in_keys{{_M:MapBytesToBytes {{ K <- undef }} }} => false  [simplification]
  rule K in_keys{{_M:MapBytesToBytes {{ K <- _ }} }} => true  [simplification]
  rule K1 in_keys{{ M:MapBytesToBytes {{ K2 <- _ }} }}
      => true requires K1 ==K K2 orBool K1 in_keys{{M}}
       [simplification]
  rule K1 in_keys{{ M:MapBytesToBytes {{ K2 <- _ }} }}
      => K1 in_keys {{ M }}
      requires K1 =/=K K2
       [simplification]
  rule K1 in_keys {{ (K2 Bytes2Bytes|-> V) M:MapBytesToBytes }}
      => K1 ==K unwrap( K2 ) orBool K1 in_keys {{ M }}
    requires definedMapElementConcat(K2, V, M)
     [simplification(100)]
  rule {false #Equals @Key in_keys{{ Key' Bytes2Bytes|-> Val @M:MapBytesToBytes }}}
      =>  #Ceil(@Key) #And #Ceil(Key' Bytes2Bytes|-> Val @M)
          #And #Not({ @Key #Equals unwrap( Key' ) })
          #And {false #Equals @Key in_keys{{@M}}}
       [simplification]
  rule {@Key in_keys{{Key' Bytes2Bytes|-> Val @M:MapBytesToBytes}} #Equals false}
      =>  #Ceil(@Key) #And #Ceil(Key' Bytes2Bytes|-> Val @M)
          #And #Not({@Key #Equals unwrap( Key' ) })
          #And {@Key in_keys{{@M}} #Equals false}
       [simplification]
endmodule

module MAP-BYTES-TO-BYTES-KORE-SYMBOLIC
  imports public MAP-BYTES-TO-BYTES
  imports private K-EQUAL
  imports private BOOL
  syntax Bool  ::=
    "definedMapElementConcat" "(" WrappedBytes "," WrappedBytes "," MapBytesToBytes ")" [function, klabel(definedMapElementConcat), total]
  rule definedMapElementConcat(K, _V, M:MapBytesToBytes) => notBool K in_keys(M)
  rule #Ceil(@M:MapBytesToBytes [@K:WrappedBytes])
      => {(@K in_keys(@M)) #Equals true}
          #And #Ceil(@M) #And #Ceil(@K)
       [simplification]
  rule (K Bytes2Bytes|-> _ M:MapBytesToBytes) [ K <- V ] => (K Bytes2Bytes|-> V M)  [simplification]
  rule M:MapBytesToBytes [ K <- V ] => (K Bytes2Bytes|-> V M) requires notBool (K in_keys(M))
       [simplification]
  rule M:MapBytesToBytes [ K <- _ ] [ K <- V ] => M [ K <- V ]  [simplification]
  rule (K1 Bytes2Bytes|-> V1 M:MapBytesToBytes) [ K2 <- V2 ] => (K1 Bytes2Bytes|-> V1 (M [ K2 <- V2 ]))
      requires K1 =/=K K2
       [simplification]
  rule (K Bytes2Bytes|-> _ M:MapBytesToBytes) [ K <- undef ] => M
      ensures notBool (K in_keys(M))
       [simplification]
  rule M:MapBytesToBytes [ K <- undef ] => M
      requires notBool (K in_keys(M))
       [simplification]
  rule (K1 Bytes2Bytes|-> V1 M:MapBytesToBytes) [ K2 <- undef ]
      => (K1 Bytes2Bytes|-> V1 (M [ K2 <- undef ]))
      requires K1 =/=K K2
       [simplification]
  rule (K  Bytes2Bytes|->  V M:MapBytesToBytes) [ K ] => V
      ensures notBool (K in_keys(M))
       [simplification]
  rule (K1 Bytes2Bytes|-> _V M:MapBytesToBytes) [ K2 ] => M [K2]
      requires K1 =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapBytesToBytes [ K  <-  V1 ]) [ K ]  => V1  [simplification]
  rule ( MAP:MapBytesToBytes [ K1 <- _V1 ]) [ K2 ] => MAP [ K2 ]
      requires K1 =/=K K2
       [simplification]
  rule (K  Bytes2Bytes|->  V M:MapBytesToBytes) [  K ] orDefault _ => V
      ensures notBool (K in_keys(M))
       [simplification]
  rule (K1 Bytes2Bytes|-> _V M:MapBytesToBytes) [ K2 ] orDefault D
      => M [K2] orDefault D
      requires K1 =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapBytesToBytes [ K  <-  V1 ]) [ K ] orDefault _ => V1  [simplification]
  rule ( MAP:MapBytesToBytes [ K1 <- _V1 ]) [ K2 ] orDefault D
      => MAP [ K2 ] orDefault D
      requires K1 =/=K K2
       [simplification]
  rule .MapBytesToBytes [ _ ] orDefault D => D  [simplification]
  rule K in_keys(_M:MapBytesToBytes [ K <- undef ]) => false  [simplification]
  rule K in_keys(_M:MapBytesToBytes [ K <- _ ]) => true  [simplification]
  rule K1 in_keys(M:MapBytesToBytes [ K2 <- _ ])
      => true requires K1 ==K K2 orBool K1 in_keys(M)
       [simplification]
  rule K1 in_keys(M:MapBytesToBytes [ K2 <- _ ])
      => K1 in_keys(M)
      requires K1 =/=K K2
       [simplification]
  rule K in_keys((K Bytes2Bytes|-> V) M:MapBytesToBytes)
      => true
    requires definedMapElementConcat(K, V, M)
     [simplification(50)]
  rule K1 in_keys((K2 Bytes2Bytes|-> V) M:MapBytesToBytes)
      => K1 in_keys(M)
    requires true
        andBool definedMapElementConcat(K2, V, M)
        andBool K1 =/=K K2
     [simplification(50)]
  rule K1 in_keys((K2 Bytes2Bytes|-> V) M:MapBytesToBytes)
      => K1 ==K K2 orBool K1 in_keys(M)
    requires definedMapElementConcat(K2, V, M)
     [simplification(100)]
  rule {false #Equals @Key in_keys(.MapBytesToBytes)} => #Ceil(@Key)  [simplification]
  rule {@Key in_keys(.MapBytesToBytes) #Equals false} => #Ceil(@Key)  [simplification]
  rule {false #Equals @Key in_keys(Key' Bytes2Bytes|-> Val @M:MapBytesToBytes)}
      =>  #Ceil(@Key) #And #Ceil(Key' Bytes2Bytes|-> Val @M)
          #And #Not({@Key #Equals Key'})
          #And {false #Equals @Key in_keys(@M)}
       [simplification]
  rule {@Key in_keys(Key' Bytes2Bytes|-> Val @M:MapBytesToBytes) #Equals false}
      =>  #Ceil(@Key) #And #Ceil(Key' Bytes2Bytes|-> Val @M)
          #And #Not({@Key #Equals Key'})
          #And {@Key in_keys(@M) #Equals false}
       [simplification]
endmodule

module MAP-BYTES-TO-BYTES-CURLY-BRACE
  imports private BOOL
  imports private K-EQUAL-SYNTAX
  imports public MAP-BYTES-TO-BYTES
  syntax MapBytesToBytes  ::=
    MapBytesToBytes "{" key: WrappedBytes "<-" value: WrappedBytes "}" [function, klabel(MapBytesToBytes:curly_update), symbol, total]
  rule M:MapBytesToBytes{Key <- Value} => M (Key Bytes2Bytes|-> Value)
    requires notBool Key in_keys(M)
  rule (Key Bytes2Bytes|-> _ M:MapBytesToBytes){Key <- Value}
      => M (Key Bytes2Bytes|-> Value)
  rule (M:MapBytesToBytes{Key <- Value})(A Bytes2Bytes|-> B N:MapBytesToBytes)
      => (M (A Bytes2Bytes|-> B)) {Key <- Value} N
      requires notBool A ==K Key
       [simplification]
  rule M:MapBytesToBytes{Key1 <- Value1}[Key2 <- Value2]
      => ((M:MapBytesToBytes[Key2 <- Value2]{Key1 <- Value1}) #And #Not ({Key1 #Equals Key2}))
        #Or ((M:MapBytesToBytes[Key2 <- Value2]) #And {Key1 #Equals Key2})
       [simplification(20)]
  rule M:MapBytesToBytes[Key <- Value]
      => M:MapBytesToBytes{Key <- Value}
       [simplification(100)]
  rule M:MapBytesToBytes{Key1 <- _Value1}[Key2] orDefault Value2
      => M[Key2] orDefault Value2
      requires Key1 =/=K Key2
       [simplification]
  rule _M:MapBytesToBytes{Key <- Value1}[Key] orDefault _Value2
      => Value1
       [simplification]
  rule M:MapBytesToBytes{Key1 <- Value1}[Key2]
      => (M[Key2] #And #Not ({Key1 #Equals Key2}))
        #Or (Value1 #And {Key1 #Equals Key2})
       [simplification]
  rule Key1 in_keys(_:MapBytesToBytes{Key1 <- _})
      => true
       [simplification(50)]
  rule Key1 in_keys(M:MapBytesToBytes{Key2 <- _})
      => Key1 in_keys(M)
      requires notBool Key1 ==K Key2
       [simplification(50)]
  rule K1 in_keys(M:MapBytesToBytes { K2 <- _ })
      => K1 ==K K2 orBool K1 in_keys(M)
     [simplification(100)]
endmodule

module INT-TYPE
  imports public INT
  syntax WrappedInt
  syntax Int
  syntax WrappedInt  ::=
    "wrap" "(" Int ")" [klabel(wrapInt), symbol]
  syntax Int  ::=
    "unwrap" "(" WrappedInt ")" [function, injective, klabel(unwrapInt), symbol, total]
  rule unwrap(wrap(A:Int)) => A
endmodule

module MAP-INT-TO-BYTES
  imports private BOOL-SYNTAX
  imports private INT-SYNTAX
  imports private LIST-BYTES
  imports private LIST
  imports private SET
  imports public INT-TYPE
  imports public BYTES-TYPE
  syntax Int
  syntax Bytes
  syntax MapIntToBytes [hook(MAP.Map)]
  syntax MapIntToBytes  ::=
    MapIntToBytes MapIntToBytes [assoc, comm, element(_Int2Bytes|->_), format(%1%n%2), function, hook(MAP.concat), index(0), klabel(_MapIntToBytes_), left, symbol, unit(.MapIntToBytes)]
  syntax MapIntToBytes  ::=
    ".MapIntToBytes" [function, hook(MAP.unit), klabel(.MapIntToBytes), symbol, total]
  syntax MapIntToBytes  ::=
    WrappedInt "Int2Bytes|->" WrappedBytes [function, hook(MAP.element), injective, klabel(_Int2Bytes|->_), symbol, total]
  syntax priority _Int2Bytes|->_  > _MapIntToBytes_ .MapIntToBytes
  syntax non-assoc _Int2Bytes|->_
  syntax WrappedBytes  ::=
    MapIntToBytes "[" WrappedInt "]" [function, hook(MAP.lookup), klabel(MapIntToBytes:lookup), symbol]
  syntax WrappedBytes  ::=
    MapIntToBytes "[" WrappedInt "]" "orDefault" WrappedBytes [function, hook(MAP.lookupOrDefault), klabel(MapIntToBytes:lookupOrDefault), symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "[" key: WrappedInt "<-" value: WrappedBytes "]" [function, hook(MAP.update), klabel(MapIntToBytes:update), prefer, symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "[" WrappedInt "<-" "undef" "]" [function, hook(MAP.remove), klabel(_MapIntToBytes[_<-undef]), symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "-Map" MapIntToBytes [function, hook(MAP.difference), total]
  syntax MapIntToBytes  ::=
    "updateMap" "(" MapIntToBytes "," MapIntToBytes ")" [function, hook(MAP.updateAll), klabel(updateMap), total]
  syntax MapIntToBytes  ::=
    "removeAll" "(" MapIntToBytes "," Set ")" [function, hook(MAP.removeAll), klabel(removeAll), total]
  syntax Set  ::=
    "keys" "(" MapIntToBytes ")" [function, hook(MAP.keys), klabel(keys), total]
  syntax List  ::=
    "keys_list" "(" MapIntToBytes ")" [function, hook(MAP.keys_list)]
  syntax Bool  ::=
    WrappedInt "in_keys" "(" MapIntToBytes ")" [function, hook(MAP.in_keys), total]
  syntax ListBytes  ::=
    "values" "(" MapIntToBytes ")" [function, hook(MAP.values), klabel(values)]
  syntax Int  ::=
    "size" "(" MapIntToBytes ")" [function, hook(MAP.size), klabel(MapIntToBytes.sizeMap), symbol, total]
  syntax Bool  ::=
    MapIntToBytes "<=Map" MapIntToBytes [function, hook(MAP.inclusion), total]
  syntax WrappedInt  ::=
    "choice" "(" MapIntToBytes ")" [function, hook(MAP.choice), klabel(MapIntToBytes:choice), symbol]
endmodule

module MAP-INT-TO-BYTES-PRIMITIVE
  imports public MAP-INT-TO-BYTES-PRIMITIVE-CONCRETE
  imports public MAP-INT-TO-BYTES-PRIMITIVE-SYMBOLIC
endmodule

module MAP-INT-TO-BYTES-PRIMITIVE-CONCRETE [concrete]
  imports public BOOL
  imports private K-EQUAL
  imports public MAP-INT-TO-BYTES
  syntax Bytes  ::=
    MapIntToBytes "{{" Int "}}" [function, klabel(MapIntToBytes:primitiveLookup), symbol]
  syntax Bytes  ::=
    MapIntToBytes "{{" Int "}}" "orDefault" Bytes [function, klabel(MapIntToBytes:primitiveLookupOrDefault), symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "{{" key: Int "<-" value: Bytes "}}" [function, klabel(MapIntToBytes:primitiveUpdate), prefer, symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "{{" Int "<-" "undef" "}}" [function, klabel(MapIntToBytes:primitiveRemove), symbol, total]
  syntax Bool  ::=
    Int "in_keys" "{{" MapIntToBytes "}}" [function, klabel(MapIntToBytes:primitiveInKeys), symbol, total]
  rule (M:MapIntToBytes {{ Key:Int }})
      => (unwrap( M[wrap(Key)] ))
  rule M:MapIntToBytes {{ Key:Int }} orDefault Value:Bytes
      => unwrap( M[wrap(Key)] orDefault wrap(Value) )
  rule M:MapIntToBytes {{ Key:Int <- Value:Bytes }}
      => M[wrap(Key) <- wrap(Value)]
  rule M:MapIntToBytes {{ Key:Int <- undef }}
      => M[wrap(Key) <- undef]
  rule Key:Int in_keys {{ M:MapIntToBytes }} => wrap(Key) in_keys(M)
endmodule

module MAP-INT-TO-BYTES-PRIMITIVE-SYMBOLIC [symbolic]
  imports public BOOL
  imports private K-EQUAL
  imports public MAP-INT-TO-BYTES
  imports private MAP-INT-TO-BYTES-KORE-SYMBOLIC
  syntax Bytes  ::=
    MapIntToBytes "{{" Int "}}" [function, klabel(MapIntToBytes:primitiveLookup), symbol]
  syntax Bytes  ::=
    MapIntToBytes "{{" Int "}}" "orDefault" Bytes [function, klabel(MapIntToBytes:primitiveLookupOrDefault), symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "{{" key: Int "<-" value: Bytes "}}" [function, klabel(MapIntToBytes:primitiveUpdate), prefer, symbol, total]
  syntax MapIntToBytes  ::=
    MapIntToBytes "{{" Int "<-" "undef" "}}" [function, klabel(MapIntToBytes:primitiveRemove), symbol, total]
  syntax Bool  ::=
    Int "in_keys" "{{" MapIntToBytes "}}" [function, klabel(MapIntToBytes:primitiveInKeys), symbol, total]
  rule (wrap(Key) Int2Bytes|-> V:WrappedBytes M:MapIntToBytes)
          {{ Key:Int }}
      => unwrap( V )
      ensures notBool Key in_keys {{ M }}
  rule (wrap(Key) Int2Bytes|-> V:WrappedBytes M:MapIntToBytes)
          {{ Key:Int }} orDefault _:Bytes
      => unwrap( V )
      ensures notBool Key in_keys {{ M }}
  rule M:MapIntToBytes {{ Key:Int }} orDefault V:Bytes
      => V
      requires notBool Key in_keys {{ M }}
  rule (wrap(Key) Int2Bytes|-> _:WrappedBytes M:MapIntToBytes)
          {{ Key:Int <- Value:Bytes }}
      => (wrap(Key) Int2Bytes|-> wrap(Value)) M
  rule M:MapIntToBytes {{ Key:Int <- Value:Bytes }}
      => (wrap(Key) Int2Bytes|-> wrap(Value)) M
      requires notBool Key in_keys {{ M }}
  rule (wrap(Key) Int2Bytes|-> _:WrappedBytes M:MapIntToBytes)
          {{ Key:Int <- undef }}
      => M
      ensures notBool Key in_keys {{ M }}
  rule M:MapIntToBytes {{ Key:Int <- undef }}
      => M
      requires notBool Key in_keys {{ M }}
  rule Key:Int in_keys
          {{wrap(Key) Int2Bytes|-> _:WrappedBytes M:MapIntToBytes}}
      => true
      ensures notBool Key in_keys {{ M }}
  rule _Key:Int in_keys {{ .MapIntToBytes }}
      => false
  rule Key:Int in_keys
          {{Key2:WrappedInt Int2Bytes|-> _:WrappedBytes M:MapIntToBytes}}
      => Key in_keys {{ M }}
      requires Key =/=K unwrap( Key2 )
      ensures notBool Key2 in_keys (M)
       [simplification]
  rule M:MapIntToBytes[Key:WrappedInt]
      => wrap(M{{unwrap( Key )}})
       [simplification, symbolic(M)]
  rule M:MapIntToBytes[Key:WrappedInt]
      => wrap(M{{unwrap( Key )}})
       [simplification, symbolic(Key)]
  rule M:MapIntToBytes{{Key}}
      => unwrap( M[wrap(Key)] )
       [concrete, simplification]
  rule M:MapIntToBytes [ Key:WrappedInt ] orDefault Value:WrappedBytes
      => wrap(M {{ unwrap( Key ) }} orDefault unwrap( Value ))
       [simplification, symbolic(M)]
  rule M:MapIntToBytes [ Key:WrappedInt ] orDefault Value:WrappedBytes
      => wrap(M {{ unwrap( Key ) }} orDefault unwrap( Value ))
       [simplification, symbolic(Key)]
  rule M:MapIntToBytes [ Key:WrappedInt ] orDefault Value:WrappedBytes
      => wrap(M {{ unwrap( Key ) }} orDefault unwrap( Value ))
       [simplification, symbolic(Value)]
  rule M:MapIntToBytes{{Key}} orDefault Value
      => unwrap( M[wrap(Key)] orDefault wrap(Value) )
       [concrete, simplification]
  rule M:MapIntToBytes[Key:WrappedInt <- Value:WrappedBytes]
      => M {{ unwrap( Key ) <- unwrap( Value ) }}
       [simplification, symbolic(M)]
  rule M:MapIntToBytes[Key:WrappedInt <- Value:WrappedBytes]
      => M {{ unwrap( Key ) <- unwrap( Value ) }}
       [simplification, symbolic(Key)]
  rule M:MapIntToBytes[Key:WrappedInt <- Value:WrappedBytes]
      => M {{ unwrap( Key ) <- unwrap( Value ) }}
       [simplification, symbolic(Value)]
  rule M:MapIntToBytes{{Key <- Value}} => M[wrap(Key) <- wrap(Value) ]
       [concrete, simplification]
  rule M:MapIntToBytes[Key:WrappedInt <- undef]
      => M {{ unwrap( Key ) <- undef }}
       [simplification, symbolic(M)]
  rule M:MapIntToBytes[Key:WrappedInt <- undef]
      => M {{ unwrap( Key ) <- undef }}
       [simplification, symbolic(Key)]
  rule M:MapIntToBytes{{Key <- undef}} => M[wrap(Key) <- undef]
       [concrete, simplification]
  rule Key:WrappedInt in_keys (M:MapIntToBytes)
      => unwrap( Key ) in_keys {{M}}
       [simplification, symbolic(M)]
  rule Key:WrappedInt in_keys (M:MapIntToBytes)
      => unwrap( Key ) in_keys {{M}}
       [simplification, symbolic(Key)]
  rule Key in_keys {{M:MapIntToBytes}} => wrap(Key) in_keys(M)
       [concrete, simplification]
  syntax Bool  ::=
    "definedPrimitiveLookup" "(" MapIntToBytes "," Int ")" [function, klabel(definedPrimitiveLookup), total]
  rule definedPrimitiveLookup(M:MapIntToBytes, K:Int) => K in_keys{{M}}
  rule #Ceil(@M:MapIntToBytes {{@K:Int}})
      => {definedPrimitiveLookup(@M, @K) #Equals true}
          #And #Ceil(@M) #And #Ceil(@K)
       [simplification]
  rule M:MapIntToBytes {{ K <- _ }} {{ K <- V }} => M {{ K <- V }}  [simplification]
  rule (K1 Int2Bytes|-> V1 M:MapIntToBytes) {{ K2 <- V2 }}
      => (K1 Int2Bytes|-> V1 (M {{ K2 <- V2 }}))
      requires unwrap( K1 ) =/=K K2
       [simplification]
  rule (K1 Int2Bytes|-> V1 M:MapIntToBytes) {{ K2 <- undef }}
      => (K1 Int2Bytes|-> V1 (M {{ K2 <- undef }}))
      requires unwrap( K1 ) =/=K K2
       [simplification]
  rule (K1 Int2Bytes|-> _V M:MapIntToBytes) {{ K2 }} => M {{K2}}
      requires unwrap( K1 ) =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapIntToBytes {{ K  <-  V1 }}) {{ K }}  => V1  [simplification]
  rule ( MAP:MapIntToBytes {{ K1 <- _V1 }}) {{ K2 }} => MAP {{ K2 }}
      requires K1 =/=K K2
       [simplification]
  rule (K1 Int2Bytes|-> _V M:MapIntToBytes) {{ K2 }} orDefault D
      => M {{K2}} orDefault D
      requires unwrap( K1 ) =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapIntToBytes {{ K  <-  V1 }}) {{ K }} orDefault _ => V1  [simplification]
  rule ( MAP:MapIntToBytes {{ K1 <- _V1 }}) {{ K2 }} orDefault D
      => MAP {{ K2 }} orDefault D
      requires K1 =/=K K2
       [simplification]
  rule K in_keys{{_M:MapIntToBytes {{ K <- undef }} }} => false  [simplification]
  rule K in_keys{{_M:MapIntToBytes {{ K <- _ }} }} => true  [simplification]
  rule K1 in_keys{{ M:MapIntToBytes {{ K2 <- _ }} }}
      => true requires K1 ==K K2 orBool K1 in_keys{{M}}
       [simplification]
  rule K1 in_keys{{ M:MapIntToBytes {{ K2 <- _ }} }}
      => K1 in_keys {{ M }}
      requires K1 =/=K K2
       [simplification]
  rule K1 in_keys {{ (K2 Int2Bytes|-> V) M:MapIntToBytes }}
      => K1 ==K unwrap( K2 ) orBool K1 in_keys {{ M }}
    requires definedMapElementConcat(K2, V, M)
     [simplification(100)]
  rule {false #Equals @Key in_keys{{ Key' Int2Bytes|-> Val @M:MapIntToBytes }}}
      =>  #Ceil(@Key) #And #Ceil(Key' Int2Bytes|-> Val @M)
          #And #Not({ @Key #Equals unwrap( Key' ) })
          #And {false #Equals @Key in_keys{{@M}}}
       [simplification]
  rule {@Key in_keys{{Key' Int2Bytes|-> Val @M:MapIntToBytes}} #Equals false}
      =>  #Ceil(@Key) #And #Ceil(Key' Int2Bytes|-> Val @M)
          #And #Not({@Key #Equals unwrap( Key' ) })
          #And {@Key in_keys{{@M}} #Equals false}
       [simplification]
endmodule

module MAP-INT-TO-BYTES-KORE-SYMBOLIC
  imports public MAP-INT-TO-BYTES
  imports private K-EQUAL
  imports private BOOL
  syntax Bool  ::=
    "definedMapElementConcat" "(" WrappedInt "," WrappedBytes "," MapIntToBytes ")" [function, klabel(definedMapElementConcat), total]
  rule definedMapElementConcat(K, _V, M:MapIntToBytes) => notBool K in_keys(M)
  rule #Ceil(@M:MapIntToBytes [@K:WrappedInt])
      => {(@K in_keys(@M)) #Equals true}
          #And #Ceil(@M) #And #Ceil(@K)
       [simplification]
  rule (K Int2Bytes|-> _ M:MapIntToBytes) [ K <- V ] => (K Int2Bytes|-> V M)  [simplification]
  rule M:MapIntToBytes [ K <- V ] => (K Int2Bytes|-> V M) requires notBool (K in_keys(M))
       [simplification]
  rule M:MapIntToBytes [ K <- _ ] [ K <- V ] => M [ K <- V ]  [simplification]
  rule (K1 Int2Bytes|-> V1 M:MapIntToBytes) [ K2 <- V2 ] => (K1 Int2Bytes|-> V1 (M [ K2 <- V2 ]))
      requires K1 =/=K K2
       [simplification]
  rule (K Int2Bytes|-> _ M:MapIntToBytes) [ K <- undef ] => M
      ensures notBool (K in_keys(M))
       [simplification]
  rule M:MapIntToBytes [ K <- undef ] => M
      requires notBool (K in_keys(M))
       [simplification]
  rule (K1 Int2Bytes|-> V1 M:MapIntToBytes) [ K2 <- undef ]
      => (K1 Int2Bytes|-> V1 (M [ K2 <- undef ]))
      requires K1 =/=K K2
       [simplification]
  rule (K  Int2Bytes|->  V M:MapIntToBytes) [ K ] => V
      ensures notBool (K in_keys(M))
       [simplification]
  rule (K1 Int2Bytes|-> _V M:MapIntToBytes) [ K2 ] => M [K2]
      requires K1 =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapIntToBytes [ K  <-  V1 ]) [ K ]  => V1  [simplification]
  rule ( MAP:MapIntToBytes [ K1 <- _V1 ]) [ K2 ] => MAP [ K2 ]
      requires K1 =/=K K2
       [simplification]
  rule (K  Int2Bytes|->  V M:MapIntToBytes) [  K ] orDefault _ => V
      ensures notBool (K in_keys(M))
       [simplification]
  rule (K1 Int2Bytes|-> _V M:MapIntToBytes) [ K2 ] orDefault D
      => M [K2] orDefault D
      requires K1 =/=K K2
      ensures notBool (K1 in_keys(M))
       [simplification]
  rule (_MAP:MapIntToBytes [ K  <-  V1 ]) [ K ] orDefault _ => V1  [simplification]
  rule ( MAP:MapIntToBytes [ K1 <- _V1 ]) [ K2 ] orDefault D
      => MAP [ K2 ] orDefault D
      requires K1 =/=K K2
       [simplification]
  rule .MapIntToBytes [ _ ] orDefault D => D  [simplification]
  rule K in_keys(_M:MapIntToBytes [ K <- undef ]) => false  [simplification]
  rule K in_keys(_M:MapIntToBytes [ K <- _ ]) => true  [simplification]
  rule K1 in_keys(M:MapIntToBytes [ K2 <- _ ])
      => true requires K1 ==K K2 orBool K1 in_keys(M)
       [simplification]
  rule K1 in_keys(M:MapIntToBytes [ K2 <- _ ])
      => K1 in_keys(M)
      requires K1 =/=K K2
       [simplification]
  rule K in_keys((K Int2Bytes|-> V) M:MapIntToBytes)
      => true
    requires definedMapElementConcat(K, V, M)
     [simplification(50)]
  rule K1 in_keys((K2 Int2Bytes|-> V) M:MapIntToBytes)
      => K1 in_keys(M)
    requires true
        andBool definedMapElementConcat(K2, V, M)
        andBool K1 =/=K K2
     [simplification(50)]
  rule K1 in_keys((K2 Int2Bytes|-> V) M:MapIntToBytes)
      => K1 ==K K2 orBool K1 in_keys(M)
    requires definedMapElementConcat(K2, V, M)
     [simplification(100)]
  rule {false #Equals @Key in_keys(.MapIntToBytes)} => #Ceil(@Key)  [simplification]
  rule {@Key in_keys(.MapIntToBytes) #Equals false} => #Ceil(@Key)  [simplification]
  rule {false #Equals @Key in_keys(Key' Int2Bytes|-> Val @M:MapIntToBytes)}
      =>  #Ceil(@Key) #And #Ceil(Key' Int2Bytes|-> Val @M)
          #And #Not({@Key #Equals Key'})
          #And {false #Equals @Key in_keys(@M)}
       [simplification]
  rule {@Key in_keys(Key' Int2Bytes|-> Val @M:MapIntToBytes) #Equals false}
      =>  #Ceil(@Key) #And #Ceil(Key' Int2Bytes|-> Val @M)
          #And #Not({@Key #Equals Key'})
          #And {@Key in_keys(@M) #Equals false}
       [simplification]
endmodule

module MAP-INT-TO-BYTES-CURLY-BRACE
  imports private BOOL
  imports private K-EQUAL-SYNTAX
  imports public MAP-INT-TO-BYTES
  syntax MapIntToBytes  ::=
    MapIntToBytes "{" key: WrappedInt "<-" value: WrappedBytes "}" [function, klabel(MapIntToBytes:curly_update), symbol, total]
  rule M:MapIntToBytes{Key <- Value} => M (Key Int2Bytes|-> Value)
    requires notBool Key in_keys(M)
  rule (Key Int2Bytes|-> _ M:MapIntToBytes){Key <- Value}
      => M (Key Int2Bytes|-> Value)
  rule (M:MapIntToBytes{Key <- Value})(A Int2Bytes|-> B N:MapIntToBytes)
      => (M (A Int2Bytes|-> B)) {Key <- Value} N
      requires notBool A ==K Key
       [simplification]
  rule M:MapIntToBytes{Key1 <- Value1}[Key2 <- Value2]
      => ((M:MapIntToBytes[Key2 <- Value2]{Key1 <- Value1}) #And #Not ({Key1 #Equals Key2}))
        #Or ((M:MapIntToBytes[Key2 <- Value2]) #And {Key1 #Equals Key2})
       [simplification(20)]
  rule M:MapIntToBytes[Key <- Value]
      => M:MapIntToBytes{Key <- Value}
       [simplification(100)]
  rule M:MapIntToBytes{Key1 <- _Value1}[Key2] orDefault Value2
      => M[Key2] orDefault Value2
      requires Key1 =/=K Key2
       [simplification]
  rule _M:MapIntToBytes{Key <- Value1}[Key] orDefault _Value2
      => Value1
       [simplification]
  rule M:MapIntToBytes{Key1 <- Value1}[Key2]
      => (M[Key2] #And #Not ({Key1 #Equals Key2}))
        #Or (Value1 #And {Key1 #Equals Key2})
       [simplification]
  rule Key1 in_keys(_:MapIntToBytes{Key1 <- _})
      => true
       [simplification(50)]
  rule Key1 in_keys(M:MapIntToBytes{Key2 <- _})
      => Key1 in_keys(M)
      requires notBool Key1 ==K Key2
       [simplification(50)]
  rule K1 in_keys(M:MapIntToBytes { K2 <- _ })
      => K1 ==K K2 orBool K1 in_keys(M)
     [simplification(100)]
endmodule

module ELROND-NODE
  imports public DOMAINS
  imports public LIST-BYTES
  imports public MAP-BYTES-TO-BYTES
  imports public MAP-INT-TO-BYTES
  imports public WASM
  configuration <node>
        <commands> .K </commands>
        <callState>
          // input
          <callee> .Bytes </callee>
          <vmInput>
            <caller> .Bytes </caller>
            <callArgs> .ListBytes </callArgs>
            <callValue> 0 </callValue>
            <esdtTransfers> .List </esdtTransfers>
            // gas
            <gasProvided> 0 </gasProvided>
            <gasPrice> 0 </gasPrice>
          </vmInput>
          // executional
          // every contract call uses its own wasm module instance, managed data heaps, and bytesStack.
          <wasm/>
          <bigIntHeap> .Map </bigIntHeap>
          <bufferHeap> .MapIntToBytes </bufferHeap>
          <bytesStack> .BytesStack </bytesStack>
          <contractModIdx> .Int </contractModIdx>
          // output
          <out> .ListBytes </out>
          <logs> .List </logs>
        </callState>
        <callStack> .List </callStack>
        <interimStates> .List </interimStates>
        <vmOutput> .VMOutput </vmOutput>
        <accounts>
          <account multiplicity="*" type="Map">
            <address> .Bytes </address>
            <nonce> 0 </nonce>
            <balance> 0 </balance>
            <esdtDatas>
              <esdtData multiplicity="*" type="Map">
                <esdtId> .Bytes </esdtId>
                <esdtBalance> 0 </esdtBalance>
                <frozen> false </frozen>
              </esdtData>
            </esdtDatas>







             <code> .Code </code>
             <ownerAddress> .Bytes </ownerAddress>




             <storage> .MapBytesToBytes </storage>
           </account>
         </accounts>
         <previousBlockInfo>
           <prevBlockTimestamp>  0 </prevBlockTimestamp>
           <prevBlockNonce>      0 </prevBlockNonce>
           <prevBlockRound>      0 </prevBlockRound>
           <prevBlockEpoch>      0 </prevBlockEpoch>
           <prevBlockRandomSeed> padRightBytes(.Bytes, 48, 0) </prevBlockRandomSeed>
         </previousBlockInfo>
         <currentBlockInfo>
           <curBlockTimestamp>  0 </curBlockTimestamp>
           <curBlockNonce>      0 </curBlockNonce>
           <curBlockRound>      0 </curBlockRound>
           <curBlockEpoch>      0 </curBlockEpoch>
           <curBlockRandomSeed> padRightBytes(.Bytes, 48, 0) </curBlockRandomSeed>
         </currentBlockInfo>
       </node>
  syntax VmInputCell
  syntax ReturnCode  ::=
    "OK" [klabel(OK), symbol]
  | ExceptionCode
  syntax ExceptionCode  ::=
    "FunctionNotFound" [klabel(FunctionNotFound), symbol]
  | "FunctionWrongSignature" [klabel(FunctionWrongSignature), symbol]
  | "ContractNotFound" [klabel(ContractNotFound), symbol]
  | "UserError" [klabel(UserError), symbol]
  | "OutOfGas" [klabel(OutOfGas), symbol]
  | "AccountCollision" [klabel(AccountCollision), symbol]
  | "OutOfFunds" [klabel(OutOfFunds), symbol]
  | "CallStackOverFlow" [klabel(CallStackOverFlow), symbol]
  | "ContractInvalid" [klabel(ContractInvalid), symbol]
  | "ExecutionFailed" [klabel(ExecutionFailed), symbol]
  | "UpgradeFailed" [klabel(UpgradeFailed), symbol]
  | "SimulateFailed" [klabel(SimulateFailed), symbol]
  syntax VMOutput  ::=
    ".VMOutput" [klabel(.VMOutput), symbol]
  | "VMOutput" "(" returnCode: ReturnCode "," returnMessage: Bytes "," out: ListBytes "," logs: List ")" [klabel(VMOutput), symbol]
  syntax Address  ::=
    Bytes
  | WasmStringToken
  syntax WasmStringToken  ::=
    "#unparseWasmString" "(" String ")" [function, hook(STRING.string2token), klabel(#unparseWasmString), total]
  syntax Bytes  ::=
    "#address2Bytes" "(" Address ")" [function, klabel(#address2Bytes), total]
  rule #address2Bytes(ADDR:WasmStringToken) => String2Bytes(#parseWasmString(ADDR))
  rule #address2Bytes(ADDR:Bytes) => ADDR
  syntax Code  ::=
    ".Code" [klabel(.Code), symbol]
  | ModuleDecl
  syntax ESDTTransfer  ::=
    "esdtTransfer" "(" tokenName: Bytes "," tokenValue: Int "," tokenNonce: Int ")" [klabel(esdtTransfer), symbol]
  syntax BytesStack  ::=
    List{Bytes,":"} [symbol(bytesStackList)]
  syntax BytesOp  ::=
    "#pushBytes" "(" Bytes ")" [klabel(#pushBytes)]
  | "#dropBytes"
  rule <instrs> #pushBytes(BS) => . ... </instrs>
         <bytesStack> STACK => BS : STACK </bytesStack>
  rule <instrs> #dropBytes => . ... </instrs>
         <bytesStack> _ : STACK => STACK </bytesStack>
  syntax InternalInstr  ::=
    "#returnLength"
  rule <instrs> #returnLength => i32.const lengthBytes(BS) ... </instrs>
         <bytesStack> BS : _ </bytesStack>
  syntax InternalInstr  ::=
    "#bytesEqual"
  rule <instrs> #bytesEqual => i32.const #bool( BS1 ==K BS2 ) ... </instrs>
         <bytesStack> BS1 : BS2 : _ </bytesStack>
  syntax InternalCmd  ::=
    "pushCallState"
  rule <commands> pushCallState => . ... </commands>
         <callStack> (.List => ListItem(CALLSTATE)) ... </callStack>
         <callState> CALLSTATE </callState>
       [priority(60)]
  syntax InternalCmd  ::=
    "popCallState"
  rule <commands> popCallState => . ... </commands>
         <callStack> (ListItem(CALLSTATE) => .List) ... </callStack>
         <callState> _ => CALLSTATE </callState>
       [priority(60)]
  syntax InternalCmd  ::=
    "dropCallState"
  rule <commands> dropCallState => . ... </commands>
         <callStack> (ListItem(_) => .List) ... </callStack>
       [priority(60)]
  syntax AccountsCellFragment
  syntax Accounts  ::=
    "{" AccountsCellFragment "}"
  syntax InternalCmd  ::=
    "pushWorldState"
  rule <commands> pushWorldState => . ... </commands>
         <interimStates> (.List => ListItem({ ACCTDATA })) ... </interimStates>
         <accounts>       ACCTDATA </accounts>
       [priority(60)]
  syntax InternalCmd  ::=
    "popWorldState"
  rule <commands> popWorldState => . ... </commands>
         <interimStates> (ListItem({ ACCTDATA }) => .List) ... </interimStates>
         <accounts>       _ => ACCTDATA </accounts>
       [priority(60)]
  syntax InternalCmd  ::=
    "dropWorldState"
  rule <commands> dropWorldState => . ... </commands>
         <interimStates> (ListItem(_) => .List) ... </interimStates>
       [priority(60)]
  syntax InternalCmd  ::=
    "#transferSuccess"
  syntax InternalCmd  ::=
    "checkAccountExists" "(" Bytes ")" [klabel(checkAccountExists)]
  rule [checkAccountExists-pass]: <commands> checkAccountExists(ADDR) => . ... </commands>
        <account>
          <address> ADDR </address>
          ...
        </account>
       [priority(60)]
  rule [checkAccountExists-fail]: <commands> checkAccountExists(ADDR)
                => #exception(ExecutionFailed, b"account not found: " +Bytes ADDR) ...
        </commands>
       [priority(61)]
  syntax InternalCmd  ::=
    "#exception" "(" ExceptionCode "," Bytes ")" [klabel(#exception)]
endmodule

module ESDT
  imports public ELROND-NODE
  syntax InternalCmd  ::=
    "transferESDT" "(" Bytes "," Bytes "," ESDTTransfer ")" [klabel(transferESDT)]
  | "transferESDTs" "(" Bytes "," Bytes "," List ")" [klabel(transferESDTs)]
  rule <commands> transferESDTs(_, _, .List) => #transferSuccess ... </commands>
  rule <commands> transferESDTs(FROM, TO, ListItem(T:ESDTTransfer) Ls)
                 => transferESDT(FROM, TO, T)
                 ~> transferESDTs(FROM, TO, Ls)
                    ...
         </commands>
  rule <commands> transferESDT(FROM, TO, esdtTransfer(TOKEN, VALUE, _))
                 => checkAccountExists(FROM)
                 ~> checkAccountExists(TO)
                 ~> checkESDTBalance(FROM, TOKEN, VALUE)
                 ~> addToESDTBalance(FROM, TOKEN, 0 -Int VALUE)
                 ~> addToESDTBalance(TO,   TOKEN, VALUE)
                    ...
         </commands>
  syntax InternalCmd  ::=
    "checkESDTBalance" "(" account: Bytes "," token: Bytes "," value: Int ")" [klabel(checkESDTBalance)]
  rule [checkESDTBalance]: <commands> checkESDTBalance(ACCT, TOKEN, VALUE) => . ... </commands>
        <account>
          <address> ACCT </address>
          <esdtData>
            <esdtId> TOKEN </esdtId>
            <esdtBalance> ORIGFROM </esdtBalance>
            ...
          </esdtData>
          ...
        </account>
      requires VALUE <=Int ORIGFROM
       [priority(60)]
  rule [checkESDTBalance-oof]: <commands> checkESDTBalance(_, _, _) => #exception(OutOfFunds, b"") ... </commands>
       [priority(61)]
  syntax InternalCmd  ::=
    "addToESDTBalance" "(" account: Bytes "," token: Bytes "," delta: Int ")" [klabel(addToESDTBalance)]
  rule [addToESDTBalance]: <commands> addToESDTBalance(ACCT, TOKEN, DELTA) => . ... </commands>
        <account>
          <address> ACCT </address>
          <esdtData>
            <esdtId> TOKEN </esdtId>
            <esdtBalance> ORIGFROM => ORIGFROM +Int DELTA </esdtBalance>
            ...
          </esdtData>
          ...
        </account>
       [priority(60)]
  rule [addToESDTBalance-new-esdtData]: <commands> addToESDTBalance(ACCT, TOKEN, DELTA) => . ... </commands>
        <account>
          <address> ACCT </address>
          (.Bag => <esdtData>
            <esdtId> TOKEN </esdtId>
            <esdtBalance> DELTA </esdtBalance>
            ...
          </esdtData>)
          ...
        </account>
       [priority(61)]
endmodule

module ELROND-CONFIG
  imports public KRYPTO
  imports public WASM-AUTO-ALLOCATE
  imports public ELROND-NODE
  imports public ESDT
  imports public LIST-BYTES
  imports public MAP-BYTES-TO-BYTES-PRIMITIVE
  configuration <elrond>
        <node/>
        <logging> "" </logging>
      </elrond>
  syntax Bool  ::=
    "#hasPrefix" "(" String "," String ")" [function, klabel(#hasPrefix), total]
  rule #hasPrefix(STR, PREFIX) => true
      requires lengthString(STR) >=Int lengthString(PREFIX)
       andBool substrString(STR, 0, lengthString(PREFIX)) ==String PREFIX
  rule #hasPrefix(STR, PREFIX) => false
      requires notBool (       lengthString(STR) >=Int lengthString(PREFIX)
                       andBool substrString(STR, 0, lengthString(PREFIX)) ==String PREFIX)
  syntax InternalInstr  ::=
    "#memStoreFromBytesStack" "(" Int ")" [klabel(#memStoreFromBytesStack)]
  | "#memStore" "(" offset: Int "," bytes: Bytes ")" [klabel(#memStore)]
  rule <instrs> #memStoreFromBytesStack(OFFSET) => #memStore(OFFSET, BS) ... </instrs>
         <bytesStack> BS : _ </bytesStack>
  rule <instrs> #memStore(OFFSET, _)
               => #throwException(ExecutionFailed, "bad bounds (lower)") ...
         </instrs>
      requires #signed(i32 , OFFSET) <Int 0
  rule <instrs> #memStore(OFFSET, BS)
               => #throwException(ExecutionFailed, "bad bounds (upper)") ...
         </instrs>
         <contractModIdx> MODIDX:Int </contractModIdx>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> MEMADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> MEMADDR </mAddr>
           <msize> SIZE </msize>
           ...
         </memInst>
      requires 0 <=Int #signed(i32 , OFFSET)
       andBool #signed(i32 , OFFSET) +Int lengthBytes(BS) >Int (SIZE *Int #pageSize())
  rule <instrs> #memStore(OFFSET, BS) => . ... </instrs>
         <contractModIdx> MODIDX:Int </contractModIdx>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> MEMADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> MEMADDR </mAddr>
           <msize> SIZE </msize>
           <mdata> DATA => #setBytesRange(DATA, OFFSET, BS) </mdata>
           ...
         </memInst>
      requires #signed(i32 , OFFSET) +Int lengthBytes(BS) <=Int (SIZE *Int #pageSize())
       andBool 0 <=Int #signed(i32 , OFFSET)
  rule [memStore-owise]: <instrs> #memStore(_, _) => #throwException(ExecutionFailed, "mem store: memory instance not found") ... </instrs>
       [owise]
  syntax InternalInstr  ::=
    "#memLoad" "(" offset: Int "," length: Int ")" [klabel(#memLoad)]
  rule [memLoad-negative-length]: <instrs> #memLoad(_, LENGTH) => #throwException(ExecutionFailed, "mem load: negative length") ... </instrs>
      requires #signed(i32 , LENGTH) <Int 0
  rule [memLoad-zero-length]: <instrs> #memLoad(_, 0) => . ... </instrs>
        <bytesStack> STACK => .Bytes : STACK </bytesStack>
  rule [memLoad-bad-bounds]: <instrs> #memLoad(OFFSET, LENGTH) => #throwException(ExecutionFailed, "mem load: bad bounds") ... </instrs>
         <contractModIdx> MODIDX:Int </contractModIdx>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> MEMADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> MEMADDR </mAddr>
           <msize> SIZE </msize>
           ...
         </memInst>
      requires #signed(i32 , LENGTH) >Int 0
       andBool (#signed(i32 , OFFSET) <Int 0
         orBool #signed(i32 , OFFSET) +Int #signed(i32 , LENGTH) >Int (SIZE *Int #pageSize()))
  rule [memLoad]: <instrs> #memLoad(OFFSET, LENGTH) => . ... </instrs>
         <bytesStack> STACK => #getBytesRange(DATA, OFFSET, LENGTH) : STACK </bytesStack>
         <contractModIdx> MODIDX:Int </contractModIdx>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> MEMADDR </memAddrs>
           ...
         </moduleInst>
         <memInst>
           <mAddr> MEMADDR </mAddr>
           <msize> SIZE </msize>
           <mdata> DATA </mdata>
           ...
         </memInst>
      requires #signed(i32 , LENGTH) >Int 0
       andBool #signed(i32 , OFFSET) >=Int 0
       andBool #signed(i32 , OFFSET) +Int #signed(i32 , LENGTH) <=Int (SIZE *Int #pageSize())
  rule [memLoad-owise]: <instrs> #memLoad(_, _) => #throwException(ExecutionFailed, "mem load: memory instance not found") ... </instrs>
       [owise]
  syntax InternalInstr  ::=
    "#storageStore"
  rule <instrs> #storageStore => #setStorage(KEY, VALUE) ... </instrs>
         <bytesStack> VALUE : KEY : STACK => STACK </bytesStack>
  syntax InternalInstr  ::=
    "#setStorage" "(" Bytes "," Bytes ")" [klabel(#setStorage)]
  rule <instrs> #setStorage(KEY, VALUE)
               => #isReservedKey(Bytes2String(KEY))
               ~> #writeToStorage(KEY, VALUE)
                  ...
         </instrs>
  syntax InternalInstr  ::=
    "#writeToStorage" "(" Bytes "," Bytes ")" [klabel(#writeToStorage)]
  rule <instrs> #writeToStorage(KEY, VALUE) => i32.const #storageStatus(STORAGE, KEY, VALUE) ... </instrs>
         <callee> CALLEE </callee>
         <account>
           <address> CALLEE </address>
           <storage> STORAGE => STORAGE{{KEY <- undef}} </storage>
           ...
         </account>
         requires VALUE ==K .Bytes
  rule <instrs> #writeToStorage(KEY, VALUE) => i32.const #storageStatus(STORAGE, KEY, VALUE) ... </instrs>
         <callee> CALLEE </callee>
         <account>
           <address> CALLEE </address>
           <storage> STORAGE => STORAGE{{KEY <- VALUE}} </storage>
           ...
         </account>
         requires VALUE =/=K .Bytes
  rule [writeToStorage-unknown-addr]: <instrs> #writeToStorage(_, _) => #throwException(ExecutionFailed, "writeToStorage: unknown account address") ... </instrs>
       [owise]
  syntax InternalInstr  ::=
    "#isReservedKey" "(" String ")" [klabel(#isReservedKey)]
  rule <instrs> #isReservedKey(KEY) => . ... </instrs>
      requires notBool #hasPrefix(KEY, "ELROND")
  rule <instrs> #isReservedKey(KEY)
               => #throwException(UserError, "cannot write to storage under Elrond reserved key") ...
         </instrs>
      requires         #hasPrefix(KEY, "ELROND")
  syntax InternalInstr  ::=
    "#storageLoad"
  | "#storageLoadFromAddress"
  rule <instrs> #storageLoad => #storageLoadFromAddress ... </instrs>
         <bytesStack> STACK => CALLEE : STACK </bytesStack>
         <callee> CALLEE </callee>
  rule [storageLoadFromAddress]: <instrs> #storageLoadFromAddress => . ... </instrs>
        <bytesStack> ADDR : KEY : STACK => #lookupStorage(STORAGE, KEY) : STACK </bytesStack>
        <account>
          <address> ADDR </address>
          <storage> STORAGE </storage>
          ...
        </account>
  rule [storageLoadFromAddress-unknown-addr]: <instrs> #storageLoadFromAddress
              => #throwException(UserError, "storageLoadFromAddress: unknown account address") ...
        </instrs>
        // ADDR does not match any user
        // <bytesStack> ADDR : _ : _ </bytesStack>
       [owise]
  syntax Bytes  ::=
    "#lookupStorage" "(" MapBytesToBytes "," key: Bytes ")" [function, klabel(#lookupStorage), total]
  rule #lookupStorage(STORAGE, KEY) => STORAGE{{KEY}} orDefault .Bytes
  syntax Int  ::=
    "#storageStatus" "(" MapBytesToBytes "," key: Bytes "," val: Bytes ")" [function, klabel(#storageStatus), total]
  | "#StorageUnmodified" "(" ")" [function, klabel(#StorageUnmodified), total]
  | "#StorageModified" "(" ")" [function, klabel(#StorageModified), total]
  | "#StorageAdded" "(" ")" [function, klabel(#StorageAdded), total]
  | "#StorageDeleted" "(" ")" [function, klabel(#StorageDeleted), total]
  rule #storageStatus(STOR, KEY,  VAL) => #StorageUnmodified() requires VAL  ==K .Bytes andBool notBool KEY in_keys{{STOR}}
  rule #storageStatus(STOR, KEY,  VAL) => #StorageUnmodified() requires VAL =/=K .Bytes andBool         KEY in_keys{{STOR}} andBool STOR{{KEY}}  ==K VAL
  rule #storageStatus(STOR, KEY,  VAL) => #StorageModified  () requires VAL =/=K .Bytes andBool         KEY in_keys{{STOR}} andBool STOR{{KEY}} =/=K VAL
  rule #storageStatus(STOR, KEY,  VAL) => #StorageAdded     () requires VAL =/=K .Bytes andBool notBool KEY in_keys{{STOR}}
  rule #storageStatus(STOR, KEY,  VAL) => #StorageDeleted   () requires VAL  ==K .Bytes andBool         KEY in_keys{{STOR}}
  rule #StorageUnmodified() => 0
  rule #StorageModified  () => 1
  rule #StorageAdded     () => 2
  rule #StorageDeleted   () => 3
  syntax Int  ::=
    "#cmpInt" "(" Int "," Int ")" [function, klabel(cmpInt), smtlib(cmpInt), symbol, total]
  rule #cmpInt(I1, I2) => -1 requires I1  <Int I2
  rule #cmpInt(I1, I2) =>  1 requires I1  >Int I2
  rule #cmpInt(I1, I2) =>  0 requires I1 ==Int I2
  syntax Int  ::=
    "#bigIntSign" "(" Int ")" [function, klabel(#bigIntSign), total]
  rule #bigIntSign(I) => 0  requires I ==Int 0
  rule #bigIntSign(I) => 1  requires I >Int 0
  rule #bigIntSign(I) => -1 requires I <Int 0
  syntax Int  ::=
    "minSInt32" [macro]
  | "maxSInt32" [macro]
  | "minUInt32" [macro]
  | "maxUInt32" [macro]
  | "minSInt64" [macro]
  | "maxSInt64" [macro]
  | "minUInt64" [macro]
  | "maxUInt64" [macro]
  rule minSInt32 => -2147483648
  rule maxSInt32 =>  2147483647
  rule minUInt32 =>  0
  rule maxUInt32 =>  4294967296
  rule minSInt64 => -9223372036854775808
  rule maxSInt64 =>  9223372036854775807
  rule minUInt64 =>  0
  rule maxUInt64 =>  18446744073709551615
  syntax InternalInstr  ::=
    "#returnIfUInt64" "(" Int "," String ")" [klabel(#returnIfUInt64)]
  | "#returnIfSInt64" "(" Int "," String ")" [klabel(#returnIfSInt64)]
  rule <instrs> #returnIfUInt64(V, _) => i64.const V ... </instrs>
      requires          minUInt64 <=Int V andBool V <=Int maxUInt64
  rule <instrs> #returnIfUInt64(V, ERRORMSG)
               => #throwException(UserError, ERRORMSG) ...
         </instrs>
      requires notBool (minUInt64 <=Int V andBool V <=Int maxUInt64)
  rule <instrs> #returnIfSInt64(V, _) => i64.const V ... </instrs>
      requires          minSInt64 <=Int V andBool V <=Int maxSInt64
  rule <instrs> #returnIfSInt64(V, ERRORMSG)
               => #throwException(UserError, ERRORMSG) ...
         </instrs>
      requires notBool (minSInt64 <=Int V andBool V <=Int maxSInt64)
  syntax InternalInstr  ::=
    "#loadBytesAsUInt64" "(" String ")" [klabel(#loadBytesAsUInt64)]
  | "#loadBytesAsSInt64" "(" String ")" [klabel(#loadBytesAsSInt64)]
  rule <instrs> #loadBytesAsUInt64(ERRORMSG) => #returnIfUInt64(Bytes2Int(BS, BE, Unsigned), ERRORMSG) ... </instrs>
         <bytesStack> BS : STACK => STACK </bytesStack>
  rule <instrs> #loadBytesAsSInt64(ERRORMSG) => #returnIfSInt64(Bytes2Int(BS, BE, Signed), ERRORMSG) ... </instrs>
         <bytesStack> BS : STACK => STACK </bytesStack>
  syntax InternalInstr  ::=
    "#appendToOutFromBytesStack"
  | "#appendToOut" "(" Bytes ")" [klabel(#appendToOut)]
  rule <instrs> #appendToOutFromBytesStack => . ... </instrs>
         <bytesStack> OUT : STACK => STACK </bytesStack>
         <out> ... (.ListBytes => ListItem(wrap(OUT))) </out>
  rule <instrs> #appendToOut(OUT) => . ... </instrs>
         <out> ... (.ListBytes => ListItem(wrap(OUT))) </out>
  syntax String  ::=
    "#alignHexString" "(" String ")" [function, klabel(#alignHexString), total]
  rule #alignHexString(S) => S             requires         lengthString(S) modInt 2 ==Int 0
  rule #alignHexString(S) => "0" +String S requires notBool lengthString(S) modInt 2 ==Int 0
  syntax Bytes  ::=
    "#parseHexBytes" "(" String ")" [function, klabel(#parseHexBytes)]
  | "#parseHexBytesAux" "(" String ")" [function, klabel(#parseHexBytesAux)]
  rule #parseHexBytes(S)  => #parseHexBytesAux(#alignHexString(S))
  rule #parseHexBytesAux("") => .Bytes
  rule #parseHexBytesAux(S)  => Int2Bytes(lengthString(S) /Int 2, String2Base(S, 16), BE)
      requires 2 <=Int lengthString(S)
  syntax LogEntry  ::=
    "logEntry" "(" Bytes "," Bytes "," ListBytes "," Bytes ")" [klabel(logEntry), symbol]
  syntax InternalInstr  ::=
    "#getArgsFromMemory" "(" Int "," Int "," Int ")" [klabel(#getArgsFromMemory)]
  | "#getArgsFromMemoryAux" "(" Int "," Int "," Int "," Int "," Int ")" [klabel(#getArgsFromMemoryAux)]
  rule <instrs> #getArgsFromMemory(NUMARGS, LENGTHOFFSET, DATAOFFSET)
               => #getArgsFromMemoryAux(NUMARGS, 0, NUMARGS, LENGTHOFFSET, DATAOFFSET)
                  ...
         </instrs>
      requires 0 <=Int #signed(i32, NUMARGS)
  rule <instrs> #getArgsFromMemory(NUMARGS, _, _)
               => #throwException(ExecutionFailed, "negative numArguments") ...
         </instrs>
      requires #signed(i32, NUMARGS) <Int 0
  rule <instrs> #getArgsFromMemoryAux(NUMARGS, TOTALLEN, 0,  _, _)
               => i32.const TOTALLEN
               ~> i32.const NUMARGS
                  ...
         </instrs>
  rule <instrs> #getArgsFromMemoryAux(NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
               => #memLoad(LENGTHOFFSET, 4)
               ~> #loadArgDataWithLengthOnStack(NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
                  ...
         </instrs>
       requires 0 <Int COUNTER
  syntax InternalInstr  ::=
    "#loadArgDataWithLengthOnStack" "(" Int "," Int "," Int "," Int "," Int ")" [klabel(#loadArgDataWithLengthOnStack)]
  | "#loadArgData" "(" Int "," Int "," Int "," Int "," Int "," Int ")" [klabel(#loadArgData)]
  rule <instrs> #loadArgDataWithLengthOnStack(NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
               => #loadArgData(Bytes2Int(ARGLEN, LE, Unsigned), NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
                  ...
         </instrs>
         <bytesStack> ARGLEN : STACK => STACK </bytesStack>
  rule <instrs> #loadArgData(ARGLEN, NUMARGS, TOTALLEN, COUNTER, LENGTHOFFSET, DATAOFFSET)
               => #memLoad(DATAOFFSET, ARGLEN)
               ~> #getArgsFromMemoryAux(NUMARGS, TOTALLEN +Int ARGLEN, COUNTER -Int 1, LENGTHOFFSET +Int 4, DATAOFFSET +Int ARGLEN)
                  ...
         </instrs>
  syntax InternalInstr  ::=
    "#writeLog"
  | "#writeLogAux" "(" Int "," ListBytes "," Bytes ")" [klabel(#writeLogAux)]
  rule <instrs> #writeLog => #writeLogAux(NUMTOPICS, .ListBytes, DATA) ... </instrs>
         <bytesStack> DATA : STACK => STACK </bytesStack>
         <valstack> <i32> NUMTOPICS : <i32> _ : VALSTACK => VALSTACK </valstack>
  rule <instrs> #writeLogAux(1, TOPICS, DATA) => . ... </instrs>
         <bytesStack> IDENTIFIER : STACK => STACK </bytesStack>
         <callee> CALLEE </callee>
         <logs> ... (.List => ListItem(logEntry(CALLEE, IDENTIFIER, TOPICS, DATA))) </logs>
  rule <instrs> #writeLogAux(NUMTOPICS, TOPICS, DATA)
               => #writeLogAux(NUMTOPICS -Int 1, ListItem(wrap(TOPIC)) TOPICS, DATA)
                  ...
         </instrs>
         <bytesStack> TOPIC : STACK => STACK </bytesStack>
       requires 1 <Int NUMTOPICS
  syntax InternalCmd  ::=
    "#endWasm"
  rule <commands> #endWasm => popCallState ~> dropWorldState ... </commands>
         <instrs> . </instrs>
         <out> OUT </out>
         <logs> LOGS </logs>
         <vmOutput> _ => VMOutput( OK , .Bytes , OUT , LOGS) </vmOutput>
       [priority(60)]
  syntax InternalCmd  ::=
    "#waitWasm"
  rule <commands> #waitWasm => . ... </commands>
         <instrs> . </instrs>
       [priority(60)]
  rule [exception-revert]: <commands> (#exception(EC, MSG) ~> #endWasm) => popCallState ~> popWorldState ... </commands>
        <vmOutput> .VMOutput => VMOutput( EC , MSG , .ListBytes , .List) </vmOutput>
  rule [exception-skip]: <commands> #exception(_,_) ~> (CMD:InternalCmd => . ) ... </commands>
      requires CMD =/=K #endWasm
  syntax InternalInstr  ::=
    "#throwException" "(" ExceptionCode "," String ")" [klabel(#throwException)]
  | "#throwExceptionBs" "(" ExceptionCode "," Bytes ")" [klabel(#throwExceptionBs)]
  rule [throwException]: <instrs> #throwException( EC , MSG )
              => #throwExceptionBs( EC , String2Bytes(MSG) ) ...
        </instrs>
  rule [throwExceptionBs]: <instrs> (#throwExceptionBs( EC , MSG ) ~> _ ) => . </instrs>
        <commands> (. => #exception(EC,MSG)) ... </commands>
  syntax Bool  ::=
    "#isSmartContract" "(" Bytes ")" [function, klabel(#isSmartContract), total]
  rule [[ #isSmartContract(ADDR) => true ]]
        <account>
          <address> ADDR </address>
          <code> _:ModuleDecl </code>
          ...
        </account>
  rule #isSmartContract(_) => false               [owise]
  syntax InternalCmd  ::=
    "createAccount" "(" Bytes ")" [klabel(createAccount), symbol]
  rule <commands> createAccount(ADDR) => . ... </commands>
         <account>
           <address> ADDR </address>
           ...
         </account>
         <logging> S => S +String " -- initAccount duplicate " +String Bytes2String(ADDR) </logging>
       [priority(60)]
  rule <commands> createAccount(ADDR) => . ... </commands>
         <accounts>
           ( .Bag
          => <account>
               <address> ADDR </address>
               ...
             </account>
           )
           ...
         </accounts>
         <logging> S => S +String " -- initAccount new " +String Bytes2String(ADDR) </logging>
       [priority(61)]
  syntax InternalCmd  ::=
    "setAccountFields" "(" Bytes "," Int "," Int "," Code "," Bytes "," MapBytesToBytes ")" [klabel(setAccountFields)]
  | "setAccountCode" "(" Bytes "," Code ")" [klabel(setAccountCode)]
  | "setAccountOwner" "(" Bytes "," Bytes ")" [klabel(setAccountOwner)]
  rule <commands> setAccountFields(ADDR, NONCE, BALANCE, CODE, OWNER_ADDR, STORAGE) => . ... </commands>
         <account>
           <address> ADDR </address>
           <nonce> _ => NONCE </nonce>
           <balance> _ => BALANCE </balance>
           <code> _ => CODE </code>
           <ownerAddress> _ => OWNER_ADDR </ownerAddress>
           <storage> _ => STORAGE </storage>
           ...
         </account>
       [priority(60)]
  rule <commands> setAccountCode(ADDR, CODE) => . ... </commands>
         <account>
           <address> ADDR </address>
           <code> _ => CODE </code>
           ...
         </account>
       [priority(60)]
  rule <commands> setAccountOwner(ADDR, OWNER) => . ... </commands>
         <account>
           <address> ADDR </address>
           <ownerAddress> _ => OWNER </ownerAddress>
           ...
         </account>
       [priority(60)]
  syntax InternalCmd  ::=
    "transferFunds" "(" Bytes "," Bytes "," Int ")" [klabel(transferFunds)]
  | "transferFundsH" "(" Bytes "," Bytes "," Int ")" [klabel(transferFundsH)]
  rule <commands> transferFunds(A, B, V)
                 => checkAccountExists(A)
                 ~> checkAccountExists(B)
                 ~> transferFundsH(A, B, V)
                    ...
         </commands>
       [priority(60)]
  rule [transferFundsH-self]: <commands> transferFundsH(ACCT, ACCT, VALUE) => #transferSuccess ... </commands>
        <account>
          <address> ACCT </address>
          <balance> ORIGFROM </balance>
          ...
        </account>
      requires VALUE <=Int ORIGFROM
       [priority(60)]
  rule [transferFundsH]: <commands> transferFundsH(ACCTFROM, ACCTTO, VALUE) => #transferSuccess ... </commands>
        <account>
          <address> ACCTFROM </address>
          <balance> ORIGFROM => ORIGFROM -Int VALUE </balance>
          ...
        </account>
        <account>
          <address> ACCTTO </address>
          <balance> ORIGTO => ORIGTO +Int VALUE </balance>
          ...
        </account>
      requires ACCTFROM =/=K ACCTTO andBool VALUE <=Int ORIGFROM
       [priority(60)]
  rule [transferFundsH-oofunds]: <commands> transferFundsH(ACCT, _, VALUE) => #exception(OutOfFunds, b"") ... </commands>
        <account>
          <address> ACCT </address>
          <balance> ORIGFROM </balance>
          ...
        </account>
      requires VALUE >Int ORIGFROM
       [priority(60)]
  rule <commands> #transferSuccess => . ... </commands>
         <instrs> . </instrs>
  syntax InternalCmd  ::=
    "callContract" "(" Bytes "," String "," VmInputCell ")" [klabel(callContractString)]
  | "callContract" "(" Bytes "," WasmString "," VmInputCell ")" [klabel(callContractWasmString)]
  | "mkCall" "(" Bytes "," WasmString "," VmInputCell ")" [klabel(mkCall)]
  rule <commands> callContract(TO, FUNCNAME:String, VMINPUT)
                 => callContract(TO, #unparseWasmString("\"" +String FUNCNAME +String "\""), VMINPUT) ...
         </commands>
       [priority(60)]
  rule [callContract]: <commands> callContract(TO, FUNCNAME:WasmStringToken,
                                <vmInput>
                                  <caller> FROM </caller>
                                  <callValue> VALUE </callValue>
                                  <esdtTransfers> ESDT </esdtTransfers>
                                  _
                                </vmInput> #as VMINPUT
                   )
                => pushWorldState
                ~> pushCallState
                ~> transferFunds(FROM, TO, VALUE)
                ~> transferESDTs(FROM, TO, ESDT)
                ~> newWasmInstance(CODE)
                ~> mkCall(TO, FUNCNAME, VMINPUT)
                ~> #endWasm
                   ...
        </commands>
        <account>
          <address> TO </address>
          <code> CODE </code>
          ...
        </account>
        <vmOutput> _ => .VMOutput </vmOutput>
        <logging> S => S +String " -- callContract " +String #parseWasmString(FUNCNAME) </logging>
       [priority(60)]
  rule [callContract-not-contract]: <commands> callContract(TO, _:WasmString, _)
                => #exception(ContractNotFound, b"not a contract: " +Bytes TO) ...
        </commands>
        <account>
          <address> TO </address>
          <code> .Code </code>
          ...
        </account>
       [priority(60)]
  rule [callContract-not-found]: <commands> callContract(TO, _:WasmString, _)
                => #exception(ExecutionFailed, b"account not found: " +Bytes TO) ...
        </commands>
       [priority(61)]
  syntax WasmCell
  syntax InternalCmd  ::=
    "newWasmInstance" "(" ModuleDecl ")" [klabel(newWasmInstance)]
  | "setContractModIdx"
  rule [newWasmInstance]: <commands> newWasmInstance(CODE) => #waitWasm ~> setContractModIdx ...</commands>
        ( _:WasmCell => <wasm>
          <instrs> initContractModule(CODE) </instrs>
          ...
        </wasm>)
  rule [setContractModIdx]: <commands> setContractModIdx => . ... </commands>
        <contractModIdx> _ => NEXTIDX -Int 1 </contractModIdx>
        <nextModuleIdx> NEXTIDX </nextModuleIdx>
  syntax K  ::=
    "initContractModule" "(" ModuleDecl ")" [function, klabel(initContractModule)]
  rule initContractModule((module _:OptionalId _:Defns):ModuleDecl #as M)
      => sequenceStmts(text2abstract(M .Stmts))
  rule initContractModule(M:ModuleDecl) => M               [owise]
  rule [mkCall]: <commands> mkCall(TO, FUNCNAME:WasmStringToken, VMINPUT) => . ... </commands>
        <callState>
          <callee> _ => TO   </callee>
          (_:VmInputCell => VMINPUT)
          // executional
          <wasm>
            <instrs> . => ( invoke FUNCADDR ) </instrs>
            <moduleInst>
              <modIdx> MODIDX </modIdx>
              <exports> ... FUNCNAME |-> FUNCIDX:Int </exports>
              <funcAddrs> ... FUNCIDX |-> FUNCADDR:Int ... </funcAddrs>
              ...
            </moduleInst>
            ...
          </wasm>
          <bigIntHeap> _ => .Map </bigIntHeap>
          <bufferHeap> _ => .MapIntToBytes </bufferHeap>
          <bytesStack> _ => .BytesStack </bytesStack>
          <contractModIdx> MODIDX:Int </contractModIdx>
          // output
          <out> _ => .ListBytes </out>
          <logs> _ => .List </logs>
        </callState>
       [priority(60)]
  rule [mkCall-func-not-found]: <commands> mkCall(_TO, FUNCNAME:WasmStringToken, _VMINPUT) => . ... </commands>
        <contractModIdx> MODIDX:Int </contractModIdx>
        <moduleInst>
          <modIdx> MODIDX </modIdx>
          <exports> EXPORTS </exports>
          ...
        </moduleInst>
        <instrs> . => #throwException(FunctionNotFound, "invalid function (not found)") </instrs>
        <logging> S => S +String " -- callContract not found " +String #parseWasmString(FUNCNAME) </logging>
      requires notBool( FUNCNAME in_keys(EXPORTS) )
       [priority(60)]
endmodule

module EEI-HELPERS
  imports public BOOL
  imports public INT
  imports public BYTES
  imports public STRING
  syntax Int  ::=
    "#tickerMinLen" [macro]
  | "#tickerMaxLen" [macro]
  | "#randomCharsLen" [macro]
  | "#idMinLen" [macro]
  | "#idMaxLen" [macro]
  rule #tickerMinLen    => 3
  rule #tickerMaxLen    => 10
  rule #randomCharsLen  => 6
  rule #idMinLen        => #tickerMinLen +Int #randomCharsLen +Int 1
  rule #idMaxLen        => #tickerMaxLen +Int #randomCharsLen +Int 1
  syntax Bool  ::=
    "#validateToken" "(" Bytes ")" [function, klabel(#validateToken), total]
  rule #validateToken(Bs) => false requires lengthBytes(Bs) <Int #idMinLen
                                     orBool lengthBytes(Bs) >Int #idMaxLen
  rule #validateToken(Bs) => #isTickerValid( #getTicker(Bs) )
                     andBool #randomCharsAreValid( #getRandomChars(Bs) )
                     andBool Bs[(lengthBytes(Bs) -Int #randomCharsLen) -Int 1 ] ==Int ordChar("-")
                              requires lengthBytes(Bs) >=Int #idMinLen
                               andBool lengthBytes(Bs) <=Int #idMaxLen
  syntax Bytes  ::=
    "#getTicker" "(" Bytes ")" [function, klabel(#getTicker), total]
  | "#getRandomChars" "(" Bytes ")" [function, klabel(#getRandomChars), total]
  rule #getTicker(Bs) => substrBytes(Bs, 0, lengthBytes(Bs) -Int #randomCharsLen -Int 1)
    requires lengthBytes(Bs) >Int #randomCharsLen
  rule #getRandomChars(Bs) => substrBytes(Bs, lengthBytes(Bs) -Int #randomCharsLen, lengthBytes(Bs))
    requires lengthBytes(Bs) >=Int #randomCharsLen
  rule #getTicker(Bs) => .Bytes
    requires lengthBytes(Bs) <=Int #randomCharsLen
  rule #getRandomChars(Bs) => .Bytes
    requires lengthBytes(Bs) <Int #randomCharsLen
  syntax Bool  ::=
    "#isTickerValid" "(" Bytes ")" [function, klabel(#isTickerValid), total]
  rule #isTickerValid(Ticker) => false
    requires lengthBytes(Ticker) <Int #tickerMinLen
      orBool lengthBytes(Ticker) >Int #tickerMaxLen
  rule #isTickerValid(Ticker) => #allReadable(Ticker, 0)
    requires lengthBytes(Ticker) >=Int #tickerMinLen
      orBool lengthBytes(Ticker) <=Int #tickerMaxLen
  syntax Bool  ::=
    "#allReadable" "(" Bytes "," Int ")" [function, klabel(#allReadable), total]
  | "#readableChar" "(" Int ")" [function, klabel(#readableChar), total]
  rule #allReadable(Bs, Ix) => #readableChar(Bs[Ix]) andBool #allReadable(Bs, Ix +Int 1)
                                            requires Ix <Int lengthBytes(Bs) andBool Ix >=Int 0
  rule #allReadable(Bs, Ix) => true         requires Ix >=Int lengthBytes(Bs)
  rule #allReadable(_Bs, Ix => 0)           requires Ix <Int 0
  rule #readableChar(X) => ( X >=Int ordChar("A") andBool X <=Int ordChar("Z") )
                    orBool ( X >=Int ordChar("0") andBool X <=Int ordChar("9") )
  syntax Bool  ::=
    "#randomCharsAreValid" "(" Bytes ")" [function, klabel(#randomCharsAreValid), total]
  rule #randomCharsAreValid(Bs) => false                      requires lengthBytes(Bs) =/=Int #randomCharsLen
  rule #randomCharsAreValid(Bs) => #allValidRandom(Bs, 0)     requires lengthBytes(Bs) ==Int #randomCharsLen
  syntax Bool  ::=
    "#allValidRandom" "(" Bytes "," Int ")" [function, klabel(#allValidRandom), total]
  | "#validRandom" "(" Int ")" [function, klabel(#validRandom), total]
  rule #allValidRandom(Bs, Ix) => #validRandom(Bs[Ix]) andBool #allValidRandom(Bs, Ix +Int 1)
                                               requires Ix <Int lengthBytes(Bs) andBool Ix >=Int 0
  rule #allValidRandom(Bs, Ix) => true         requires Ix >=Int lengthBytes(Bs)
  rule #allValidRandom(_Bs, Ix => 0)           requires Ix <Int 0
  rule #validRandom(X) => ( X >=Int ordChar("a") andBool X <=Int ordChar("f") )
                   orBool ( X >=Int ordChar("0") andBool X <=Int ordChar("9") )
endmodule

module UTILS
  imports public STRING
  imports public INT
  imports public LIST
  imports public LIST-BYTES
  imports public BYTES-TYPE
  imports public UTILS-CEILS
  syntax Error  ::=
    "Err" "(" String ")" [klabel(Err)]
  syntax ListBytesResult  ::=
    ListBytes
  | Error
  syntax ListResult  ::=
    List
  | Error
  syntax BytesResult  ::=
    Bytes
  | Error
  syntax IntResult  ::=
    Int
  | Error
  syntax ListResult  ::=
    "catListResult" "(" ListResult "," ListResult ")" [function, klabel(catListResult), total]
  rule catListResult(ERR:Error, _)      => ERR
  rule catListResult(_:List, ERR:Error) => ERR
  rule catListResult(A:List, B:List)    => A B
  syntax ListBytesResult  ::=
    "catListBytesResult" "(" ListBytesResult "," ListBytesResult ")" [function, klabel(catListBytesResult), total]
  rule catListBytesResult(ERR:Error, _)             => ERR
  rule catListBytesResult(_:ListBytes, ERR:Error)   => ERR
  rule catListBytesResult(A:ListBytes, B:ListBytes) => A B
  syntax ListBytesResult  ::=
    "BytesResult2ListResult" "(" BytesResult ")" [function, klabel(BytesResult2ListResult), total]
  rule BytesResult2ListResult(BS:Bytes) => ListItem(wrap(BS))
  rule BytesResult2ListResult(Err(E))   => Err(E)
  syntax ListResult  ::=
    "IntResult2ListResult" "(" IntResult ")" [function, klabel(IntResult2ListResult), total]
  rule IntResult2ListResult(BS:Int) => ListItem(BS)
  rule IntResult2ListResult(Err(E)) => Err(E)
endmodule

module UTILS-CEILS
  imports public BOOL
  imports public LIST-BYTES
  imports public INT
  imports public LIST
  imports public WASM-DATA
  syntax Bool  ::=
    "definedListLookup" "(" List "," index: Int ")" [function, klabel(definedListLookup), total]
  rule definedListLookup (L:List, Idx:Int)
        => (Idx >=Int 0 -Int size(L)) andBool (Idx <Int size(L))
  rule #Ceil(@Arg0:List[@Index:Int])
        =>  ( ( {true #Equals definedListLookup(@Arg0, @Index)} // TODO: This is wrong, use #Ceil(true #And definedListLookup(@Arg0, @Index))
              #And #Ceil(@Arg0)
              )
            #And #Ceil(@Index)
            )
         [simplification]
  syntax KItem  ::=
    List "{{" Int "}}" [function, klabel(listLookupTotal), no-evaluators, symbol, total]
  rule L:List{{Index:Int}}
        => L[Index]
        requires definedListLookup(L, Index)
         [concrete, simplification]
  rule L:List{{Index:Int}} => 0
        requires notBool definedListLookup(L, Index)
         [simplification]
  rule L:List[Index:Int]
        => L{{Index}}
        requires definedListLookup(L, Index)
         [simplification, symbolic(L)]
  rule L:List[Index:Int]
        => L{{Index}}
        requires definedListLookup(L, Index)
         [simplification, symbolic(Index)]
  syntax Bool  ::=
    "definedBytesListLookup" "(" ListBytes "," index: Int ")" [function, klabel(definedBytesListLookup), total]
  rule definedBytesListLookup (L:ListBytes, Idx:Int)
        => (Idx >=Int 0 -Int size(L)) andBool (Idx <Int size(L))
  rule #Ceil(@Arg0:ListBytes[@Index:Int])
        =>  ( ( {true #Equals definedBytesListLookup(@Arg0, @Index)} // TODO: This is wrong, use #Ceil(true #And definedBytesListLookup(@Arg0, @Index))
              #And #Ceil(@Arg0)
              )
            #And #Ceil(@Index)
            )
         [simplification]
  syntax Bool  ::=
    "definedSigned" "(" IValType "," Int ")" [function, klabel(definedSigned), total]
  rule definedSigned(T:IValType, N:Int) => 0 <=Int N andBool N <Int #pow(T)
  rule #Ceil(#signed(@Arg0:IValType, @Arg1:Int))
        =>  (({ definedSigned(@Arg0, @Arg1)  #Equals true }
          #And #Ceil(@Arg0))
          #And #Ceil(@Arg1))
         [simplification]
  syntax Int  ::=
    "#signedTotal" "(" IValType "," Int ")" [function, klabel(#signedTotal), no-evaluators, smtlib(signedTotal), symbol, total]
  rule #signedTotal(Arg0:IValType, Arg1:Int)
        => #signed(Arg0, Arg1)
        requires definedSigned(Arg0, Arg1)
         [concrete, simplification]
  rule #signed(Arg0:IValType, Arg1:Int)
        => #signedTotal(Arg0, Arg1)
        requires definedSigned(Arg0, Arg1)
         [simplification, symbolic(Arg0)]
  rule #signed(Arg0:IValType, Arg1:Int)
        => #signedTotal(Arg0, Arg1)
        requires definedSigned(Arg0, Arg1)
         [simplification, symbolic(Arg1)]
endmodule

module BASEOPS
  imports public ELROND-CONFIG
  imports public EEI-HELPERS
  imports public UTILS
  imports private LIST-BYTES-EXTENSIONS
  rule <instrs> hostCall("env", "getSCAddress", [ i32  .ValTypes ] -> [ .ValTypes ])
               => #memStore(RESULTOFFSET, CALLEE)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> RESULTOFFSET
         </locals>
         <callee> CALLEE </callee>
  rule <instrs> hostCall("env", "isSmartContract", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(ADDROFFSET, 32)
               ~> #checkIsSmartContract
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDROFFSET
         </locals>
  syntax InternalInstr  ::=
    "#checkIsSmartContract"
  rule <instrs> #checkIsSmartContract => i32.const 1 ... </instrs>
         <bytesStack> ADDR : STACK => STACK </bytesStack>
         <account>
           <address> ADDR </address>
           <code> _:ModuleDecl </code>
           ...
         </account>
  rule <instrs> #checkIsSmartContract => i32.const 0 ... </instrs>
         <bytesStack> ADDR : STACK => STACK </bytesStack>
         <account>
           <address> ADDR </address>
           <code> .Code </code>
           ...
         </account>
  rule <instrs> hostCall("env", "getExternalBalance", [ i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(ADDROFFSET, 32)
               ~> #getExternalBalance
               ~> #memStoreFromBytesStack(RESULTOFFSET)
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDROFFSET
           1 |-> <i32> RESULTOFFSET
         </locals>
  syntax InternalInstr  ::=
    "#getExternalBalance"
  rule <instrs> #getExternalBalance => . ... </instrs>
         <bytesStack> ADDR : STACK => Int2Bytes(BAL, BE, Unsigned) : STACK </bytesStack>
         <account>
           <address> ADDR </address>
           <balance> BAL </balance>
           ...
         </account>
  rule <instrs> #getExternalBalance => . ... </instrs>
         <bytesStack> _ADDR : STACK => Int2Bytes(0, BE, Unsigned) : STACK </bytesStack>
       [priority(201)]
  rule <instrs> hostCall("env", "transferValue", [ i32 i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(DSTOFFSET, 32)
               ~> #memLoad(VALUEOFFSET, 32)
               ~> #memLoad(DATAOFFSET, LENGTH)
               ~> #transferValue
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DSTOFFSET
           1 |-> <i32> VALUEOFFSET
           2 |-> <i32> DATAOFFSET
           3 |-> <i32> LENGTH
         </locals>
  syntax InternalInstr  ::=
    "#transferValue"
  | "#waitForTransfer"
  rule <commands> (. => transferFunds(CALLEE, DEST, Bytes2Int(VALUE, BE, Unsigned))) ... </commands>
         <instrs> #transferValue => #waitForTransfer ~> i32.const 0 ... </instrs>
         <callee> CALLEE </callee>
         <bytesStack> _DATA : VALUE : DEST : STACK => STACK </bytesStack>
  rule <commands> (#transferSuccess => .) ~> #endWasm ... </commands>
         <instrs> #waitForTransfer => . ... </instrs>
  syntax Bool  ::=
    "#validArgIdx" "(" Int "," ListBytes ")" [function, klabel(#validArgIdx), total]
  rule #validArgIdx(IDX, ARGS)
        => 0 <=Int #signed(i32, IDX)
          andBool definedSigned(i32, IDX)
          andBool definedBytesListLookup(ARGS, IDX)
  rule <instrs> hostCall("env", "getArgumentLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => i32.const lengthBytes( ARGS {{ IDX }} ) ...
         </instrs>
         <locals> 0 |-> <i32> IDX:Int </locals>
         <callArgs> ARGS:ListBytes </callArgs>
      requires #validArgIdx(IDX, ARGS)
  rule <instrs> hostCall("env", "getArgumentLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #throwException(ExecutionFailed, "invalid argument") ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <callArgs> ARGS </callArgs>
      requires notBool #validArgIdx(IDX, ARGS)
  rule <instrs> hostCall("env", "getArgument", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memStore(OFFSET, ARGS {{ IDX }} )
               ~> i32.const lengthBytes( ARGS {{ IDX }} )
                  ...
         </instrs>
         <locals>
           0 |-> <i32> IDX
           1 |-> <i32> OFFSET
         </locals>
         <callArgs> ARGS </callArgs>
      requires #validArgIdx(IDX, ARGS)
  rule <instrs> hostCall("env", "getArgument", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #throwException(ExecutionFailed, "invalid argument") ...
         </instrs>
         <locals>
           0 |-> <i32> IDX
           1 |-> <i32> _OFFSET
         </locals>
         <callArgs> ARGS </callArgs>
      requires notBool #validArgIdx(IDX, ARGS)
  rule <instrs> hostCall("env", "getNumArguments", [ .ValTypes ] -> [ i32 .ValTypes ]) => i32.const size(ARGS) ... </instrs>
         <callArgs> ARGS </callArgs>
  rule <instrs> hostCall("env", "storageStore", [ i32 i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #memLoad(VALOFFSET, VALLENGTH)
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> VALOFFSET
           3 |-> <i32> VALLENGTH
         </locals>
  rule <instrs> hostCall("env", "storageLoadLength", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
         </locals>
  rule <instrs> hostCall("env", "storageLoad", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #memStoreFromBytesStack(VALOFFSET)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> VALOFFSET
         </locals>
  rule <instrs> hostCall("env", "getCaller", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #memStore(OFFSET, CALLER)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <caller> CALLER </caller>
  rule [checkNoPayment-pass]: <instrs> hostCall("env", "checkNoPayment", [ .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
        <callValue> VAL </callValue>
        <esdtTransfers> T:List </esdtTransfers>
      requires VAL <=Int 0 andBool size(T) ==K 0
  rule [checkNoPayment-fail-egld]: <instrs> hostCall("env", "checkNoPayment", [ .ValTypes ] -> [ .ValTypes ])
              => #throwException(ExecutionFailed, "function does not accept EGLD payment") ...
        </instrs>
        <callValue> VAL </callValue>
      requires 0 <Int VAL
  rule [checkNoPayment-fail-esdt]: <instrs> hostCall("env", "checkNoPayment", [ .ValTypes ] -> [ .ValTypes ])
              => #throwException(ExecutionFailed, "function does not accept ESDT payment") ...
        </instrs>
        <callValue> VAL </callValue>
        <esdtTransfers> T:List </esdtTransfers>
      requires VAL <=Int 0 andBool 0 <Int size(T)
  rule [getESDTTokenName]: <instrs> hostCall("env", "getESDTTokenName", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
              => #memStore(OFFSET, TOKENNAME)
              ~> i32.const lengthBytes(TOKENNAME)
                ...
        </instrs>
        <locals> 0 |-> <i32> OFFSET </locals>
        <esdtTransfers> ListItem( esdtTransfer( TOKENNAME , _VALUE , _NONCE ) ) </esdtTransfers>
  rule [getESDTTokenName-too-many]: <instrs> hostCall("env", "getESDTTokenName", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
              => #throwException(ExecutionFailed, "too many ESDT transfers")
                ...
        </instrs>
        <locals> 0 |-> <i32> _ </locals>
        <esdtTransfers> ESDTs </esdtTransfers>
      requires size(ESDTs) >Int 1
  rule [getESDTTokenName-none]: <instrs> hostCall("env", "getESDTTokenName", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
              => #throwException(ExecutionFailed, "invalid token index")
                ...
        </instrs>
        <locals> 0 |-> <i32> _ </locals>
        <esdtTransfers> .List </esdtTransfers>
  rule <instrs> hostCall ( "env" , "getNumESDTTransfers" , [ .ValTypes ] -> [ i32  .ValTypes ] )
               => i32.const size( TS )
                  ...
         </instrs>
         <esdtTransfers> TS </esdtTransfers>
  rule <instrs> hostCall("env", "writeEventLog", [ i32 i32 i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #getArgsFromMemory(NUMTOPICS, TOPICLENGTHOFFSET, TOPICOFFSET)
               ~> #memLoad(DATAOFFSET, DATALENGTH)
               ~> #writeLog
                  ...
         </instrs>
         <locals>
           0 |-> <i32> NUMTOPICS
           1 |-> <i32> TOPICLENGTHOFFSET
           2 |-> <i32> TOPICOFFSET
           3 |-> <i32> DATAOFFSET
           4 |-> <i32> DATALENGTH
         </locals>
  rule <instrs> hostCall("env", "finish", [ i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #returnData(OFFSET, LENGTH)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> OFFSET
           1 |-> <i32> LENGTH
         </locals>
  syntax InternalInstr  ::=
    "#returnData" "(" Int "," Int ")" [klabel(#returnData)]
  rule <instrs> #returnData(OFFSET, LENGTH)
               => #memLoad(OFFSET, LENGTH)
               ~> #appendToOutFromBytesStack
                  ...
         </instrs>
  rule <instrs> hostCall("env", "signalError", [ i32 i32 .ValTypes ] -> [ .ValTypes ] )
               => #memLoad(OFFSET, LENGTH)
               ~> #signalError
                  ...
         </instrs>
         <locals>
           0 |-> <i32> OFFSET
           1 |-> <i32> LENGTH
         </locals>
  syntax InternalInstr  ::=
    "#signalError"
  rule <instrs> #signalError => #throwExceptionBs(UserError, DATA) ... </instrs>
         <bytesStack> DATA : STACK => STACK </bytesStack>
  rule <instrs> hostCall("env", "getBlockTimestamp", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const TIMESTAMP ... </instrs>
         <curBlockTimestamp> TIMESTAMP </curBlockTimestamp>
  rule <instrs> hostCall("env", "getBlockNonce", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const NONCE ... </instrs>
         <curBlockNonce> NONCE </curBlockNonce>
  rule <instrs> hostCall("env", "getBlockRound", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const ROUND ... </instrs>
         <curBlockRound> ROUND </curBlockRound>
  rule <instrs> hostCall("env", "getBlockEpoch", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const EPOCH ... </instrs>
         <curBlockEpoch> EPOCH </curBlockEpoch>
  rule <instrs> hostCall("env", "getBlockRandomSeed", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #memStore(OFFSET, SEED)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <curBlockRandomSeed> SEED </curBlockRandomSeed>
  rule <instrs> hostCall("env", "getPrevBlockTimestamp", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const TIMESTAMP ... </instrs>
         <prevBlockTimestamp> TIMESTAMP </prevBlockTimestamp>
  rule <instrs> hostCall("env", "getPrevBlockNonce", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const NONCE ... </instrs>
         <prevBlockNonce> NONCE </prevBlockNonce>
  rule <instrs> hostCall("env", "getPrevBlockRound", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const ROUND ... </instrs>
         <prevBlockRound> ROUND </prevBlockRound>
  rule <instrs> hostCall("env", "getPrevBlockEpoch", [ .ValTypes ] -> [ i64 .ValTypes ]) => i64.const EPOCH ... </instrs>
         <prevBlockEpoch> EPOCH </prevBlockEpoch>
  rule <instrs> hostCall("env", "getPrevBlockRandomSeed", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #memStore(OFFSET, SEED)
                  ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET </locals>
         <prevBlockRandomSeed> SEED </prevBlockRandomSeed>
  rule <instrs> hostCall("env", "validateTokenIdentifier", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
              => i32 . const #bool( #validateToken(TokId) )
                 ...
        </instrs>
        <locals> 0 |-> <i32> ID_IDX </locals>
        <bufferHeap> ... wrap(ID_IDX) Int2Bytes|-> wrap(TokId) ... </bufferHeap>
  syntax InternalInstr  ::=
    "#transferESDTNFTExecuteWithTypedArgs" "(" BytesResult "," ListResult "," Int "," BytesResult "," ListBytesResult ")" [klabel(#transferESDTNFTExecuteWithTypedArgs)]
  rule <instrs> #transferESDTNFTExecuteWithTypedArgs(Dest, Transfers, _GasLimit, b"", _Args)
               => #waitForTransfer
               ~> i32.const 0
                  ...
         </instrs>
         <callee> Callee </callee>
         <commands> (. => transferESDTs(Callee, Dest, Transfers)) ... </commands>
  rule [transfer-esdt-and-execute]: <instrs> #transferESDTNFTExecuteWithTypedArgs(Dest, Transfers, GasLimit, Func, Args)
              => #executeOnDestContext(Dest, 0, Transfers, GasLimit, Func, Args)
                 ...
        </instrs>
      requires 0 <Int lengthBytes(Func)
  syntax InternalInstr  ::=
    "#transferValueExecuteWithTypedArgs" "(" BytesResult "," IntResult "," Int "," BytesResult "," ListBytesResult ")" [klabel(#transferValueExecuteWithTypedArgs)]
  rule <instrs> #transferValueExecuteWithTypedArgs(Dest, Value, _GasLimit, b"", _Args)
               => #waitForTransfer
               ~> i32.const 0
                  ...
         </instrs>
         <callee> Callee </callee>
         <commands> (. => transferFunds(Callee, Dest, Value)) ... </commands>
  rule [transfer-and-execute]: <instrs> #transferValueExecuteWithTypedArgs(Dest, Value, GasLimit, Func, Args)
              => #executeOnDestContext(Dest, Value, .List, GasLimit, Func, Args)
                 ...
        </instrs>
      requires 0 <Int lengthBytes(Func)
  syntax InternalInstr  ::=
    "#executeOnDestContext" "(" Bytes "," Int "," List "," Int "," Bytes "," ListBytes ")" [klabel(#executeOnDestContext)]
  rule [executeOnDestContext]: <instrs> #executeOnDestContext(Dest, Value, Esdt, GasLimit, Func, Args)
              => #finishExecuteOnDestContext
                 ...
        </instrs>
        <callee> Callee </callee>
        <commands>
          (. => callContract( Dest, Bytes2String(Func), prepareIndirectContractCallInput(Callee, Value, Esdt, GasLimit, Args))) ...
        </commands>
  syntax VmInputCell  ::=
    "prepareIndirectContractCallInput" "(" Bytes "," Int "," List "," Int "," ListBytes ")" [function, klabel(prepareIndirectContractCallInput), total]
  rule prepareIndirectContractCallInput(SENDER, VALUE, ESDT, GASLIMIT, ARGS)
      => <vmInput>
            <caller> SENDER </caller>
            <callArgs> ARGS </callArgs>
            <callValue> VALUE </callValue>
            <esdtTransfers> ESDT </esdtTransfers>
            // gas
            <gasProvided> GASLIMIT </gasProvided>
            <gasPrice> 0 </gasPrice>
          </vmInput>
  syntax InternalInstr  ::=
    "#finishExecuteOnDestContext"
  rule [finishExecuteOnDestContext-ok]: <commands> #endWasm ... </commands>
        <instrs> #finishExecuteOnDestContext
              => i32.const 0
                 ...
        </instrs>
        <vmOutput>
          VMOutput ( OK , _ , OUTPUT , LOGS ) => .VMOutput
        </vmOutput>
        // merge outputs
        <out> ... (.ListBytes => OUTPUT) </out>
        <logs> ... (.List => LOGS) </logs>
  rule [finishExecuteOnDestContext-exception]: <commands> #endWasm ... </commands>
        <instrs> #finishExecuteOnDestContext
              => resolveErrorFromOutput(EC, MSG)
                 ...
        </instrs>
        <vmOutput>
          VMOutput ( EC:ExceptionCode , MSG , _ , _ ) => .VMOutput
        </vmOutput>
  rule <commands> (#transferSuccess => .) ... </commands>
         <instrs> #finishExecuteOnDestContext ... </instrs>
  syntax InternalInstr  ::=
    "resolveErrorFromOutput" "(" ExceptionCode "," Bytes ")" [function, klabel(resolveErrorFromOutput), total]
  rule resolveErrorFromOutput(ExecutionFailed, b"memory limit reached")
        => #throwExceptionBs(ExecutionFailed, b"execution failed")
  rule resolveErrorFromOutput(FunctionNotFound, MSG)
        => #throwExceptionBs(ExecutionFailed, MSG)
  rule resolveErrorFromOutput(UserError, _)
        => #throwExceptionBs(ExecutionFailed, b"error signalled by smartcontract")
  rule resolveErrorFromOutput(OutOfFunds, _)
        => #throwExceptionBs(ExecutionFailed, b"failed transfer (insufficient funds)")
  rule resolveErrorFromOutput(EC, MSG)
        => #throwExceptionBs(EC, MSG)
         [owise]
  rule <instrs> hostCall("env", "asyncCall", [ DOM ] -> [ CODOM ]) => . ... </instrs>
         <valstack> VS => #zero(CODOM) ++ #drop(lengthValTypes(DOM), VS) </valstack>
endmodule

module BIGINT-HELPERS
  imports public ELROND-CONFIG
  imports public BASEOPS
  imports public MAP-INT-TO-BYTES-PRIMITIVE
  imports public LIST-BYTES-EXTENSIONS
  syntax IntResult  ::=
    "getBigInt" "(" Int ")" [function, klabel(getBigInt), total]
  rule [[ getBigInt(IDX) => I ]]
      <bigIntHeap> ... IDX |-> I:Int ... </bigIntHeap>
  rule getBigInt(_) => Err("no bigInt under the given handle")  [owise]
  syntax InternalInstr  ::=
    "#getBigInt" "(" idx: Int "," Signedness ")" [klabel(#getBigInt)]
  rule <instrs> #getBigInt(BIGINT_IDX, SIGN) => . ... </instrs>
         <bytesStack> STACK => Int2Bytes({HEAP[BIGINT_IDX]}:>Int, BE, SIGN) : STACK </bytesStack>
         <bigIntHeap> HEAP </bigIntHeap>
      requires #validIntId(BIGINT_IDX, HEAP)
  rule <instrs> #getBigInt(BIGINT_IDX, _SIGN) => #throwException(ExecutionFailed, "no bigInt under the given handle") ... </instrs>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool #validIntId(BIGINT_IDX, HEAP)
  syntax InternalInstr  ::=
    "#getBigIntOrCreate" "(" idx: Int "," Signedness ")" [klabel(#getBigIntOrCreate)]
  rule [getBigIntOrCreate-get]: <instrs> #getBigIntOrCreate(BIGINT_IDX, SIGN) => . ... </instrs>
        <bytesStack> STACK => Int2Bytes({HEAP[BIGINT_IDX]}:>Int, BE, SIGN) : STACK </bytesStack>
        <bigIntHeap> HEAP </bigIntHeap>
      requires #validIntId(BIGINT_IDX, HEAP)
  rule [getBigIntOrCreate-create]: <instrs> #getBigIntOrCreate(BIGINT_IDX, SIGN) => #setBigIntValue(BIGINT_IDX, 0) ... </instrs>
        <bytesStack> STACK => Int2Bytes(0, BE, SIGN) : STACK </bytesStack>
        <bigIntHeap> HEAP </bigIntHeap>
      requires notBool #validIntId(BIGINT_IDX, HEAP)
  syntax InternalInstr  ::=
    "#setBigIntFromBytesStack" "(" idx: Int "," Signedness ")" [klabel(#setBigIntFromBytesStack)]
  | "#setBigInt" "(" idx: Int "," value: Bytes "," Signedness ")" [klabel(#setBigInt)]
  | "#setBigIntValue" "(" Int "," Int ")" [klabel(#setBigIntValue)]
  rule <instrs> #setBigIntFromBytesStack(BIGINT_IDX, SIGN) => #setBigInt(BIGINT_IDX, BS, SIGN) ... </instrs>
         <bytesStack> BS : _ </bytesStack>
  rule <instrs> #setBigInt(BIGINT_IDX, BS, SIGN) => . ... </instrs>
         <bigIntHeap> HEAP => HEAP [BIGINT_IDX <- Bytes2Int(BS, BE, SIGN)] </bigIntHeap>
  rule <instrs> #setBigIntValue(BIGINT_IDX, VALUE) => . ... </instrs>
         <bigIntHeap> HEAP => HEAP [BIGINT_IDX <- VALUE] </bigIntHeap>
  syntax Bool  ::=
    "#validIntId" "(" Int "," Map ")" [function, klabel(#validIntId), total]
  rule #validIntId( IDX , HEAP ) => IDX in_keys(HEAP) andBool isInt(HEAP[IDX] orDefault 0)
  syntax Int  ::=
    "#newKey" "(" Map ")" [function, klabel(#newKey), total]
  | "#newKeyAux" "(" Int "," Map ")" [function, klabel(#newKeyAux), total]
  | "#newKey" "(" MapIntToBytes ")" [function, klabel(#newKey), total]
  | "#newKeyAux" "(" Int "," MapIntToBytes ")" [function, klabel(#newKeyAux), total]
  rule #newKey(M:Map)       => #newKeyAux(size(M), M)
  rule #newKeyAux(I, M:Map) => I                        requires notBool(I in_keys(M))
  rule #newKeyAux(I, M:Map) => #newKeyAux(I +Int 1, M)  requires         I in_keys(M)
  rule #newKey(M:MapIntToBytes)       => #newKeyAux(size(M), M)
  rule #newKeyAux(I, M:MapIntToBytes) => I                        requires notBool(I in_keys{{M}})
  rule #newKeyAux(I, M:MapIntToBytes) => #newKeyAux(I +Int 1, M)  requires         I in_keys{{M}}
  syntax Int  ::=
    "sqrtInt" "(" Int ")" [function, klabel(sqrtInt), total]
  rule sqrtInt(X) => -1                           requires X <Int 0
  rule sqrtInt(0) => 0
  rule sqrtInt(X) => #let P = 2 ^Int (log2Int(X) /Int 2) // the largest power of 2 less than or eq. to X
                       #in sqrtBS(X, P, P *Int 2)   requires X >Int 0
  syntax Int  ::=
    "sqrtBS" "(" Int "," Int "," Int ")" [function, klabel(sqrtBS)]
  rule sqrtBS(_, L, R) => L                                      requires L ==Int R
  rule sqrtBS(X, L, R) => sqrtBS(X, L, bsMid(L,R) -Int 1)        requires L <Int R
                                                                    andBool squareInt(bsMid(L,R)) >Int X
  rule sqrtBS(X, L, R) => sqrtBS(X, bsMid(L,R), R)               requires L <Int R
                                                                    andBool squareInt(bsMid(L,R)) <=Int X
  rule #Ceil(sqrtBS(@X:Int, @L:Int, @R:Int)) => #Ceil(@X) #And #Ceil(@L) #And #Ceil(@R)
                                             #And {(@L <=Int @R) #Equals true}    [simplification]
  syntax Int  ::=
    "bsMid" "(" Int "," Int ")" [function, klabel(bsMid), total]
  rule bsMid(X,Y) => (X +Int Y +Int 1) /Int 2
  syntax Int  ::=
    "squareInt" "(" Int ")" [function, klabel(squareInt), total]
  rule squareInt(I) => I *Int I
endmodule

module BIGINTOPS
  imports public BIGINT-HELPERS
  rule <instrs> hostCall("env", "bigIntNew", [ i64 .ValTypes ] -> [ i32 .ValTypes ])
               => i32.const #newKey(HEAP)
                  ...
         </instrs>
         <locals> 0 |-> <i64> INITIAL </locals>
         <bigIntHeap> HEAP => HEAP[#newKey(HEAP) <- #signed(i64, INITIAL)] </bigIntHeap>
  rule <instrs> hostCall("env", "bigIntUnsignedByteLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #getBigInt(IDX, Unsigned)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
  rule <instrs> hostCall("env", "bigIntSignedByteLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #getBigInt(IDX, Unsigned)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
  rule [bigIntGetInt64]: <instrs> hostCall ("env", "bigIntGetInt64", [i32 .ValTypes ] -> [i64  .ValTypes ] )
              => i64 . const V
                 ...
        </instrs>
        <locals> 0 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
      requires V <=Int maxSInt64
       andBool minSInt64 <=Int V
  rule [bigIntGetInt64-not-int64]: <instrs> hostCall ("env", "bigIntGetInt64", [i32 .ValTypes ] -> [i64  .ValTypes ] )
              => #throwException(ExecutionFailed, "big int cannot be represented as int64") ...
        </instrs>
        <locals> 0 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
      requires V >Int maxSInt64
        orBool minSInt64 >Int V
  rule [bigIntGetInt64-invalid-handle]: <instrs> hostCall ("env", "bigIntGetInt64", [i32 .ValTypes ] -> [i64  .ValTypes ] )
              => #setBigIntValue(IDX, 0)
              ~> i64 . const 0
                 ...
        </instrs>
        <locals> 0 |-> <i32> IDX </locals>
        <bigIntHeap> HEAP </bigIntHeap>
      requires notBool #validIntId(IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntGetUnsignedBytes", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #getBigInt(IDX, Unsigned)
               ~> #memStoreFromBytesStack(OFFSET)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX  1 |-> <i32> OFFSET </locals>
  rule <instrs> hostCall("env", "bigIntGetSignedBytes", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #getBigInt(IDX, Signed)
               ~> #memStoreFromBytesStack(OFFSET)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX  1 |-> <i32> OFFSET </locals>
  rule <instrs> hostCall("env", "bigIntSetUnsignedBytes", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(OFFSET, LENGTH)
               ~> #setBigIntFromBytesStack(IDX, Unsigned)
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX 1 |-> <i32> OFFSET 2 |-> <i32> LENGTH </locals>
  rule <instrs> hostCall("env", "bigIntSetSignedBytes", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(OFFSET, LENGTH)
               ~> #setBigIntFromBytesStack(IDX, Signed)
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX 1 |-> <i32> OFFSET 2 |-> <i32> LENGTH </locals>
  rule <instrs> hostCall ( "env" , "bigIntSetInt64" , [ i32  i64  .ValTypes ] -> [ .ValTypes ] )
               => #setBigIntValue(DEST_IDX, #signed(i64, VALUE))
                  ...
         </instrs>
         <locals> 0 |-> <i32> DEST_IDX 1 |-> <i64> VALUE </locals>
  rule <instrs> hostCall("env", "bigIntAdd", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int +Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>
      requires #validIntId(OP1_IDX, HEAP)
       andBool #validIntId(OP2_IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntAdd", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
         </instrs>
         <locals> 0 |-> <i32> _DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(OP1_IDX, HEAP))
        orBool notBool (#validIntId(OP2_IDX, HEAP))
  rule <instrs> hostCall("env", "bigIntSub", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int -Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>
      requires #validIntId(OP1_IDX, HEAP)
       andBool #validIntId(OP2_IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntSub", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
         </instrs>
         <locals> 0 |-> <i32> _DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(OP1_IDX, HEAP))
        orBool notBool (#validIntId(OP2_IDX, HEAP))
  rule <instrs> hostCall("env", "bigIntMul", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int *Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>
      requires #validIntId(OP1_IDX, HEAP)
       andBool #validIntId(OP2_IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntMul", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
         </instrs>
         <locals> 0 |-> <i32> _DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(OP1_IDX, HEAP))
        orBool notBool (#validIntId(OP2_IDX, HEAP))
  rule <instrs> hostCall("env", "bigIntTDiv", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP => HEAP [DST <- {HEAP[OP1_IDX]}:>Int /Int {HEAP[OP2_IDX]}:>Int] </bigIntHeap>
      requires #validIntId(OP1_IDX, HEAP)
       andBool #validIntId(OP2_IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntTDiv", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
         </instrs>
         <locals> 0 |-> <i32> _DST  1 |-> <i32> OP1_IDX  2 |-> <i32> OP2_IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(OP1_IDX, HEAP))
        orBool notBool (#validIntId(OP2_IDX, HEAP))
  rule <instrs> hostCall("env", "bigIntSign", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => i32.const #bigIntSign({HEAP[IDX]}:>Int)
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires #validIntId(IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntSign", [ i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #throwException(ExecutionFailed, "no bigInt under the given handle")
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool #validIntId(IDX, HEAP)
  rule <instrs> hostCall("env", "bigIntCmp", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => i32.const #cmpInt({HEAP[IDX1]}:>Int, {HEAP[IDX2]}:>Int)
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX1  1 |-> <i32> IDX2 </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires #validIntId(IDX1,  HEAP)
       andBool #validIntId(IDX2,  HEAP)
  rule <instrs> hostCall("env", "bigIntCmp", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #throwException(ExecutionFailed, "no bigInt under the given handle")
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX1  1 |-> <i32> IDX2 </locals>
         <bigIntHeap> HEAP </bigIntHeap>
      requires notBool #validIntId(IDX1,  HEAP)
        orBool notBool #validIntId(IDX2,  HEAP)
  rule <instrs> hostCall("env", "bigIntFinishUnsigned", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #getBigInt(IDX, Unsigned)
               ~> #appendToOutFromBytesStack
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
  rule <instrs> hostCall("env", "bigIntFinishSigned", [ i32 .ValTypes ] -> [ .ValTypes ])
               => #getBigInt(IDX, Signed)
               ~> #appendToOutFromBytesStack
                  ...
         </instrs>
         <locals> 0 |-> <i32> IDX </locals>
  rule <instrs> hostCall("env", "bigIntStorageStoreUnsigned", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #getBigIntOrCreate(BIGINTIDX, Unsigned)
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> BIGINTIDX
         </locals>
  rule <instrs> hostCall("env", "bigIntStorageLoadUnsigned", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #setBigIntFromBytesStack(DEST, Unsigned)
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
           2 |-> <i32> DEST
         </locals>
  rule <instrs> hostCall("env", "bigIntGetUnsignedArgument", [ i32 i32 .ValTypes ] -> [ .ValTypes ]) =>  . ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> BIG_IDX </locals>
         <callArgs> ARGS </callArgs>
         <bigIntHeap> HEAP => HEAP [BIG_IDX <- Bytes2Int(ARGS {{ ARG_IDX }}, BE, Unsigned)] </bigIntHeap>
      requires #validArgIdx(ARG_IDX, ARGS)
  rule <instrs> hostCall("env", "bigIntGetUnsignedArgument", [ i32 i32 .ValTypes ] -> [ .ValTypes ]) =>  . ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> _BIG_IDX </locals>
         <callArgs> ARGS </callArgs>
      requires notBool #validArgIdx(ARG_IDX, ARGS)
  rule <instrs> hostCall("env", "bigIntGetSignedArgument", [ i32 i32 .ValTypes ] -> [ .ValTypes ]) =>  . ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> BIG_IDX </locals>
         <callArgs> ARGS </callArgs>
         <bigIntHeap> HEAP => HEAP [BIG_IDX <- Bytes2Int(ARGS {{ ARG_IDX }}, BE, Signed)] </bigIntHeap>
      requires #validArgIdx(ARG_IDX, ARGS)
  rule <instrs> hostCall("env", "bigIntGetSignedArgument", [ i32 i32 .ValTypes ] -> [ .ValTypes ]) =>  . ... </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> _BIG_IDX </locals>
         <callArgs> ARGS </callArgs>
      requires notBool #validArgIdx(ARG_IDX, ARGS)
  rule <instrs> hostCall("env", "bigIntGetCallValue", [ i32 .ValTypes ] -> [ .ValTypes ]) => . ... </instrs>
         <locals> 0 |-> <i32> IDX </locals>
         <bigIntHeap> HEAP => HEAP[IDX <- VALUE] </bigIntHeap>
         <callValue> VALUE </callValue>
  rule <instrs> hostCall("env", "bigIntGetExternalBalance", [ i32 i32 .ValTypes ] -> [ .ValTypes ])
               => #memLoad(ADDROFFSET, 32)
               ~> #getExternalBalance
               ~> #setBigIntFromBytesStack(RESULT, Unsigned)
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDROFFSET
           1 |-> <i32> RESULT
         </locals>
  rule <instrs> hostCall ( "env" , "bigIntGetESDTExternalBalance" , [ i32  i32  i32  i64  i32  .ValTypes ] -> [ .ValTypes ] )
               => #memLoad(ADDR_OFFSET, 32)
               ~> #memLoad(TOK_ID_OFFSET, TOK_ID_LEN)
               ~> #bigIntGetESDTExternalBalance(RES_HANDLE)
               ~> #dropBytes
               ~> #dropBytes
                  ...
         </instrs>
         <locals>
           0 |-> <i32> ADDR_OFFSET
           1 |-> <i32> TOK_ID_OFFSET
           2 |-> <i32> TOK_ID_LEN
           3 |-> <i64> _NONCE   // TODO use nonce
           4 |-> <i32> RES_HANDLE
         </locals>
  syntax InternalInstr  ::=
    "#bigIntGetESDTExternalBalance" "(" Int ")" [klabel(#bigIntGetESDTExternalBalance)]
  rule <instrs> #bigIntGetESDTExternalBalance(RES_HANDLE)
               => #setBigIntValue( RES_HANDLE , BALANCE )
                  ...
         </instrs>
         <bytesStack> TOK_ID : ADDR : _ </bytesStack>
         <account>
           <address> ADDR </address>
           <esdtData>
             <esdtId> TOK_ID </esdtId>
             <esdtBalance> BALANCE </esdtBalance>
             ...
           </esdtData>
           ...
         </account>
       [priority(60)]
  rule <instrs> #bigIntGetESDTExternalBalance(RES_HANDLE)
               => #setBigIntValue( RES_HANDLE , 0 )
                  ...
         </instrs>
         <bytesStack> _TOK_ID : ADDR : _ </bytesStack>
         <account>
           <address> ADDR </address>
           ...
         </account>
       [priority(61)]
  rule [bigIntIsInt64-invalid-handle]: <instrs> hostCall ( "env" , "bigIntIsInt64" , [ i32  .ValTypes ] -> [ i32  .ValTypes ] )
              => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
        </instrs>
        <locals> 0 |-> <i32> IDX </locals>
        <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(IDX, HEAP))
  rule [bigIntIsInt64]: <instrs> hostCall ( "env" , "bigIntIsInt64" , [ i32  .ValTypes ] -> [ i32  .ValTypes ] )
              => i32.const #bool( minSInt64 <=Int V andBool V <=Int maxSInt64 )
                 ...
        </instrs>
        <locals> 0 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
  rule [bigIntSqrt-invalid-handle]: <instrs> hostCall ( "env" , "bigIntSqrt" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
        </instrs>
        <locals> 0 |-> <i32> _DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> HEAP </bigIntHeap>
      requires notBool #validIntId(IDX, HEAP)
  rule [bigIntSqrt-neg]: <instrs> hostCall ( "env" , "bigIntSqrt" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #throwException(ExecutionFailed, "bad bounds (lower)")
                 ...
        </instrs>
        <locals> 0 |-> <i32> _DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
      requires V <Int 0
  rule [bigIntSqrt]: <instrs> hostCall ( "env" , "bigIntSqrt" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #setBigIntValue(DEST, sqrtInt(V))
                 ...
        </instrs>
        <locals> 0 |-> <i32> DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
  rule [bigIntAbs-invalid-handle]: <instrs> hostCall ( "env" , "bigIntAbs" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
        </instrs>
        <locals> 0 |-> <i32> _DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(IDX, HEAP))
  rule [bigIntAbs]: <instrs> hostCall ( "env" , "bigIntAbs" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #setBigIntValue(DEST, absInt(V))
                 ...
        </instrs>
        <locals> 0 |-> <i32> DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
  rule [bigIntNeg-invalid-handle]: <instrs> hostCall ( "env" , "bigIntNeg" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #throwException(ExecutionFailed, "no bigInt under the given handle") ...
        </instrs>
        <locals> 0 |-> <i32> _DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> HEAP </bigIntHeap>
      requires notBool (#validIntId(IDX, HEAP))
  rule [bigIntNeg]: <instrs> hostCall ( "env" , "bigIntNeg" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
              => #setBigIntValue(DEST, 0 -Int V)
                 ...
        </instrs>
        <locals> 0 |-> <i32> DEST  1 |-> <i32> IDX </locals>
        <bigIntHeap> ... IDX |-> V ... </bigIntHeap>
endmodule

module MANBUFOPS
  imports public ELROND-CONFIG
  imports public BIGINT-HELPERS
  imports public MAP-INT-TO-BYTES-PRIMITIVE
  imports public LIST-BYTES-EXTENSIONS
  syntax Bool  ::=
    "#validBufferId" "(" Int "," MapIntToBytes ")" [function, klabel(#validBufferId), total]
  rule #validBufferId(IDX, HEAP) => IDX in_keys {{HEAP}}
  syntax BytesResult  ::=
    "getBuffer" "(" Int ")" [function, klabel(getBuffer), total]
  rule [[ getBuffer(BUFFER_IDX) => {Bs}:>BytesResult ]]
      <bufferHeap> ... wrap(BUFFER_IDX) Int2Bytes|-> wrap(Bs:Bytes) ... </bufferHeap>
  rule getBuffer(_) => {Err("no managed buffer under the given handle")}:>BytesResult  [owise]
  syntax InternalInstr  ::=
    "#getBuffer" "(" idx: Int ")" [klabel(#getBuffer)]
  rule [getBuffer]: <instrs> #getBuffer(BUFFER_IDX) => . ... </instrs>
        <bytesStack> STACK => HEAP{{BUFFER_IDX}} orDefault .Bytes : STACK </bytesStack>
        <bufferHeap> HEAP </bufferHeap>
      requires #validBufferId(BUFFER_IDX, HEAP)
  rule [getBuffer-not-found]: <instrs> #getBuffer(BUFFER_IDX)
              => #throwException(ExecutionFailed, "no managed buffer under the given handle")
                 ...
        </instrs>
        <bufferHeap> HEAP </bufferHeap>
      requires notBool #validBufferId(BUFFER_IDX, HEAP)
  syntax InternalInstr  ::=
    "#setBufferFromBytesStack" "(" idx: Int ")" [klabel(#setBufferFromBytesStack)]
  | "#setBuffer" "(" idx: Int "," value: Bytes ")" [klabel(#setBuffer)]
  rule <instrs> #setBufferFromBytesStack(BUFFER_IDX) => #setBuffer(BUFFER_IDX, BS) ... </instrs>
         <bytesStack> BS : _ </bytesStack>
  rule <instrs> #setBuffer(BUFFER_IDX, BS) => . ... </instrs>
         <bufferHeap> HEAP => HEAP {{ BUFFER_IDX <- BS }} </bufferHeap>
  syntax InternalInstr  ::=
    "#appendBytesToBuffer" "(" Int ")" [klabel(#appendBytesToBuffer)]
  | "#appendBytes"
  rule <instrs> #appendBytesToBuffer( DEST_IDX )
               => #getBuffer(DEST_IDX)
               ~> #appendBytes
               ~> #setBufferFromBytesStack( DEST_IDX )
                  ...
         </instrs>
  rule <instrs> #appendBytes => . ... </instrs>
         <bytesStack> BS1 : BS2 : BSS => (BS1 +Bytes BS2) : BSS </bytesStack>
  syntax InternalInstr  ::=
    "#sliceBytes" "(" Int "," Int ")" [klabel(#sliceBytes)]
  rule <instrs> #sliceBytes(OFFSET, LENGTH) => . ... </instrs>
         <bytesStack> (BS => substrBytes(BS, OFFSET, OFFSET +Int LENGTH)) : _ </bytesStack>
         requires #sliceBytesInBounds( BS , OFFSET , LENGTH )
  syntax Bool  ::=
    "#sliceBytesInBounds" "(" Bytes "," Int "," Int ")" [function, klabel(#sliceBytesInBounds), total]
  rule #sliceBytesInBounds( BS , OFFSET , LENGTH )
            => OFFSET >=Int 0 andBool
               LENGTH >=Int 0 andBool
               OFFSET +Int LENGTH <=Int lengthBytes(BS)
  rule <instrs> hostCall("env", "mBufferSetBytes", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad(OFFSET, LENGTH)
               ~> #setBufferFromBytesStack ( ARG_IDX )
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> OFFSET  2 |-> <i32> LENGTH </locals>
  rule <instrs> hostCall ( "env" , "mBufferGetBytes" , [ i32  i32  .ValTypes ] -> [ i32  .ValTypes ] )
               => #getBuffer( BUFF_IDX )
               ~> #memStoreFromBytesStack ( DEST_OFFSET )
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUFF_IDX  1 |-> <i32> DEST_OFFSET </locals>
  rule <instrs> hostCall("env", "mBufferFromBigIntUnsigned", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBigInt(BIG_IDX, Unsigned)
               ~> #setBufferFromBytesStack ( BUFF_IDX )
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUFF_IDX  1 |-> <i32> BIG_IDX </locals>
  rule <instrs> hostCall("env", "mBufferFromBigIntSigned", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBigInt(BIG_IDX, Signed)
               ~> #setBufferFromBytesStack ( BUFF_IDX )
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUFF_IDX  1 |-> <i32> BIG_IDX </locals>
  rule <instrs> hostCall("env", "mBufferStorageStore", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer(KEY_IDX)
               ~> #getBuffer(VAL_IDX)
               ~> #storageStore
                  ...
         </instrs>
         <locals> 0 |-> <i32> KEY_IDX  1 |-> <i32> VAL_IDX </locals>
  rule <instrs> hostCall("env", "mBufferStorageLoad", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer(KEY_IDX)
               ~> #storageLoad
               ~> #setBufferFromBytesStack(DEST_IDX)
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> KEY_IDX  1 |-> <i32> DEST_IDX </locals>
  rule <instrs> hostCall("env", "mBufferToBigIntUnsigned", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer(KEY_IDX)
               ~> #setBigIntFromBytesStack(DEST_IDX, Unsigned)
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> KEY_IDX  1 |-> <i32> DEST_IDX </locals>
  rule <instrs> hostCall("env", "mBufferToBigIntSigned", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer(KEY_IDX)
               ~> #setBigIntFromBytesStack(DEST_IDX, Signed)
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> KEY_IDX  1 |-> <i32> DEST_IDX </locals>
  rule <instrs> hostCall("env", "mBufferGetArgument", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #setBuffer(DEST_IDX, ARGS {{ ARG_IDX }})
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> ARG_IDX  1 |-> <i32> DEST_IDX </locals>
         <callArgs> ARGS </callArgs>
      requires #validArgIdx(ARG_IDX, ARGS)
  rule <instrs> hostCall("env", "mBufferAppend", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer(DATA_IDX)
               ~> #appendBytesToBuffer( ACC_IDX )
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> ACC_IDX  1 |-> <i32> DATA_IDX </locals>
  rule <instrs> hostCall ( "env" , "mBufferEq" , [ i32  i32  .ValTypes ] -> [ i32  .ValTypes ] )
               => #getBuffer(BUFF1_IDX)
               ~> #getBuffer(BUFF2_IDX)
               ~> #bytesEqual
               ~> #dropBytes
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUFF1_IDX  1 |-> <i32> BUFF2_IDX </locals>
  rule <instrs> hostCall("env", "mBufferAppendBytes", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #memLoad( OFFSET , LENGTH )
               ~> #appendBytesToBuffer( BUFF_IDX )
               ~> #dropBytes
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUFF_IDX  1 |-> <i32> OFFSET  2 |-> <i32> LENGTH </locals>
  rule <instrs> hostCall("env", "mBufferGetLength", [ i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer( BUFF_IDX )
               ~> #returnLength
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUFF_IDX </locals>
  rule <instrs> hostCall("env", "mBufferGetByteSlice", [ i32 i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
               => #getBuffer( SRC_BUFF_IDX )
               ~> #mBufferGetByteSliceH( OFFSET , LENGTH , DEST_OFFSET )
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> SRC_BUFF_IDX  1 |-> <i32> OFFSET  2 |-> <i32> LENGTH  3 |-> <i32> DEST_OFFSET </locals>
  syntax InternalInstr  ::=
    "#mBufferGetByteSliceH" "(" Int "," Int "," Int ")" [klabel(#mBufferGetByteSliceH)]
  rule <instrs> #mBufferGetByteSliceH( OFFSET , LENGTH , DEST_OFFSET )
               => #sliceBytes( OFFSET , LENGTH )
               ~> #memStoreFromBytesStack( DEST_OFFSET )
               ~> i32 . const 0
                  ...
         </instrs>
         <bytesStack> BS : _ </bytesStack>
         requires #sliceBytesInBounds( BS , OFFSET , LENGTH )
  rule <instrs> #mBufferGetByteSliceH( OFFSET , LENGTH , _DEST_OFFSET )
               => i32 . const 1
                  ...
         </instrs>
         <bytesStack> BS : _ </bytesStack>
         requires notBool( #sliceBytesInBounds( BS , OFFSET , LENGTH ) )
  rule <instrs> hostCall("env", "mBufferNew", [ .ValTypes ] -> [ i32 .ValTypes ] )
               => i32.const #newKey(HEAP)
                  ...
         </instrs>
         <bufferHeap> HEAP => HEAP{{#newKey(HEAP) <- .Bytes}} </bufferHeap>
  rule <instrs> hostCall ( "env" , "mBufferNewFromBytes" , [ i32  i32  .ValTypes ] -> [ i32  .ValTypes ] )
              => #memLoad( OFFSET , LENGTH )
              ~> #setBufferFromBytesStack( #newKey(HEAP) )
              ~> #dropBytes
              ~> i32 . const #newKey(HEAP)
                 ...
         </instrs>
         <locals> 0 |-> <i32> OFFSET  1 |-> <i32> LENGTH </locals>
         <bufferHeap> HEAP => HEAP{{#newKey(HEAP) <- .Bytes}} </bufferHeap>
  rule <instrs> hostCall("env", "managedCaller", [ i32 .ValTypes ] -> [ .ValTypes ] )
               => #setBuffer( DEST_IDX , CALLER )
                 ...
         </instrs>
         <locals> 0 |-> <i32> DEST_IDX </locals>
         <caller> CALLER </caller>
  rule <instrs> hostCall("env", "mBufferStorageLoadFromAddress", [ i32 i32 i32 .ValTypes ] -> [ .ValTypes ] )
               => #getBuffer( KEY_IDX )
               ~> #getBuffer( ADDR_IDX )
               ~> #storageLoadFromAddress
               ~> #setBufferFromBytesStack( DEST_IDX )
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> ADDR_IDX  1 |-> <i32> KEY_IDX  2 |-> <i32> DEST_IDX </locals>
  rule <instrs> hostCall ( "env" , "mBufferFinish" , [ i32  .ValTypes ] -> [ i32  .ValTypes ] )
               => #getBuffer( SRC_IDX )
               ~> #appendToOutFromBytesStack
               ~> i32 . const 0
                  ...
         </instrs>
         <locals> 0 |-> <i32> SRC_IDX </locals>
  rule <instrs> hostCall ( "env" , "mBufferCopyByteSlice" , [ i32  i32  i32  i32  .ValTypes ] -> [ i32  .ValTypes ] )
               => #getBuffer( SRC_IDX )
               ~> #mBufferCopyByteSliceH( OFFSET , LENGTH , DEST_IDX )
               ~> #dropBytes
                  ...
         </instrs>
         <locals> 0 |-> <i32> SRC_IDX  1 |-> <i32> OFFSET  2 |-> <i32> LENGTH  3 |-> <i32> DEST_IDX </locals>
  syntax InternalInstr  ::=
    "#mBufferCopyByteSliceH" "(" Int "," Int "," Int ")" [klabel(#mBufferCopyByteSliceH)]
  rule <instrs> #mBufferCopyByteSliceH( OFFSET , LENGTH , DEST_IDX )
               => #sliceBytes( OFFSET , LENGTH )
               ~> #setBufferFromBytesStack( DEST_IDX )
               ~> i32 . const 0
                  ...
         </instrs>
         <bytesStack> BS : _ </bytesStack>
         requires #sliceBytesInBounds( BS , OFFSET , LENGTH )
  rule <instrs> #mBufferCopyByteSliceH( OFFSET , LENGTH , _DEST_OFFSET )
               => i32 . const 1
                  ...
         </instrs>
         <bytesStack> BS : _ </bytesStack>
         requires notBool( #sliceBytesInBounds( BS , OFFSET , LENGTH ) )
endmodule

module CRYPTOEI-HELPERS
  imports public ELROND-CONFIG
  imports public MANBUFOPS
  syntax HashBytesStackInstr  ::=
    "#sha256FromBytesStack"
  rule <instrs> #sha256FromBytesStack => . ... </instrs>
         <bytesStack> (DATA => #parseHexBytes(Sha256(Bytes2String(DATA)))) : _STACK </bytesStack>
  syntax HashBytesStackInstr  ::=
    "#keccakFromBytesStack"
  rule <instrs> #keccakFromBytesStack => . ... </instrs>
         <bytesStack> (DATA => #parseHexBytes(Keccak256(Bytes2String(DATA)))) : _STACK </bytesStack>
  syntax InternalInstr  ::=
    "#hashMemory" "(" Int "," Int "," Int "," HashBytesStackInstr ")" [klabel(#hashMemory)]
  rule <instrs> #hashMemory(DATAOFFSET, LENGTH, RESULTOFFSET, HASHINSTR)
               => #memLoad(DATAOFFSET, LENGTH)
               ~> HASHINSTR
               ~> #memStoreFromBytesStack(RESULTOFFSET)
               ~> #dropBytes
               ~> i32.const 0
               ...
          </instrs>
  syntax InternalInstr  ::=
    "#hashManBuffer" "(" Int "," Int "," HashBytesStackInstr ")" [klabel(#hashManBuffer)]
  rule [hashManBuffer]: <instrs> #hashManBuffer(DATA_HANDLE, DEST_HANDLE, HASHINSTR)
              => #getBuffer(DATA_HANDLE)
              ~> HASHINSTR
              ~> #setBufferFromBytesStack(DEST_HANDLE)
              ~> #dropBytes
              ~> i32.const 0
                ...
        </instrs>
endmodule

module CRYPTOEI
  imports public CRYPTOEI-HELPERS
  rule <instrs> hostCall("env", "sha256", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #hashMemory(DATAOFFSET, LENGTH, RESULTOFFSET, #sha256FromBytesStack)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DATAOFFSET
           1 |-> <i32> LENGTH
           2 |-> <i32> RESULTOFFSET
         </locals>
  rule [managedSha256]: <instrs> hostCall("env", "managedSha256", [ i32 i32  .ValTypes ] -> [ i32  .ValTypes ] )
              => #hashManBuffer(DATA, DEST, #sha256FromBytesStack)
                 ...
        </instrs>
        <locals> 0 |-> <i32> DATA 1 |-> <i32> DEST </locals>
  rule <instrs> hostCall("env", "keccak256", [ i32 i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
               => #hashMemory(DATAOFFSET, LENGTH, RESULTOFFSET, #keccakFromBytesStack)
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DATAOFFSET
           1 |-> <i32> LENGTH
           2 |-> <i32> RESULTOFFSET
         </locals>
  rule [managedKeccak256]: <instrs> hostCall("env", "managedKeccak256", [ i32 i32 .ValTypes ] -> [ i32 .ValTypes ])
              => #hashManBuffer(DATA, DEST, #keccakFromBytesStack)
                 ...
        </instrs>
        <locals> 0 |-> <i32> DATA 1 |-> <i32> DEST </locals>
endmodule

module MANAGEDCONVERSIONS
  imports public ELROND-CONFIG
  imports public MANBUFOPS
  imports public UTILS
  syntax InternalInstr  ::=
    "#writeEsdtsToBytes" "(" List ")" [klabel(#writeEsdtsToBytes)]
  | "#writeEsdtToBytes" "(" ESDTTransfer ")" [klabel(#writeEsdtToBytes)]
  rule <instrs> #writeEsdtsToBytes(.List) => . ... </instrs>
  rule <instrs> #writeEsdtsToBytes(Ts ListItem(T))
               => #writeEsdtToBytes(T)
               ~> #writeEsdtsToBytes(Ts)
                  ...
        </instrs>
  rule <instrs> #writeEsdtToBytes(esdtTransfer(TokId, Value, Nonce))
               => #setBuffer(      #newKey(BUF_HEAP) , TokId )
               ~> #setBigIntValue( #newKey(INT_HEAP) , Value )
               ~> #pushBytes(
                    Int2Bytes(4, #newKey(BUF_HEAP), BE) +Bytes
                    Int2Bytes(8, Nonce,             BE) +Bytes
                    Int2Bytes(4, #newKey(INT_HEAP), BE)
                  )
               ~> #appendBytes
                  ...
        </instrs>
        <bufferHeap> BUF_HEAP </bufferHeap>
        <bigIntHeap> INT_HEAP </bigIntHeap>
  syntax ListResult  ::=
    "readESDTTransfers" "(" Int ")" [function, klabel(readESDTTransfers), total]
  | "readESDTTransfersR" "(" BytesResult ")" [function, klabel(readESDTTransfersR), total]
  | "readESDTTransfersH" "(" Bytes ")" [function, klabel(readESDTTransfersH), total]
  rule readESDTTransfers(IDX)       => readESDTTransfersR(getBuffer(IDX))
  rule readESDTTransfersR(BS:Bytes) => readESDTTransfersH(BS)
  rule readESDTTransfersR(E:Error)  => E
  rule readESDTTransfersH(Bs) => .List
      requires lengthBytes(Bs) ==Int 0
  rule readESDTTransfersH(Bs) => Err("invalid managed vector of ESDT transfers")
      requires lengthBytes(Bs) <Int 16
       andBool lengthBytes(Bs) >Int 0
  rule readESDTTransfersH(Bs)
      => catListResult( readESDTTransfer(substrBytes(Bs, 0, 16))
                      , readESDTTransfersH(substrBytes(Bs, 16, lengthBytes(Bs)))
                      )
      requires lengthBytes(Bs) >=Int 16
  syntax ListResult  ::=
    "readESDTTransfer" "(" Bytes ")" [function, klabel(readESDTTransfer), total]
  rule readESDTTransfer(Bs)
        => mkEsdtTransferFromResults(
              getBuffer( Bytes2Int(substrBytes(Bs, 0, 4), BE, Unsigned) ),
              getBigInt( Bytes2Int(substrBytes(Bs, 12, 16), BE, Unsigned) ),
              Bytes2Int(substrBytes(Bs, 4, 12), BE, Unsigned)
           )
      requires lengthBytes(Bs) ==Int 16
  rule readESDTTransfer(Bs) => Err("invalid ESDT transfer object encoding")
      requires lengthBytes(Bs) =/=Int 16
  syntax ListResult  ::=
    "mkEsdtTransferFromResults" "(" BytesResult "," IntResult "," IntResult ")" [function, klabel(mkEsdtTransferFromResults), total]
  rule mkEsdtTransferFromResults(TokId,   Value,  Nonce)  => ListItem(esdtTransfer(TokId, Value, Nonce))
  rule mkEsdtTransferFromResults(Err(E),  _,      _)      => Err(E)
  rule mkEsdtTransferFromResults(_:Bytes, Err(E), _)      => Err(E)
  rule mkEsdtTransferFromResults(_:Bytes, _:Int,  Err(E)) => Err(E)
  syntax ListBytesResult  ::=
    "readManagedVecOfManagedBuffers" "(" Int ")" [function, klabel(readManagedVecOfManagedBuffers), total]
  rule [[ readManagedVecOfManagedBuffers(BUFFER_IDX) => chunks2buffers(VecBs) ]]
      <bufferHeap> ... wrap(BUFFER_IDX) Int2Bytes|-> wrap(VecBs:Bytes) ... </bufferHeap>
  rule readManagedVecOfManagedBuffers(_) => Err("no managed buffer under the given handle")
       [owise]
  syntax ListBytesResult  ::=
    "chunks2buffers" "(" Bytes ")" [function, klabel(chunks2buffers), total]
  rule chunks2buffers(VecBs) => .ListBytes
      requires lengthBytes(VecBs) ==Int 0
  rule chunks2buffers(VecBs) => Err("invalid managed vector of managed buffer handles")
      requires lengthBytes(VecBs) =/=Int 0
       andBool lengthBytes(VecBs) <Int 4
  rule chunks2buffers(VecBs)
      => catListBytesResult
          ( BytesResult2ListResult(
              getBuffer(Bytes2Int(substrBytes(VecBs, 0, 4), BE, Unsigned))
            )
          , chunks2buffers(substrBytes(VecBs, 4, lengthBytes(VecBs)))
          )
      requires lengthBytes(VecBs) >=Int 4
endmodule

module MANAGEDEI
  imports public ELROND-CONFIG
  imports public MANBUFOPS
  imports public MANAGEDCONVERSIONS
  rule <instrs> hostCall ( "env" , "managedOwnerAddress" , [ i32  .ValTypes ] -> [ .ValTypes ] )
               => #setBuffer( DEST_IDX , OWNER )
                  ...
         </instrs>
         <locals> 0 |-> <i32> DEST_IDX </locals>
         <callee> CALLEE </callee>
         <account>
            <address> CALLEE </address>
            <ownerAddress> OWNER </ownerAddress>
            ...
         </account>
  rule <instrs> hostCall ( "env" , "managedWriteLog" , [ i32  i32  .ValTypes ] -> [ .ValTypes ] )
               => .
                  ...
         </instrs>
  rule <instrs> hostCall ( "env" , "managedSignalError" , [ i32  .ValTypes ] -> [ .ValTypes ] )
               => #getBuffer(ERR_IDX)
               ~> #signalError
                  ...
         </instrs>
         <locals>  0 |-> <i32> ERR_IDX  </locals>
  rule <instrs> hostCall ( "env" , "managedGetMultiESDTCallValue" , [ i32  .ValTypes ] -> [ .ValTypes ] )
               => #pushBytes(.Bytes)
               ~> #writeEsdtsToBytes(ESDTS)
               ~> #setBufferFromBytesStack(DEST_IDX)
               ~> #dropBytes
                  ...
         </instrs>
         <locals>  0 |-> <i32> DEST_IDX  </locals>
         <esdtTransfers> ESDTS </esdtTransfers>
  rule [managedMultiTransferESDTNFTExecute]: <instrs> hostCall("env", "managedMultiTransferESDTNFTExecute", [ i32 i32 i64 i32 i32 .ValTypes ] -> [ i32 .ValTypes ] )
              => #transferESDTNFTExecuteWithTypedArgs(
                  getBuffer(DEST_IDX),
                  readESDTTransfers(TRANSFERS_IDX),
                  GAS_LIMIT,
                  getBuffer(FUNC_IDX),
                  readManagedVecOfManagedBuffers(ARGS_IDX)
                 )
                 ...
        </instrs>
        <locals>
          0 |-> <i32> DEST_IDX
          1 |-> <i32> TRANSFERS_IDX
          2 |-> <i64> GAS_LIMIT
          3 |-> <i32> FUNC_IDX
          4 |-> <i32> ARGS_IDX
        </locals>
  rule <instrs> hostCall ( "env" , "managedSCAddress" , [ i32  .ValTypes ] -> [ .ValTypes ] )
               => #setBuffer( DEST_IDX , CALLEE )
                  ...
         </instrs>
         <locals> 0 |-> <i32> DEST_IDX </locals>
         <callee> CALLEE </callee>
  rule <instrs> hostCall ( "env" , "managedTransferValueExecute" , [ i32  i32  i64  i32  i32  .ValTypes ] -> [ i32  .ValTypes ] )
               => #transferValueExecuteWithTypedArgs(
                    getBuffer(DEST_IDX),
                    getBigInt(VALUE_IDX),
                    GAS_LIMIT,
                    getBuffer(FUNC_IDX),
                    readManagedVecOfManagedBuffers(ARGS_IDX)
                  )
                  ...
         </instrs>
         <locals>
           0 |-> <i32> DEST_IDX
           1 |-> <i32> VALUE_IDX
           2 |-> <i64> GAS_LIMIT
           3 |-> <i32> FUNC_IDX
           4 |-> <i32> ARGS_IDX
         </locals>
  rule <instrs> hostCall("env", "managedGetBlockRandomSeed", [i32  .ValTypes] -> [ .ValTypes ] )
               => #setBuffer(BUF_IDX, SEED)
                  ...
         </instrs>
         <locals> 0 |-> <i32> BUF_IDX </locals>
         <curBlockRandomSeed> SEED </curBlockRandomSeed>
  rule [managedGetPrevBlockRandomSeed]: <instrs> hostCall("env", "managedGetPrevBlockRandomSeed", [i32 .ValTypes] -> [ .ValTypes ] )
              => #setBuffer(BUF_IDX, SEED)
                 ...
        </instrs>
        <locals> 0 |-> <i32> BUF_IDX </locals>
        <prevBlockRandomSeed> SEED </prevBlockRandomSeed>
endmodule

module SMALLINTOPS
  imports public BASEOPS
  imports public ELROND-CONFIG
  imports private LIST-BYTES-EXTENSIONS
  rule [smallIntGetUnsignedArgument]: <instrs> hostCall("env", "smallIntGetUnsignedArgument", [ i32 .ValTypes ] -> [ i64 .ValTypes ])
              => #returnIfUInt64(Bytes2Int(ARGS {{ ARG_IDX }} orDefault b"", BE, Unsigned), "argument out of range")
                 ...
        </instrs>
        <locals> 0 |-> <i32> ARG_IDX </locals>
        <callArgs> ARGS </callArgs>
      requires #validArgIdx(ARG_IDX, ARGS)
  rule [smallIntGetUnsignedArgument-ioor]: <instrs> hostCall("env", "smallIntGetUnsignedArgument", [ i32 .ValTypes ] -> [ i64 .ValTypes ])
              => #throwException(ExecutionFailed, "argument index out of range")
                 ...
        </instrs>
        <locals> 0 |-> <i32> ARG_IDX </locals>
        <callArgs> ARGS </callArgs>
      requires notBool #validArgIdx(ARG_IDX, ARGS)
  rule [smallIntGetSignedArgument]: <instrs> hostCall("env", "smallIntGetSignedArgument", [ i32 .ValTypes ] -> [ i64 .ValTypes ])
              => #returnIfSInt64(Bytes2Int(ARGS {{ ARG_IDX }} orDefault b"", BE, Signed), "argument out of range")
                 ...
        </instrs>
        <locals> 0 |-> <i32> ARG_IDX </locals>
        <callArgs> ARGS </callArgs>
      requires #validArgIdx(ARG_IDX, ARGS)
  rule [smallIntGetSignedArgument-ioor]: <instrs> hostCall("env", "smallIntGetSignedArgument", [ i32 .ValTypes ] -> [ i64 .ValTypes ])
              => #throwException(ExecutionFailed, "argument index out of range")
                 ...
        </instrs>
        <locals> 0 |-> <i32> ARG_IDX </locals>
        <callArgs> ARGS </callArgs>
      requires notBool #validArgIdx(ARG_IDX, ARGS)
  rule <instrs> hostCall("env", "smallIntFinishUnsigned", [ i64 .ValTypes ] -> [ .ValTypes ])
               => #appendToOut(Int2Bytes(#unsigned(i64, VALUE), BE, Unsigned))
                  ...
         </instrs>
         <locals> 0 |-> <i64> VALUE </locals>
  rule <instrs> hostCall("env", "smallIntFinishSigned", [ i64 .ValTypes ] -> [ .ValTypes ])
               => #appendToOut(Int2Bytes(#signed(i64, VALUE), BE, Signed))
                  ...
         </instrs>
         <locals> 0 |-> <i64> VALUE </locals>
  rule <instrs> hostCall("env", "smallIntStorageStoreUnsigned", [ i32 i32 i64 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLEN)
               ~> #pushBytes(Int2Bytes(VALUE, BE, Unsigned))
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLEN
           2 |-> <i64> VALUE
         </locals>
  rule <instrs> hostCall("env", "smallIntStorageStoreSigned", [ i32 i32 i64 .ValTypes ] -> [ i32 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLEN)
               ~> #pushBytes(Int2Bytes(VALUE, BE, Signed))
               ~> #storageStore
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLEN
           2 |-> <i64> VALUE
         </locals>
  rule <instrs> hostCall("env", "smallIntStorageLoadUnsigned", [ i32 i32 .ValTypes ] -> [ i64 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #loadBytesAsUInt64("storage value out of range")
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
         </locals>
  rule <instrs> hostCall("env", "smallIntStorageLoadSigned", [ i32 i32 .ValTypes ] -> [ i64 .ValTypes ])
               => #memLoad(KEYOFFSET, KEYLENGTH)
               ~> #storageLoad
               ~> #loadBytesAsSInt64("storage value out of range")
                  ...
         </instrs>
         <locals>
           0 |-> <i32> KEYOFFSET
           1 |-> <i32> KEYLENGTH
         </locals>
endmodule

module VMHOOKS
  imports public ELROND-CONFIG
  imports public BIGINTOPS
  imports public CRYPTOEI
  imports public BASEOPS
  imports public MANAGEDEI
  imports public MANBUFOPS
  imports public SMALLINTOPS
endmodule

module ELROND
  imports public ELROND-CONFIG
  imports public VMHOOKS
endmodule

module MANDOS-SYNTAX
  imports public MANDOS
  imports public WASM-TEXT-SYNTAX
endmodule

module MANDOS
  imports public COLLECTIONS
  imports public ELROND
  configuration <mandos>
        <k> $PGM:Steps </k>
        <newAddresses> .Map </newAddresses>
        <checkedAccounts> .Set </checkedAccounts>
        <elrond/>
        <exit-code exit=""> 0 </exit-code>
      </mandos>
  syntax Step  ::=
    "#wait"
  rule <k> #wait => . ... </k>
         <commands> . </commands>
         <instrs> . </instrs>
  syntax Steps  ::=
    List{Step,""} [symbol(mandosSteps)]
  rule [steps-empty]: <k> .Steps => . </k>
        <commands> . </commands>
       [priority(60)]
  rule [steps-seq]: <k> S:Step SS:Steps => S ~> SS ... </k>
        <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "setExitCode" Int [klabel(setExitCode), symbol]
  rule <k> setExitCode I => . ... </k>
         <commands> . </commands>
         <instrs> . </instrs>
         <exit-code> _ => I </exit-code>
       [priority(60)]
  syntax Step  ::=
    ModuleDecl
  rule <k> (module _:OptionalId _:Defns):ModuleDecl #as M => #wait ... </k>
         <instrs> . => sequenceStmts(text2abstract(M .Stmts)) </instrs>
         <commands> . </commands>
  rule <k> M:ModuleDecl => #wait ... </k>
         <instrs> . => M </instrs>
         <commands> . </commands>
       [owise]
  syntax Step  ::=
    "register" String [klabel(register), symbol]
  rule <k> register NAME => . ... </k>
         <moduleRegistry> REG => REG [NAME <- IDX -Int 1] </moduleRegistry>
         <nextModuleIdx> IDX </nextModuleIdx>
         <commands> . </commands>
       [priority(60)]
  syntax MapBytesToBytes  ::=
    "#removeEmptyBytes" "(" MapBytesToBytes ")" [function, klabel(#removeEmptyBytes)]
  rule #removeEmptyBytes(.MapBytesToBytes)
        => .MapBytesToBytes
  rule #removeEmptyBytes(Key Bytes2Bytes|-> Value M)
        =>  #if Value ==K wrap(.Bytes)
            #then #removeEmptyBytes(M)
            #else Key Bytes2Bytes|-> Value #removeEmptyBytes(M)
            #fi
  rule #removeEmptyBytes(Key Bytes2Bytes|-> Value M)
        =>  #if Value ==K wrap(.Bytes)
            #then #removeEmptyBytes(M)
            #else Key Bytes2Bytes|-> Value #removeEmptyBytes(M)
            #fi
         [simplification]
  syntax Step  ::=
    "setAccount" "(" address: Address "," nonce: Int "," balance: Int "," code: Code "," owner: Address "," storage: MapBytesToBytes ")" [klabel(setAccount), symbol]
  | "setAccountAux" "(" address: Bytes "," nonce: Int "," balance: Int "," code: Code "," owner: Bytes "," storage: MapBytesToBytes ")" [klabel(setAccountAux), symbol]
  | "createAndSetAccountWithEmptyCode" "(" Bytes "," Int "," Int "," Map ")" [klabel(createAndSetAccountWithEmptyCode)]
  | "createAndSetAccountAfterInitCodeModule" "(" Bytes "," Int "," Int "," Map ")" [klabel(createAndSetAccountAfterInitCodeModule)]
  rule <k> setAccount(ADDRESS, NONCE, BALANCE, CODE, OWNER, STORAGE)
          => setAccountAux(#address2Bytes(ADDRESS), NONCE, BALANCE, CODE, #address2Bytes(OWNER), STORAGE) ... </k>
         <commands> . </commands>
       [priority(60)]
  rule <k> setAccountAux(ADDRESS, NONCE, BALANCE, CODE, OWNER, STORAGE) => #wait ... </k>
         <commands> .
                 => createAccount(ADDRESS)
                 ~> setAccountFields(ADDRESS, NONCE, BALANCE, CODE, OWNER, STORAGE)
         </commands>
       [priority(60)]
  syntax Step  ::=
    "setEsdtBalance" "(" Bytes "," Bytes "," Int ")" [klabel(setEsdtBalance), symbol]
  rule <k> setEsdtBalance( ADDR , TokId , Value ) => . ... </k>
        <account>
          <address> ADDR </address>
          <esdtData>
            <esdtId> TokId </esdtId>
            <esdtBalance> _ => Value </esdtBalance>
            ...
           </esdtData>
          ...
        </account>
        <commands> . </commands>
       [priority(60)]
  rule <k> setEsdtBalance( ADDR , TokId , Value ) => . ... </k>
        <account>
          <address> ADDR </address>
          <esdtDatas>
            (.Bag => <esdtData>
              <esdtId> TokId </esdtId>
              <esdtBalance> Value </esdtBalance>
              <frozen> false </frozen>
            </esdtData>)
            ...
          </esdtDatas>
          ...
        </account>
        <commands> . </commands>
       [priority(61)]
  syntax Step  ::=
    "newAddress" "(" Address "," Int "," Address ")" [klabel(newAddress), symbol]
  | "newAddressAux" "(" Bytes "," Int "," Bytes ")" [klabel(newAddressAux), symbol]
  rule <k> newAddress(CREATOR, NONCE, NEW)
          => newAddressAux(#address2Bytes(CREATOR), NONCE, #address2Bytes(NEW)) ... </k>
         <commands> . </commands>
       [priority(60)]
  rule <k> newAddressAux(CREATOR, NONCE, NEW) => . ... </k>
         <newAddresses> NEWADDRESSES => NEWADDRESSES [tuple(CREATOR, NONCE) <- NEW] </newAddresses>
         <commands> . </commands>
       [priority(60)]
  syntax AddressNonce  ::=
    "tuple" "(" Bytes "," Int ")" [klabel(tuple)]
  syntax Step  ::=
    "setCurBlockInfo" "(" BlockInfo ")" [klabel(setCurBlockInfo), symbol]
  | "setPrevBlockInfo" "(" BlockInfo ")" [klabel(setPrevBlockInfo), symbol]
  syntax BlockInfo  ::=
    "blockTimestamp" "(" Int ")" [klabel(blockTimestamp), symbol]
  | "blockNonce" "(" Int ")" [klabel(blockNonce), symbol]
  | "blockRound" "(" Int ")" [klabel(blockRound), symbol]
  | "blockEpoch" "(" Int ")" [klabel(blockEpoch), symbol]
  | "blockRandomSeed" "(" Bytes ")" [klabel(blockRandomSeed), symbol]
  rule <k> setCurBlockInfo(blockTimestamp(TIMESTAMP)) => . ... </k>
         <curBlockTimestamp> _ => TIMESTAMP </curBlockTimestamp>
         <commands> . </commands>
       [priority(60)]
  rule <k> setCurBlockInfo(blockNonce(NONCE)) => . ... </k>
         <curBlockNonce> _ => NONCE </curBlockNonce>
         <commands> . </commands>
       [priority(60)]
  rule <k> setCurBlockInfo(blockRound(ROUND)) => . ... </k>
         <curBlockRound> _ => ROUND </curBlockRound>
         <commands> . </commands>
       [priority(60)]
  rule <k> setCurBlockInfo(blockEpoch(EPOCH)) => . ... </k>
         <curBlockEpoch> _ => EPOCH </curBlockEpoch>
         <commands> . </commands>
       [priority(60)]
  rule <k> setCurBlockInfo(blockRandomSeed(SEED)) => . ... </k>
         <curBlockRandomSeed> _ => SEED </curBlockRandomSeed>
         <commands> . </commands>
       [priority(60)]
  rule <k> setPrevBlockInfo(blockTimestamp(TIMESTAMP)) => . ... </k>
         <prevBlockTimestamp> _ => TIMESTAMP </prevBlockTimestamp>
         <commands> . </commands>
       [priority(60)]
  rule <k> setPrevBlockInfo(blockNonce(NONCE)) => . ... </k>
         <prevBlockNonce> _ => NONCE </prevBlockNonce>
         <commands> . </commands>
       [priority(60)]
  rule <k> setPrevBlockInfo(blockRound(ROUND)) => . ... </k>
         <prevBlockRound> _ => ROUND </prevBlockRound>
         <commands> . </commands>
       [priority(60)]
  rule <k> setPrevBlockInfo(blockEpoch(EPOCH)) => . ... </k>
         <prevBlockEpoch> _ => EPOCH </prevBlockEpoch>
         <commands> . </commands>
       [priority(60)]
  rule <k> setPrevBlockInfo(blockRandomSeed(SEED)) => . ... </k>
         <prevBlockRandomSeed> _ => SEED </prevBlockRandomSeed>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkAccountNonce" "(" Address "," Int ")" [klabel(checkAccountNonce), symbol]
  | "checkAccountNonceAux" "(" Bytes "," Int ")" [klabel(checkAccountNonceAux), symbol]
  rule <k> checkAccountNonce(ADDRESS, NONCE)
             => checkAccountNonceAux(#address2Bytes(ADDRESS), NONCE) ... </k>
       [priority(60)]
  rule <k> checkAccountNonceAux(ADDR, NONCE) => . ... </k>
         <account>
           <address> ADDR </address>
           <nonce> NONCE </nonce>
           ...
         </account>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkAccountBalance" "(" Address "," Int ")" [klabel(checkAccountBalance), symbol]
  | "checkAccountBalanceAux" "(" Bytes "," Int ")" [klabel(checkAccountBalanceAux), symbol]
  rule <k> checkAccountBalance(ADDRESS, BALANCE)
             => checkAccountBalanceAux(#address2Bytes(ADDRESS), BALANCE) ... </k>
         <commands> . </commands>
       [priority(60)]
  rule <k> checkAccountBalanceAux(ADDR, BALANCE) => . ... </k>
         <account>
           <address> ADDR </address>
           <balance> BALANCE </balance>
           ...
         </account>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkAccountStorage" "(" Address "," MapBytesToBytes ")" [klabel(checkAccountStorage), symbol]
  | "checkAccountStorageAux" "(" Bytes "," MapBytesToBytes ")" [klabel(checkAccountStorageAux), symbol]
  rule <k> checkAccountStorage(ADDRESS, STORAGE)
             => checkAccountStorageAux(#address2Bytes(ADDRESS), STORAGE) ... </k>
         <commands> . </commands>
       [priority(60)]
  rule <k> checkAccountStorageAux(ADDR, STORAGE) => . ... </k>
         <account>
           <address> ADDR </address>
           <storage> ACCTSTORAGE </storage>
           ...
         </account>
         <commands> . </commands>
        requires ACCTSTORAGE ==K #removeEmptyBytes(STORAGE)
       [priority(60)]
  syntax Step  ::=
    "checkAccountCode" "(" Address "," String ")" [klabel(checkAccountCode), symbol]
  | "checkAccountCodeAux" "(" Bytes "," String ")" [klabel(checkAccountCodeAux), symbol]
  rule <k> checkAccountCode(ADDRESS, CODEPATH)
             => checkAccountCodeAux(#address2Bytes(ADDRESS), CODEPATH) ... </k>
         <commands> . </commands>
       [priority(60)]
  syntax OptionalString  ::=
    "#getModuleCodePath" "(" ModuleDecl ")" [function, klabel(#getModuleCodePath), total]
  rule #getModuleCodePath(#module (... metadata: #meta (... filename: PATH ) ) ) => PATH
  rule #getModuleCodePath((module OID:OptionalId DS:Defns) => structureModule(DS, OID))
  rule #getModuleCodePath(_) => .String                                                    [owise]
  rule <k> checkAccountCodeAux(ADDR, "") => . ... </k>
         <account>
           <address> ADDR </address>
           <code> .Code </code>
           ...
         </account>
         <commands> . </commands>
       [priority(60)]
  rule <k> checkAccountCodeAux(ADDR, CODEPATH) => . ... </k>
         <account>
           <address> ADDR </address>
           <code> CODE:ModuleDecl </code>
           ...
         </account>
         <commands> . </commands>
      requires CODEPATH ==K #getModuleCodePath(CODE)
       [priority(60)]
  syntax Step  ::=
    "checkedAccount" "(" Address ")" [klabel(checkedAccount), symbol]
  | "checkedAccountAux" "(" Bytes ")" [klabel(checkedAccountAux), symbol]
  rule <k> checkedAccount(ADDRESS)
             => checkedAccountAux(#address2Bytes(ADDRESS)) ... </k>
         <commands> . </commands>
       [priority(60)]
  rule <k> checkedAccountAux(ADDR) => . ... </k>
         <checkedAccounts> ... (.Set => SetItem(ADDR)) ... </checkedAccounts>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkNoAdditionalAccounts" "(" Set ")" [klabel(checkNoAdditionalAccounts), symbol]
  rule <k> checkNoAdditionalAccounts(EXPECTED) => . ... </k>
         <checkedAccounts> CHECKEDACCTS </checkedAccounts>
         <commands> . </commands>
      requires EXPECTED ==K CHECKEDACCTS
       [priority(60)]
  syntax Step  ::=
    "clearCheckedAccounts" [klabel(clearCheckedAccounts), symbol]
  rule <k> clearCheckedAccounts => . ... </k>
         <checkedAccounts> _ => .Set </checkedAccounts>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "callTx" "(" from: Address "," to: Address "," value: Int "," esdtValue: List "," func: WasmString "," args: ListBytes "," gasLimit: Int "," gasPrice: Int ")" [klabel(callTx), symbol]
  | "callTxAux" "(" from: Bytes "," to: Bytes "," value: Int "," esdtValue: List "," func: WasmString "," args: ListBytes "," gasLimit: Int "," gasPrice: Int ")" [klabel(callTxAux), symbol]
  rule [callTx]: <k> callTx(FROM, TO, VALUE, ESDT, FUNCTION, ARGS, GASLIMIT, GASPRICE)
         => callTxAux(#address2Bytes(FROM), #address2Bytes(TO), VALUE, ESDT, FUNCTION, ARGS, GASLIMIT, GASPRICE) ...
        </k>
        <commands> . </commands>
       [priority(60)]
  rule [callTxAux]: <k> callTxAux(FROM, TO, VALUE, ESDT, FUNCTION, ARGS, GASLIMIT, GASPRICE) => #wait ... </k>
        <commands> . => callContract(TO, FUNCTION, mkVmInputSCCall(FROM, ARGS, VALUE, ESDT, GASLIMIT, GASPRICE)) </commands>
        <account>
          <address> FROM </address>
          <nonce> NONCE => NONCE +Int 1 </nonce>
          <balance> BALANCE => BALANCE -Int GASLIMIT *Int GASPRICE </balance>
          ...
        </account>
        <logging> S => S +String " -- call contract: " +String #parseWasmString(FUNCTION) </logging>
       [priority(60)]
  syntax VmInputCell  ::=
    "mkVmInputSCCall" "(" Bytes "," ListBytes "," Int "," List "," Int "," Int ")" [function, klabel(mkVmInputSCCall), total]
  rule mkVmInputSCCall(FROM, ARGS, VALUE, ESDT, GAS, GAS_PRICE)
      => <vmInput>
            <caller> FROM </caller>
            <callArgs> ARGS </callArgs>
            <callValue> VALUE </callValue>
            <esdtTransfers> ESDT </esdtTransfers>
            // gas
            <gasProvided> GAS </gasProvided>
            <gasPrice> GAS_PRICE </gasPrice>
          </vmInput>
  syntax Step  ::=
    "checkExpectOut" "(" ListBytes ")" [klabel(checkExpectOut), symbol]
  rule <k> checkExpectOut(OUT) => . ... </k>
         <vmOutput> VMOutput(... out: OUT) </vmOutput>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkExpectStatus" "(" ReturnCode ")" [klabel(checkExpectStatus), symbol]
  rule <k> checkExpectStatus(RETURNCODE) => . ... </k>
         <vmOutput> VMOutput(... returnCode: RETURNCODE) </vmOutput>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkExpectMessage" "(" Bytes ")" [klabel(checkExpectMessage), symbol]
  rule <k> checkExpectMessage(MSG) => . ... </k>
         <vmOutput> VMOutput(... returnMessage: MSG) </vmOutput>
         <commands> . </commands>
       [priority(60)]
  syntax Step  ::=
    "checkExpectLogs" "(" List ")" [klabel(checkExpectLogs), symbol]
  rule <k> checkExpectLogs(LOGS) => . ... </k>
         <vmOutput> VMOutput(... logs: LOGS) </vmOutput>
         <commands> . </commands>
       [priority(60)]
  rule <k> checkExpectLogs(_LOGS) => . ... </k>
         <commands> . </commands>
       [priority(61)]
  syntax Step  ::=
    "queryTx" "(" to: Address "," func: WasmString "," args: ListBytes ")" [klabel(queryTx), symbol]
  | "queryTxAux" "(" to: Bytes "," func: WasmString "," args: ListBytes ")" [klabel(queryTxAux), symbol]
  rule <k> queryTx(TO, FUNCTION, ARGS) => queryTxAux(#address2Bytes(TO), FUNCTION, ARGS) ... </k>
       [priority(60)]
  rule <k> queryTxAux(TO, FUNCTION, ARGS) => #wait ... </k>
         <commands> . => callContract(TO, FUNCTION, mkVmInputQuery(TO, ARGS)) </commands>
         <logging> S => S +String " -- query contract: " +String #parseWasmString(FUNCTION) </logging>
       [priority(60)]
  syntax VmInputCell  ::=
    "mkVmInputQuery" "(" Bytes "," ListBytes ")" [function, klabel(mkVmInputQuery), total]
  rule mkVmInputQuery(TO, ARGS)
      => <vmInput>
            <caller> TO </caller>
            <callArgs> ARGS </callArgs>
            <callValue> 0 </callValue>
            <esdtTransfers> .List </esdtTransfers>
            // gas
            <gasProvided> maxUInt64 </gasProvided>
            <gasPrice> 0 </gasPrice>
          </vmInput>
  syntax Step  ::=
    "deployTx" "(" Address "," Int "," ModuleDecl "," ListBytes "," Int "," Int ")" [klabel(deployTx), symbol]
  | "deployTxAux" "(" Bytes "," Int "," ModuleDecl "," ListBytes "," Int "," Int ")" [klabel(deployTxAux), symbol]
  rule <k> deployTx(FROM, VALUE, MODULE, ARGS, GASLIMIT, GASPRICE)
          => deployTxAux(#address2Bytes(FROM), VALUE, MODULE, ARGS, GASLIMIT, GASPRICE) ...
         </k>
         <commands> . </commands>
       [priority(60)]
  rule [deployTxAux]: <k> deployTxAux(FROM, VALUE, MODULE, ARGS, GASLIMIT, GASPRICE) => #wait ... </k>
        <commands> .
                => createAccount(NEWADDR)
                ~> setAccountOwner(NEWADDR, FROM)
                ~> setAccountCode(NEWADDR, MODULE)
                ~> callContract(NEWADDR, "init", mkVmInputDeploy(FROM, VALUE, ARGS, GASLIMIT, GASPRICE))
        </commands>
        <account>
           <address> FROM </address>
           <nonce> NONCE => NONCE +Int 1 </nonce>
           <balance> BALANCE => BALANCE -Int GASLIMIT *Int GASPRICE </balance>
           ...
        </account>
        <newAddresses> ... tuple(FROM, NONCE) |-> NEWADDR:Bytes ... </newAddresses>
       [priority(60)]
  syntax VmInputCell  ::=
    "mkVmInputDeploy" "(" Bytes "," Int "," ListBytes "," Int "," Int ")" [function, klabel(mkVmInputDeploy), total]
  rule mkVmInputDeploy(FROM, VALUE, ARGS, GASLIMIT, GASPRICE)
      => <vmInput>
            <caller> FROM </caller>
            <callArgs> ARGS </callArgs>
            <callValue> VALUE </callValue>
            <esdtTransfers> .List </esdtTransfers>
            // gas
            <gasProvided> GASLIMIT </gasProvided>
            <gasPrice> GASPRICE </gasPrice>
          </vmInput>
  syntax Step  ::=
    "transfer" "(" TransferTx ")" [klabel(transfer), symbol]
  rule <k> transfer(TX) => TX ... </k>
         <commands> . </commands>
       [priority(60)]
  syntax TransferTx  ::=
    "transferTx" "(" from: Address "," to: Bytes "," value: Int ")" [klabel(transferTx), symbol]
  | "transferTxAux" "(" from: Bytes "," to: Bytes "," value: Int ")" [klabel(transferTxAux), symbol]
  rule <k> transferTx(FROM, TO, VAL)
          => transferTxAux(#address2Bytes(FROM), #address2Bytes(TO), VAL) ...
         </k>
         <commands> . </commands>
     [priority(60)]
  rule <k> transferTxAux(FROM, TO, VAL) => #wait ... </k>
         <commands> . => transferFunds(FROM, TO, VAL) </commands>
       [priority(60)]
  syntax Step  ::=
    "validatorReward" "(" ValidatorRewardTx ")" [klabel(validatorReward), symbol]
  rule <k> validatorReward(TX) => TX ... </k>
         <commands> . </commands>
       [priority(60)]
  syntax ValidatorRewardTx  ::=
    "validatorRewardTx" "(" to: Address "," value: Int ")" [klabel(validatorRewardTx), symbol]
  | "validatorRewardTxAux" "(" to: Bytes "," value: Int ")" [klabel(validatorRewardTxAux), symbol]
  rule <k> validatorRewardTx(TO, VAL) => validatorRewardTxAux(#address2Bytes(TO), VAL) ... </k>
         <commands> . </commands>
       [priority(60)]
  rule <k> validatorRewardTxAux(TO, VAL) => . ... </k>
         <account>
           <address> TO </address>
            <storage> STOR
                   => STOR{{String2Bytes("ELRONDreward")
                           <- #incBytes(#lookupStorage(STOR, String2Bytes("ELRONDreward")), VAL)}}
            </storage>
            <balance> TO_BAL => TO_BAL +Int VAL </balance>
            ...
         </account>
         <commands> . </commands>
       [priority(60)]
  syntax Bytes  ::=
    "#incBytes" "(" val: Bytes "," inc: Int ")" [function, klabel(#incBytes)]
  rule #incBytes(VAL, INC) => Int2Bytes(Bytes2Int(VAL, BE, Signed) +Int INC, BE, Signed)
endmodule
