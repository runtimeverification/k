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

module WASM-AUXIL
  imports public WASM
  syntax Stmt  ::=
    Auxil
  syntax Auxil  ::=
    "#clearConfig"
  rule <instrs> #clearConfig => . ...     </instrs>
         <curModIdx>         _ => .Int      </curModIdx>
         <valstack>          _ => .ValStack </valstack>
         <locals>            _ => .Map      </locals>
         <moduleInstances>   _ => .Bag      </moduleInstances>
         <moduleIds>         _ => .Map      </moduleIds>
         <nextModuleIdx>     _ => 0         </nextModuleIdx>
         <moduleRegistry>    _ => .Map      </moduleRegistry>
         <mainStore>
           <nextFuncAddr>    _ => 0         </nextFuncAddr>
           <funcs>           _ => .Bag      </funcs>
           <nextTabAddr>     _ => 0         </nextTabAddr>
           <tabs>            _ => .Bag      </tabs>
           <nextMemAddr>     _ => 0         </nextMemAddr>
           <mems>            _ => .Bag      </mems>
           <nextGlobAddr>    _ => 0         </nextGlobAddr>
           <globals>         _ => .Bag      </globals>
         </mainStore>
endmodule

module WASM-TEST-SYNTAX
  imports public WASM-TEST
  imports public WASM-TEXT-SYNTAX
  imports public WASM-AUXIL
  imports public WASM-REFERENCE-INTERPRETER-SYNTAX
endmodule

module WASM-REFERENCE-INTERPRETER-SYNTAX
  imports public WASM-COMMON-SYNTAX
  syntax Auxil  ::=
    Action
  syntax Action  ::=
    "(" "invoke" OptionalId WasmString Instrs ")"
  | "invoke" Int WasmString
  | "(" "get" OptionalId WasmString ")"
  | "get" Int WasmString
  syntax Auxil  ::=
    "(" "register" WasmString ")"
  | "(" "register" WasmString Index ")"
  syntax DefnStrings  ::=
    List{WasmString,""}
  syntax ModuleDecl  ::=
    "(" "module" OptionalId "binary" DataString ")" [macro]
  | "(" "module" OptionalId "quote" DefnStrings ")" [macro]
  syntax Auxil  ::=
    Assertion
  syntax Assertion  ::=
    "(" "assert_return" Action Instr ")"
  | "(" "assert_return" Action ")"
  | "(" "assert_return_canonical_nan" Action ")"
  | "(" "assert_return_arithmetic_nan" Action ")"
  | "(" "assert_trap" Action WasmString ")"
  | "(" "assert_exhaustion" Action WasmString ")"
  | "(" "assert_malformed" ModuleDecl WasmString ")"
  | "(" "assert_invalid" ModuleDecl WasmString ")"
  | "(" "assert_unlinkable" ModuleDecl WasmString ")"
  | "(" "assert_trap" ModuleDecl WasmString ")"
endmodule

module WASM-TEST
  imports public WASM-REFERENCE-INTERPRETER-SYNTAX
  imports public WASM-AUXIL
  imports public WASM-TEXT
  configuration <wasm-test>
        <k> $PGM:Stmts </k>
        <wasm/>
      </wasm-test>
  rule <k> PGM => . </k>
         <instrs> .K => sequenceStmts(text2abstract(PGM)) </instrs>
  rule <instrs> A:Alloc => #emptyModule() ~> A ... </instrs>
         <curModIdx> .Int </curModIdx>
       [owise]
  rule <instrs> FI:FoldedInstr => sequenceInstrs(unfoldInstrs(FI .Instrs)) ... </instrs>
  syntax Val  ::=
    "token"
  rule <instrs> ( invoke OID:OptionalId ENAME:WasmString IS:Instrs ) => sequenceInstrs(IS) ~> ( invoke OID ENAME .Instrs ) ... </instrs>
      requires IS =/=K .Instrs
  rule <instrs> ( invoke ENAME:WasmString .Instrs ) => invoke CUR ENAME ... </instrs>
         <curModIdx> CUR </curModIdx>
  rule <instrs> ( invoke ID:Identifier ENAME:WasmString .Instrs ) => invoke MODIDX ENAME ... </instrs>
         <moduleIds> ... ID |-> MODIDX ... </moduleIds>
  rule <instrs> invoke MODIDX:Int ENAME:WasmString => ( invoke FADDR ):Instr ... </instrs>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <exports> ... ENAME |-> IDX ... </exports>
           <funcAddrs> ... IDX |-> FADDR ... </funcAddrs>
           ...
         </moduleInst>
  rule <instrs> ( get NAME:WasmString ) => get CUR NAME  ... </instrs>
         <curModIdx> CUR </curModIdx>
  rule <instrs> ( get MOD:Identifier NAME:WasmString ) => get MODIDX NAME ... </instrs>
         <moduleIds> ... MOD |-> MODIDX ... </moduleIds>
  rule <instrs> get MODIDX:Int NAME:WasmString => VAL ... </instrs>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <exports> ... NAME |-> TFIDX ... </exports>
           <globIds> IDS </globIds>
           <globalAddrs> ... #ContextLookup(IDS, TFIDX) |-> ADDR ... </globalAddrs>
           ...
         </moduleInst>
         <globalInst>
           <gAddr> ADDR </gAddr>
           <gValue> VAL </gValue>
           ...
         </globalInst>
  rule <instrs> ( register S ) => ( register S (NEXT -Int 1) )... </instrs> // Register last instantiated module.
         <nextModuleIdx> NEXT </nextModuleIdx>
      requires NEXT >Int 0
  rule <instrs> ( register S ID:Identifier ) => ( register S IDX ) ... </instrs>
         <moduleIds> ... ID |-> IDX ... </moduleIds>
  rule <instrs> ( register S:WasmString IDX:Int ) => . ... </instrs>
         <moduleRegistry> ... .Map => S |-> IDX ... </moduleRegistry>
  rule ( module OID binary _DS ) => ( module OID .Defns )
  rule ( module OID quote _DS ) => ( module OID .Defns )
  syntax Instr  ::=
    "spectest_trap"
  rule <instrs> spectest_trap ~> (_L:Label => .) ... </instrs>
  rule <instrs> spectest_trap ~> (_F:Frame => .) ... </instrs>
  rule <instrs> spectest_trap ~> (_I:Instr => .) ... </instrs>
  rule <instrs> spectest_trap ~> (_D:Defn  => .) ... </instrs>
  rule <instrs> (spectest_trap => .) ~> _M:ModuleDecl ... </instrs>
  rule <instrs> (spectest_trap => .) ~> _A:Assertion  ... </instrs>
  rule <instrs> #import(MOD, _, #funcDesc(... id: OID, type: TIDX))
               => #func(... type: TIDX, locals: [ .ValTypes ], body: spectest_trap .Instrs, metadata: #meta(... id: OID, localIds: .Map))
               ...
         </instrs>
      requires MOD ==K #token("\"spectest\"", "WasmStringToken")
        orBool MOD ==K #token("\"test\""    , "WasmStringToken")
  rule <instrs> (assert_return ACT INSTR)               => ACT ~> INSTR ~> #assertAndRemoveEqual ~> #assertAndRemoveToken ... </instrs>
         <valstack> VALSTACK => token : VALSTACK </valstack>
  rule <instrs> (assert_return ACT)                     => ACT                                   ~> #assertAndRemoveToken ... </instrs>
         <valstack> VALSTACK => token : VALSTACK </valstack>
  rule <instrs> (assert_return_canonical_nan  _ACT)     => . ... </instrs>
  rule <instrs> (assert_return_arithmetic_nan _ACT)     => . ... </instrs>
  rule <instrs> (assert_trap        ACT:Action    DESC) => ACT ~> #assertTrap DESC ... </instrs>
  rule <instrs> (assert_exhaustion _ACT:Action   _DESC) => . ... </instrs>
  rule <instrs> (assert_malformed  _MOD          _DESC) => . ... </instrs>
  rule <instrs> (assert_invalid    _MOD          _DESC) => . ... </instrs>
  rule <instrs> (assert_unlinkable _MOD          _DESC) => . ... </instrs>
  rule <instrs> (assert_trap       MOD:ModuleDecl DESC) => sequenceStmts(text2abstract(MOD .Stmts)) ~> #assertTrap DESC ... </instrs>
  syntax Assertion  ::=
    "#assertAndRemoveEqual"
  | "#assertAndRemoveToken"
  rule <instrs> #assertAndRemoveEqual => #assertTopStack V .WasmString ~> ( drop ) ... </instrs>
         <valstack> V : VALSTACK => VALSTACK </valstack>
  rule <instrs> #assertAndRemoveToken => . ... </instrs>
         <valstack> token : VALSTACK => VALSTACK </valstack>
  syntax Assertion  ::=
    "#assertTrap" WasmString
  rule <instrs> trap ~> #assertTrap _ => . ... </instrs>
  syntax Assertion  ::=
    "#assertTopStack" Val WasmString
  | "#assertTopStackExactly" Val WasmString
  | "#assertStack" ValStack WasmString
  | "#assertStackAux" ValStack ValStack
  rule <instrs> #assertTopStack S                      _ => . ... </instrs> <valstack> S              : _VALSTACK </valstack>
  rule <instrs> #assertTopStack < ITYPE:IValType > VAL _ => . ... </instrs> <valstack> < ITYPE > VAL' : _VALSTACK </valstack>
      requires #unsigned(ITYPE, VAL) ==Int VAL'
  rule <instrs> #assertTopStack < FTYPE:FValType > VAL _ => . ... </instrs> <valstack> < FTYPE > VAL' : _VALSTACK </valstack>
      requires signFloat(VAL) ==Bool signFloat(VAL') andBool VAL ==Float VAL'
  rule <instrs> #assertTopStackExactly A               _ => . ... </instrs> <valstack> A              : _VALSTACK </valstack>
  rule <instrs> #assertStack S1 _ => #assertStackAux S1 S2  ... </instrs>
         <valstack> S2 </valstack>
  rule <instrs> #assertStackAux .ValStack  _                                 => .                       ... </instrs>
  rule <instrs> #assertStackAux (            V : S1')              (V : S2') => #assertStackAux S1' S2' ... </instrs>
  rule <instrs> #assertStackAux (< ITYPE > VAL : S1') (< ITYPE > VAL' : S2') => #assertStackAux S1' S2' ... </instrs>
      requires #unsigned(ITYPE, VAL) ==Int VAL'
  syntax Assertion  ::=
    "#assertLocal" Int Val WasmString
  | "#assertGlobal" Index Val WasmString
  rule <instrs> #assertLocal INDEX VALUE _ => . ... </instrs>
         <locals> ... INDEX |-> VALUE ... </locals>
  rule <instrs> #assertGlobal TFIDX VALUE _ => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <globIds> IDS </globIds>
           <globalAddrs> ... #ContextLookup(IDS , TFIDX) |-> GADDR ... </globalAddrs>
           ...
         </moduleInst>
         <globals>
           <globalInst>
             <gAddr>  GADDR </gAddr>
             <gValue> VALUE </gValue>
             ...
           </globalInst>
           ...
         </globals>
  syntax Assertion  ::=
    "#assertType" Int FuncType
  | "#assertNextTypeIdx" Int
  rule <instrs> #assertType IDX FTYPE => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <types> ... IDX |-> FTYPE ... </types>
           ...
         </moduleInst>
  rule <instrs> #assertNextTypeIdx IDX => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <nextTypeIdx> IDX </nextTypeIdx>
           ...
         </moduleInst>
  syntax Assertion  ::=
    "#assertFunction" Index FuncType VecType WasmString
  rule <instrs> #assertFunction IDX FTYPE LTYPE _ => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <funcAddrs> ... IDX |-> FADDR ... </funcAddrs>
           ...
         </moduleInst>
         <funcs>
           <funcDef>
             <fAddr>  FADDR </fAddr>
             <fType>  FTYPE </fType>
             <fLocal> LTYPE </fLocal>
             ...
           </funcDef>
           ...
         </funcs>
  syntax Assertion  ::=
    "#assertTable" Index Int OptionalInt WasmString
  rule <instrs> #assertTable TFIDX SIZE MAX _MSG => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabIds> IDS </tabIds>
           <tabAddrs> #ContextLookup(IDS, TFIDX) |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabs>
           <tabInst>
             <tAddr> ADDR </tAddr>
             <tmax>  MAX  </tmax>
             <tsize> SIZE </tsize>
             ...
           </tabInst>
           ...
         </tabs>
  syntax Assertion  ::=
    "#assertTableElem" "(" Int "," Int ")" WasmString
  rule <instrs> #assertTableElem (KEY , VAL) _MSG => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <tabAddrs> 0 |-> ADDR </tabAddrs>
           ...
         </moduleInst>
         <tabs>
           <tabInst>
             <tAddr> ADDR </tAddr>
             <tdata> ...  KEY |-> VAL ... </tdata>
               ...
           </tabInst>
           ...
         </tabs>
  syntax Assertion  ::=
    "#assertMemory" Index Int OptionalInt WasmString
  rule <instrs> #assertMemory TFIDX SIZE MAX _MSG => . ... </instrs>
         <curModIdx> CUR </curModIdx>
         <moduleInst>
           <modIdx> CUR </modIdx>
           <memIds> IDS </memIds>
           <memAddrs> #ContextLookup(IDS, TFIDX) |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <mems>
           <memInst>
             <mAddr>   ADDR  </mAddr>
             <mmax>    MAX   </mmax>
             <msize>   SIZE  </msize>
             ...
           </memInst>
           ...
         </mems>
  syntax Assertion  ::=
    "#assertMemoryData" "(" Int "," Int ")" WasmString
  syntax Assertion  ::=
    "#assertMemoryData" Int "(" Int "," Int ")" WasmString
  rule <instrs> #assertMemoryData (KEY , VAL) MSG => #assertMemoryData CUR (KEY, VAL) MSG ... </instrs>
         <curModIdx> CUR </curModIdx>
  rule <instrs> #assertMemoryData MODIDX (KEY , VAL) _MSG => . ... </instrs>
         <moduleInst>
           <modIdx> MODIDX </modIdx>
           <memAddrs> 0 |-> ADDR </memAddrs>
           ...
         </moduleInst>
         <mems>
           <memInst>
             <mAddr> ADDR </mAddr>
             <mdata> BM </mdata>
             ...
           </memInst>
           ...
         </mems>
      requires #getRange(BM, KEY, 1) ==Int VAL
  syntax Assertion  ::=
    "#assertNamedModule" Identifier WasmString
  rule <instrs> #assertNamedModule NAME _S => . ... </instrs>
         <moduleIds> ... NAME |-> IDX ... </moduleIds>
         <moduleInstances>
           <moduleInst>
             <modIdx> IDX </modIdx>
             ...
           </moduleInst>
           ...
         </moduleInstances>
  syntax Assertion  ::=
    "#assertRegistrationUnnamed" WasmString WasmString
  | "#assertRegistrationNamed" WasmString Identifier WasmString
  rule <instrs> #assertRegistrationUnnamed REGNAME _ => . ... </instrs>
         <modIdx> IDX </modIdx>
         <moduleRegistry> ... REGNAME |-> IDX ...  </moduleRegistry>
  rule <instrs> #assertRegistrationNamed REGNAME _NAME _ => . ... </instrs>
         <modIdx> IDX </modIdx>
         <moduleRegistry> ... REGNAME |-> IDX ...  </moduleRegistry>
endmodule


