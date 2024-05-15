// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module JSON-SYNTAX
  imports public INT-SYNTAX
  imports public STRING-SYNTAX
  imports public BOOL-SYNTAX
  imports public FLOAT-SYNTAX
  syntax JSONs  ::=
    List{JSON,","} [symbol(JSONs)]
  syntax JSONKey  ::=
    String
  syntax JSON  ::=
    "null" [klabel(JSONnull), symbol]
  | String
  | Int
  | Float
  | Bool
  | JSONKey ":" JSON [klabel(JSONEntry), symbol]
  | "{" JSONs "}" [klabel(JSONObject), symbol]
  | "[" JSONs "]" [klabel(JSONList), symbol]
endmodule

module JSON
  imports public JSON-SYNTAX
  syntax String  ::=
    "JSON2String" "(" JSON ")" [function, hook(JSON.json2string), klabel(JSON2String)]
  syntax JSON  ::=
    "String2JSON" "(" String ")" [function, hook(JSON.string2json), klabel(String2JSON)]
endmodule

module TEAL-FIELDS
  imports public TEAL-TYPES-SYNTAX
  syntax GlobalField  ::=
    "MinTxnFee"
  | "MinBalance"
  | "MaxTxnLife"
  | "ZeroAddress"
  | "GroupSize"
  | "LogicSigVersion"
  | "Round"
  | "LatestTimestamp"
  | "CurrentApplicationID"
  | "CreatorAddress"
  | "CurrentApplicationAddress"
  | "OpcodeBudget"
  | "CreatorAddress"
  syntax AssetHoldingField  ::=
    "AssetBalance"
  | "AssetFrozen"
  syntax AssetParamsField  ::=
    "AssetTotal" [klabel(AssetTotal), symbol]
  | "AssetDecimals" [klabel(AssetDecimals), symbol]
  | "AssetDefaultFrozen" [klabel(AssetDefaultFrozen), symbol]
  | "AssetUnitName" [klabel(AssetUnitName), symbol]
  | "AssetName" [klabel(AssetName), symbol]
  | "AssetURL" [klabel(AssetURL), symbol]
  | "AssetMetadataHash" [klabel(AssetMetadataHash), symbol]
  | "AssetManager" [klabel(AssetManager), symbol]
  | "AssetReserve" [klabel(AssetReserve), symbol]
  | "AssetFreeze" [klabel(AssetFreeze), symbol]
  | "AssetClawback" [klabel(AssetClawback), symbol]
  | "AssetCreator" [klabel(AssetCreator), symbol]
  syntax AppParamsField  ::=
    "AppApprovalProgram" [klabel(AppApprovalProgram), symbol]
  | "AppClearStateProgram" [klabel(AppClearStateProgram), symbol]
  | "AppGlobalNumUint" [klabel(AppGlobalNumUint), symbol]
  | "AppGlobalNumByteSlice" [klabel(AppGlobalNumByteSlice), symbol]
  | "AppLocalNumUint" [klabel(AppLocalNumUint), symbol]
  | "AppLocalNumByteSlice" [klabel(AppLocalNumByteSlice), symbol]
  | "AppExtraProgramPages" [klabel(AppExtraProgramPages), symbol]
  | "AppCreator" [klabel(AppCreator), symbol]
  | "AppAddress" [klabel(AppAddress), symbol]
  syntax TxnFieldTop  ::=
    TxnField
  | TxnaField
  syntax TxnField  ::=
    TxnStaticField
  | TxnDynamicField
  syntax TxnStaticField  ::=
    TxnHeaderField
  | TxnPayField
  | TxnKeyregField
  | TxnAcfgField
  | TxnAxferField
  | TxnAfrzField
  | TxnApplField
  syntax TxnHeaderField  ::=
    "TxID"
  | "Sender"
  | "Fee"
  | "FirstValid"
  | "FirstValidTime"
  | "LastValid"
  | "Note"
  | "Lease"
  | "RekeyTo"
  | "Type"
  | "TypeEnum"
  | "GroupIndex"
  | "StateProofPK"
  syntax TxnDynamicField  ::=
    "LastLog"
  | "NumLogs"
  | "CreatedApplicationID"
  | "CreatedAssetID"
  syntax TxnPayField  ::=
    "Receiver"
  | "Amount"
  | "CloseRemainderTo"
  syntax TxnKeyregField  ::=
    "VotePK"
  | "SelectionPK"
  | "VoteFirst"
  | "VoteLast"
  | "VoteKeyDilution"
  | "Nonparticipation"
  syntax TxnAcfgField  ::=
    "ConfigAsset"
  | "ConfigAssetTotal"
  | "ConfigAssetDecimals"
  | "ConfigAssetDefaultFrozen"
  | "ConfigAssetUnitName"
  | "ConfigAssetName"
  | "ConfigAssetURL"
  | "ConfigAssetMetaDataHash"
  | "ConfigAssetManager"
  | "ConfigAssetReserve"
  | "ConfigAssetFreeze"
  | "ConfigAssetClawback"
  syntax TxnAxferField  ::=
    "XferAsset"
  | "AssetAmount"
  | "AssetSender"
  | "AssetReceiver"
  | "AssetCloseTo"
  syntax TxnAfrzField  ::=
    "FreezeAsset"
  | "FreezeAssetAccount"
  | "FreezeAssetFrozen"
  syntax TxnApplField  ::=
    "ApplicationID"
  | "OnCompletion"
  | "NumAppArgs"
  | "NumAccounts"
  | "NumAssets"
  | "NumApplications"
  | "ApprovalProgram"
  | "ClearStateProgram"
  | "ExtraProgramPages"
  | "NumApprovalProgramPages"
  | "NumClearStateProgramPages"
  | "LocalNumByteSlice"
  | "LocalNumUint"
  | "GlobalNumByteSlice"
  | "GlobalNumUint"
  syntax TxnaField  ::=
    TxnaStaticField
  | TxnaDynamicField
  syntax TxnaStaticField  ::=
    "ApplicationArgs"
  | "Accounts"
  | "Applications"
  | "Assets"
  syntax TxnaDynamicField  ::=
    "Logs"
  syntax AccountParamsField  ::=
    "AcctBalance"
  | "AcctMinBalance"
  | "AcctAuthAddr"
endmodule

module TEAL-TYPES-SYNTAX
  imports public INT-SYNTAX
  imports public STRING-SYNTAX
  syntax TUInt64  ::=
    Int
  syntax TUInt8  ::=
    Int
  syntax B64Encoded [token]
  syntax B32Encoded [token]
  syntax HexToken [token]
  syntax TAddressLiteral [token]
  syntax TBytes  ::=
    TBytesLiteral
  | TAddressLiteral
  syntax TBytesLiteral  ::=
    "base64" B64Encoded
  | "b64" B64Encoded
  | "base64" "(" B64Encoded ")"
  | "b64" "(" B64Encoded ")"
  | "base32" B32Encoded
  | "b32" B32Encoded
  | "base32" "(" B32Encoded ")"
  | "b32" "(" B32Encoded ")"
  | HexToken
  | String
  syntax TValue  ::=
    TUInt64
  | TBytes
  syntax TValueNeList  ::=
    TValue
  | TValue TValueNeList
  syntax TValueList  ::=
    ".TValueList" [klabel(.TValueList), symbol]
  | TValueNeList
  syntax MaybeTValue  ::=
    "NoTValue" [klabel(NoTValue), symbol]
  | TValue
  syntax TValuePair  ::=
    "(" TValue "," TValue ")"
  syntax TValuePairNeList  ::=
    TValuePair
  | TValuePair TValuePairNeList
  syntax TValuePairList  ::=
    ".TValuePairList" [klabel(.TValuePairList), symbol]
  | TValuePairNeList
  syntax MaybeTValuePair  ::=
    "NoTValuePair"
  | TValuePair
endmodule

module TEAL-TYPES
  imports public TEAL-TYPES-SYNTAX
  imports public BOOL
  imports public K-EQUAL
  imports public BYTES
  imports public INT
  imports public STRING
  imports public KRYPTO
  syntax Int  ::=
    "MAX_UINT8" [macro]
  | "MAX_UINT64" [macro]
  | "MAX_UINT128" [macro]
  rule MAX_UINT8   => 255
  rule MAX_UINT64  => 18446744073709551615
  rule MAX_UINT128 => 340282366920938463463374607431768211455
  syntax Int  ::=
    "lowerU64" "(" Int ")" [function, klabel(lowerU64)]
  rule lowerU64(I) => I &Int MAX_UINT64
  syntax Int  ::=
    "upperU64" "(" Int ")" [function, klabel(upperU64)]
  rule upperU64(I) => I >>Int 64
  syntax TBytes  ::=
    Bytes
  syntax Bytes  ::=
    "normalizeB" "(" TBytes ")" [function, klabel(normalizeB)]
  rule normalizeB(B:Bytes)  => B
  rule normalizeB(S:String) => String2Bytes(S)
  rule normalizeB(H:HexToken) => prepBytesString(Hex2String(H))
  rule normalizeB(TA:TAddressLiteral) => DecodeAddressString(TealAddress2String(TA))
  syntax Bytes  ::=
    "prepBytesString" "(" String ")" [function, klabel(prepBytesString)]
  rule prepBytesString(S:String) => #ParseBytes(substrString(S, 2, lengthString(S)), .Bytes)
  syntax Bytes  ::=
    "#ParseBytes" "(" String "," Bytes ")" [function, klabel(#ParseBytes)]
  rule #ParseBytes("", ByteStr) => ByteStr
  rule #ParseBytes(Hex, ByteStr)
    => #ParseBytes(substrString(Hex, 2, lengthString(Hex)),
                   ByteStr
            +Bytes Int2Bytes(1, String2Base(substrString(Hex, 0, 2), 16), BE))
    requires Hex =/=String ""
  syntax TAddressLiteral  ::=
    "Bytes2TAddressLiteral" "(" Bytes ")" [function, klabel(Bytes2TAddressLiteral)]
  rule Bytes2TAddressLiteral(B) => String2TealAddress(EncodeAddressBytes(B))
  syntax HexToken  ::=
    "Bytes2HexToken" "(" Bytes ")" [function, klabel(Bytes2HexToken)]
  rule Bytes2HexToken(B) => String2Hex("0x" +String Base2String(Bytes2Int(B, BE, Unsigned), 16))
  syntax String  ::=
    "TealAddress2String" "(" TAddressLiteral ")" [function, hook(STRING.token2string), klabel(TealAddress2String), total]
  syntax String  ::=
    "Hex2String" "(" HexToken ")" [function, hook(STRING.token2string), klabel(Hex2String), total]
  syntax TAddressLiteral  ::=
    "String2TealAddress" "(" String ")" [function, hook(STRING.string2token), klabel(String2TealAddress)]
  syntax HexToken  ::=
    "String2Hex" "(" String ")" [function, hook(STRING.string2token), klabel(String2Hex)]
  syntax Bytes  ::=
    "DecodeAddressString" "(" String ")" [function, klabel(DecodeAddressString)]
  syntax String  ::=
    "EncodeAddressBytes" "(" Bytes ")" [function, klabel(EncodeAddressBytes)]
  rule DecodeAddressString(S) => DecodeAddressStringInternal(S) requires IsAddressValid(S)
  rule EncodeAddressBytes(B)  => EncodeAddressBytesInternal(B)  requires lengthBytes(B)  ==Int 32
  syntax Bytes  ::=
    "DecodeAddressStringInternal" "(" String ")" [function, hook(KAVM.address_decode), klabel(DecodeAddressStringInternal)]
  syntax String  ::=
    "EncodeAddressBytesInternal" "(" Bytes ")" [function, hook(KAVM.address_encode), klabel(EncodeAddressBytesInternal)]
  syntax Bool  ::=
    "IsAddressValid" "(" String ")" [function, hook(KAVM.check_address), klabel(IsAddressValid)]
  syntax Bytes  ::=
    "getAppAddressBytes" "(" Int ")" [function, klabel(getAppAddressBytes), total]
  rule getAppAddressBytes(APP_ID) => String2Bytes(Sha512_256raw(Bytes2String(b"appID" +Bytes Int2Bytes(8, APP_ID, BE))))
  syntax Bytes  ::=
    "Base64Decode" "(" String ")" [function, hook(KAVM.b64_decode), klabel(Base64Decode)]
  syntax String  ::=
    "Base64Encode" "(" Bytes ")" [function, hook(KAVM.b64_encode), klabel(Base64Encode)]
  syntax TValue  ::=
    "getTValueAt" "(" Int "," TValueNeList ")" [function, klabel(getTValueAt)]
  rule getTValueAt(I, _ VL) => getTValueAt(I -Int 1, VL)
    requires I >Int 0
  rule getTValueAt(0, V _) => V
  rule getTValueAt(0, V  ) => V
  syntax Int  ::=
    "size" "(" TValueList ")" [function, klabel(size), smtlib(tvlistsize), total]
  rule size(_ VL:TValueNeList) => 1 +Int size(VL)
  rule size(_:TValue       ) => 1
  rule size(.TValueList    ) => 0
  syntax Bool  ::=
    "contains" "(" TValueList "," TValue ")" [function, klabel(contains), total]
  rule contains(V1:TValue VL:TValueNeList, V2:TValue) => contains(VL, V2) orBool V1 ==K V2
  rule contains(V1:TValue                , V2:TValue) => V1 ==K V2
  rule contains(              .TValueList,  _:TValue) => false
  syntax Bool  ::=
    "contains" "(" TValuePairList "," TValuePair ")" [function, klabel(contains), total]
  rule contains(V1:TValuePair VL:TValuePairNeList, V2:TValuePair) => contains(VL, V2) orBool V1 ==K V2
  rule contains(V1:TValuePair                    , V2:TValuePair) => V1 ==K V2
  rule contains(              .TValuePairList,      _:TValuePair) => false
  syntax TValueNeList  ::=
    "reverse" "(" TValueNeList ")" [function, klabel(reverse)]
  rule reverse(V:TValue VL) => append(V, reverse(VL))
  rule reverse(V:TValue   ) => V
  syntax TValuePairList  ::=
    "concat" "(" TValuePairList "," TValuePairList ")" [function, klabel(concat)]
  rule concat(V1:TValuePair V1S:TValuePairNeList, V2S:TValuePairList) => concat(V1S, append(V1, V2S))
  rule concat(.TValuePairList, V2S:TValuePairList) => V2S
  syntax TValueNeList  ::=
    "append" "(" TValue "," TValueList ")" [function, klabel(append)]
  rule append(V, V':TValue VL) => V' append(V, VL)
  rule append(V, V':TValue   ) => V' V
  rule append(V, .TValueList ) => V
  syntax TValueNeList  ::=
    "prepend" "(" TValue "," TValueList ")" [function, klabel(prepend)]
  rule prepend(V, V':TValueNeList) => V V'
  rule prepend(V, .TValueList) => V
  syntax TValuePairNeList  ::=
    "prepend" "(" TValuePair "," TValuePairList ")" [function, klabel(prepend)]
  rule prepend(V, V':TValuePairNeList) => V V'
  rule prepend(V, .TValuePairList) => V
  syntax TValuePairList  ::=
    "reverse" "(" TValuePairList ")" [function, klabel(reverse)]
  rule reverse(V:TValuePair VL) => append(V, reverse(VL))
  rule reverse(V:TValuePair   ) => V
  syntax TValuePairNeList  ::=
    "append" "(" TValuePair "," TValuePairList ")" [function, klabel(append)]
  rule append(V, V':TValuePair VL) => V' append(V, VL)
  rule append(V, V':TValuePair   ) => V' V
  syntax TValueList  ::=
    "convertToBytes" "(" TValueList ")" [function, klabel(convertToBytes), total]
  rule convertToBytes(.TValueList) => .TValueList
  rule convertToBytes(B:TBytes) => B
  rule convertToBytes(I:TUInt64) => Int2Bytes({I}:>Int, BE, Unsigned)
  rule convertToBytes(B:TBytes L:TValueNeList) => (B {convertToBytes(L)}:>TValueNeList)
  rule convertToBytes(I:TUInt64 L:TValueNeList) => (Int2Bytes({I}:>Int, BE, Unsigned) {convertToBytes(L)}:>TValueNeList)
  syntax Int  ::=
    "sizeInBytes" "(" TValue ")" [function, klabel(sizeInBytes), total]
  rule sizeInBytes(_:TUInt64) => 64
  rule sizeInBytes(B:TBytes) => lengthBytes({B}:>Bytes)
  syntax Int  ::=
    "maybeTUInt64" "(" MaybeTValue "," Int ")" [function, klabel(maybeTUInt64), total]
  rule maybeTUInt64(X, _)       => X       requires isTUInt64(X)
  rule maybeTUInt64(_, DEFAULT) => DEFAULT  [owise]
  syntax TValue  ::=
    "normalize" "(" TValue ")" [function, klabel(normalize)]
  rule normalize(V:TUInt64) => V
  rule normalize(V:TBytes) => normalizeB(V)
  syntax Bool  ::=
    "int2Bool" "(" Int ")" [function, klabel(int2Bool), total]
  rule int2Bool(0) => false
  rule int2Bool(A) => true requires A =/=Int 0
  syntax Int  ::=
    "bool2Int" "(" Bool ")" [function, klabel(bool2Int), smtlib(bool2Int), total]
  rule bool2Int(true ) => 1
  rule bool2Int(false) => 0
endmodule

module TEAL-CONSTANTS
  imports public TEAL-TYPES-SYNTAX
  imports public BYTES
  syntax PseudoTUInt64  ::=
    TUInt64
  | TUInt64Token
  syntax TUInt64Token  ::=
    "unknown"
  | "pay"
  | "keyreg"
  | "acfg"
  | "axfer"
  | "afrz"
  | "appl"
  | "ccfg"
  | "ccall"
  | "cfx"
  syntax TUInt64Token  ::=
    "NoOp"
  | "OptIn"
  | "CloseOut"
  | "ClearState"
  | "UpdateApplication"
  | "DeleteApplication"
  syntax TValue  ::=
    "normalizeI" "(" PseudoTUInt64 ")" [function, klabel(normalizeI), total]
  rule normalizeI(V:TUInt64) => V
  rule normalizeI(NoOp             ) => 0
  rule normalizeI(OptIn            ) => 1
  rule normalizeI(CloseOut         ) => 2
  rule normalizeI(ClearState       ) => 3
  rule normalizeI(UpdateApplication) => 4
  rule normalizeI(DeleteApplication) => 5
  rule normalizeI(unknown          ) => 0
  rule normalizeI(pay              ) => 1
  rule normalizeI(keyreg           ) => 2
  rule normalizeI(acfg             ) => 3
  rule normalizeI(axfer            ) => 4
  rule normalizeI(afrz             ) => 5
  rule normalizeI(appl             ) => 6
  rule normalizeI(ccfg             ) => 7
  rule normalizeI(ccall            ) => 8
  rule normalizeI(cfx              ) => 9
  syntax Int  ::=
    "@" TUInt64Token [macro]
  rule @ NoOp              => 0
  rule @ OptIn             => 1
  rule @ CloseOut          => 2
  rule @ ClearState        => 3
  rule @ UpdateApplication => 4
  rule @ DeleteApplication => 5
  rule @ unknown           => 0
  rule @ pay               => 1
  rule @ keyreg            => 2
  rule @ acfg              => 3
  rule @ axfer             => 4
  rule @ afrz              => 5
  rule @ appl              => 6
  rule @ ccfg              => 7
  rule @ ccall             => 8
  rule @ cfx               => 9
  syntax Int  ::=
    "typeString2Enum" "(" Bytes ")" [function, klabel(typeString2Enum)]
  rule typeString2Enum(b"unknown") => @ unknown
  rule typeString2Enum(b"pay")     => @ pay
  rule typeString2Enum(b"keyreg")  => @ keyreg
  rule typeString2Enum(b"acfg")    => @ acfg
  rule typeString2Enum(b"axfer")   => @ axfer
  rule typeString2Enum(b"afrz")    => @ afrz
  rule typeString2Enum(b"appl")    => @ appl
  rule typeString2Enum(b"ccfg")    => @ ccfg
  rule typeString2Enum(b"ccall")   => @ ccall
  rule typeString2Enum(b"cfx")     => @ cfx
  syntax Bytes  ::=
    "typeEnum2String" "(" Int ")" [function, klabel(typeEnum2String)]
  rule typeEnum2String(@ unknown) => b"unknown"
  rule typeEnum2String(@ pay)     => b"pay"
  rule typeEnum2String(@ keyreg)  => b"keyreg"
  rule typeEnum2String(@ acfg)    => b"acfg"
  rule typeEnum2String(@ axfer)   => b"axfer"
  rule typeEnum2String(@ afrz)    => b"afrz"
  rule typeEnum2String(@ appl)    => b"appl"
  rule typeEnum2String(@ ccfg)    => b"ccfg"
  rule typeEnum2String(@ ccall)   => b"ccal"
  rule typeEnum2String(@ cfx)     => b"cfx"
endmodule

module TEAL-OPCODES
  imports public TEAL-CONSTANTS
  imports public TEAL-FIELDS
  syntax PseudoOpCode
  syntax OpCode  ::=
    "NoOpCode"
  | ErrOpCode
  | CryptoOpCode
  | ArithOpCode
  | BitOpCode
  | RelationalOpCode
  | LogicalOpCode
  | ByteOpCode
  | BlockchainOpCode
  | ScratchOpCode
  | BranchingOpCode
  | StackOpCode
  | BoxStorageOpCode
  syntax SigOpCode  ::=
    SigVerOpCode
  | ArgOpCode
  syntax AppOpCode  ::=
    StateOpCode
  | TxnGroupStateOpCode
  | InnerTxOpCode
  syntax ErrOpCode  ::=
    "err"
  syntax CryptoOpCode  ::=
    "sha256"
  | "keccak256"
  | "sha512_256"
  syntax ArithOpCode  ::=
    UnaryArithOpCode
  | BinaryArithOpCode
  syntax UnaryArithOpCode  ::=
    "sqrt"
  syntax BinaryArithOpCode  ::=
    "+"
  | "-"
  | "/"
  | "*"
  | "%"
  | "exp"
  | "addw"
  | "divmodw"
  | "divw"
  | "mulw"
  | "expw"
  syntax BitOpCode  ::=
    NullaryBitOpCode
  | BinaryBitOpCode
  | UnaryBitOpCode
  syntax BinaryBitOpCode  ::=
    "|"
  | "&"
  | "^"
  | "shl"
  | "shr"
  syntax UnaryBitOpCode  ::=
    "~"
  | "bitlen"
  | "bsqrt"
  syntax NullaryBitOpCode  ::=
    "getbit"
  | "setbit"
  syntax RelationalOpCode  ::=
    InequalityOpCode
  | EqualityOpCode
  syntax InequalityOpCode  ::=
    "<"
  | ">"
  | "<="
  | ">="
  syntax EqualityOpCode  ::=
    "=="
  | "!="
  syntax LogicalOpCode  ::=
    BinaryLogicalOpCode
  | UnaryLogicalOpCode
  syntax BinaryLogicalOpCode  ::=
    "&&"
  | "||"
  syntax UnaryLogicalOpCode  ::=
    "!"
  syntax ByteOpCode  ::=
    UnaryByteOpCode
  | BinaryByteOpCode
  | TernaryByteOpCode
  | MathByteOpCode
  syntax UnaryByteOpCode  ::=
    "len"
  | "itob"
  | "btoi"
  | "substring" Int Int
  | "getbyte"
  | "setbyte"
  | "bzero"
  | "extract" TUInt8 TUInt8
  syntax BinaryByteOpCode  ::=
    "concat"
  | "extract_uint16"
  | "extract_uint32"
  | "extract_uint64"
  | "replace2" Int
  syntax TernaryByteOpCode  ::=
    "substring3"
  | "extract3"
  | "replace3"
  syntax MathByteOpCode  ::=
    ArithmMathByteOpCode
  | RelationalMathByteOpCode
  | LogicalMathByteOpCode
  syntax ArithmMathByteOpCode  ::=
    "b+"
  | "b-"
  | "b/"
  | "b%"
  | "b*"
  syntax RelationalMathByteOpCode  ::=
    InequalityMathByteOpCode
  | EqualityMathByteOpCode
  syntax InequalityMathByteOpCode  ::=
    "b<"
  | "b>"
  | "b<="
  | "b>="
  syntax EqualityMathByteOpCode  ::=
    "b=="
  | "b!="
  syntax LogicalMathByteOpCode  ::=
    BinaryLogicalMathByteOpCode
  | UnaryLogicalMathByteOpCode
  syntax BinaryLogicalMathByteOpCode  ::=
    "b|"
  | "b&"
  | "b^"
  syntax UnaryLogicalMathByteOpCode  ::=
    "b~"
  syntax OpCode  ::=
    "intcblock" TUInt64 TValueNeList
  | "intc" Int
  | "intc_0"
  | "intc_1"
  | "intc_2"
  | "intc_3"
  | "bytecblock" TUInt64 TValuePairNeList
  | "bytec" Int
  | "bytec_0"
  | "bytec_1"
  | "bytec_2"
  | "bytec_3"
  syntax PseudoOpCode  ::=
    "int" PseudoTUInt64
  | "byte" TBytesLiteral
  | "addr" TAddressLiteral
  | "method" TBytesLiteral
  syntax BlockchainOpCode  ::=
    "txn" TxnField
  | "txn" TxnaField Int
  | "gtxn" Int TxnField
  | "gtxns" TxnField
  | "txna" TxnaField Int
  | "txnas" TxnaField
  | "gtxna" Int TxnaField Int
  | "gtxnas" Int TxnaField
  | "gtxnsa" TxnaField Int
  | "gtxnsas" TxnaField
  | "global" GlobalField
  syntax ScratchOpCode  ::=
    LoadOpCode
  | StoreOpCode
  syntax LoadOpCode  ::=
    "load" Int
  | "loads"
  syntax StoreOpCode  ::=
    "store" Int
  | "stores"
  syntax Label  ::=
    r"([a-zA-Z0-9]|_)+" [token]
  syntax BranchingOpCode  ::=
    CondBranchOpCode
  | JumpOpCode
  | ReturnOpCode
  | AssertOpCode
  | SubroutineOpCode
  syntax CondBranchOpCode  ::=
    "bnz" Label
  | "bz" Label
  syntax JumpOpCode  ::=
    "b" Label
  syntax ReturnOpCode  ::=
    "return"
  syntax AssertOpCode  ::=
    "assert"
  syntax SubroutineOpCode  ::=
    "callsub" Label
  | "retsub"
  | "proto" Int Int
  | "dupn" Int
  | "frame_dig" Int
  | "frame_bury" Int
  syntax StackOpCode  ::=
    NullaryStackOpCode
  | UnaryStackOpCode
  | BinaryStackOpCode
  | TernaryStackOpCode
  | NAryStackOpCode
  syntax NullaryStackOpCode  ::=
    "pushint" PseudoTUInt64
  | "pushbytes" TBytesLiteral
  syntax UnaryStackOpCode  ::=
    "pop"
  | "dup"
  syntax BinaryStackOpCode  ::=
    "dup2"
  | "swap"
  syntax TernaryStackOpCode  ::=
    "select"
  syntax NAryStackOpCode  ::=
    "dig" Int
  | "cover" Int
  | "uncover" Int
  | "bury" Int
  | "popn" Int
  syntax SigVerOpCode  ::=
    "ed25519verify"
  syntax ArgOpCode  ::=
    "arg" Int
  | "args"
  | "arg_0"
  | "arg_1"
  | "arg_2"
  | "arg_3"
  syntax StateOpCode  ::=
    UnaryStateOpCode
  | BinaryStateOpCode
  | TernaryStateOpCode
  syntax UnaryStateOpCode  ::=
    "balance"
  | "app_global_del"
  | "app_global_get"
  | "asset_params_get" AssetParamsField
  | "acct_params_get" AccountParamsField
  | "app_params_get" AppParamsField
  | "min_balance"
  | "log"
  syntax BinaryStateOpCode  ::=
    "app_opted_in"
  | "app_local_get"
  | "app_global_get_ex"
  | "app_global_put"
  | "app_local_del"
  | "asset_holding_get" AssetHoldingField
  syntax TernaryStateOpCode  ::=
    "app_local_get_ex"
  | "app_local_put"
  syntax BoxStorageOpCode  ::=
    "box_create"
  | "box_extract"
  | "box_replace"
  | "box_del"
  | "box_len"
  | "box_get"
  | "box_put"
  syntax TxnGroupStateOpCode  ::=
    NullaryTxnGroupStateOpCode
  | UnaryTxnGroupStateOpCode
  | BinaryTxnGroupStateOpCode
  syntax NullaryTxnGroupStateOpCode  ::=
    "gaid" Int
  | "gload" Int Int
  syntax UnaryTxnGroupStateOpCode  ::=
    "gaids"
  | "gloads" Int
  syntax BinaryTxnGroupStateOpCode  ::=
    "gloadss"
  syntax InnerTxOpCode  ::=
    "itxn_begin"
  | "itxn_submit"
  | "itxn_field" TxnFieldTop
  | "itxn_next"
  | "itxn" TxnField
  | "itxna" TxnaField Int
  | "itxnas" TxnaField
  | "gitxnas" Int TxnaField
  | "gitxn" Int TxnField
  | "gitxna" Int TxnaField Int
endmodule

module TEAL-SYNTAX
  imports public TEAL-OPCODES
  imports public INT
  imports public STRING
  imports public BOOL
  syntax LabelCode  ::=
    Label ":"
  syntax TealOpCode  ::=
    PseudoOpCode
  | OpCode
  | SigOpCode
  | AppOpCode
  syntax TealOpCodeOrLabel  ::=
    TealOpCode
  | LabelCode
  syntax TealPragmas  ::=
    TealPragma TealPragmas
  | TealPragma
  syntax TealPragma  ::=
    "#pragma" PragmaDirective
  syntax PragmaDirective  ::=
    VersionPragma
  syntax TealMode  ::=
    "stateless"
  | "stateful"
  | "undefined"
  syntax VersionPragma  ::=
    "version" Int
  syntax TealPgm  ::=
    TealOpCodeOrLabel
  | TealOpCodeOrLabel TealPgm [format(%1%n%2)]
  syntax TealInputPgm  ::=
    TealPragmas TealPgm
  | TealPgm
endmodule

module TEAL-PARSER-SYNTAX
  imports public TEAL-SYNTAX
  syntax #Layout  ::=
    r"\\/\\/[^\\n\\r]*"
  | r"([\\ \\n\\r\\t])"
  syntax lexical Digit = r"[0-9]"
  syntax lexical HexDigit = r"[0-9a-fA-F]"
  syntax lexical Alpha = r"[a-zA-Z]"
  syntax lexical Alnum = r"{Alpha}|{Digit}"
  syntax lexical AlnumUbar = r"{Alnum}|_"
  syntax lexical Special = r"[\\-!?+<>=/*]"
  syntax HexToken  ::=
    r"0x{HexDigit}+" [prec(2), token]
  syntax TAddressLiteral  ::=
    r"[0-9A-Z]{58}" [prec(1), token]
endmodule

module TEAL-UNPARSER
  imports public TEAL-SYNTAX
  imports public TEAL-TYPES
  imports public STRING
  syntax String  ::=
    "unparseTEAL" "(" TealPgm ")" [function, klabel(unparseTEAL)]
  rule unparseTEAL(O:TealOpCodeOrLabel TP:TealPgm)
    => unparseTEAL(O) +String "\n" +String unparseTEAL(TP)
  rule unparseTEAL(err)                           => "err"
  rule unparseTEAL(sha256)                        => "sha256"
  rule unparseTEAL(keccak256)                     => "keccak256"
  rule unparseTEAL(sha512_256)                    => "sha512_256"
  rule unparseTEAL(+)                             => "+"
  rule unparseTEAL(-)                             => "-"
  rule unparseTEAL(/)                             => "/"
  rule unparseTEAL(*)                             => "*"
  rule unparseTEAL(%)                             => "%"
  rule unparseTEAL(exp)                           => "exp"
  rule unparseTEAL(addw)                          => "addw"
  rule unparseTEAL(divmodw)                       => "divmodw"
  rule unparseTEAL(divw)                          => "divw"
  rule unparseTEAL(mulw)                          => "mulw"
  rule unparseTEAL(expw)                          => "expw"
  rule unparseTEAL(|)                             => "|"
  rule unparseTEAL(&)                             => "&"
  rule unparseTEAL(^)                             => "^"
  rule unparseTEAL(~)                             => "~"
  rule unparseTEAL(getbit)                        => "getbit"
  rule unparseTEAL(setbit)                        => "setbit"
  rule unparseTEAL(<)                             => "<"
  rule unparseTEAL(>)                             => ">"
  rule unparseTEAL(<=)                            => "<="
  rule unparseTEAL(>=)                            => ">="
  rule unparseTEAL(==)                            => "=="
  rule unparseTEAL(!=)                            => "!="
  rule unparseTEAL(&&)                            => "&&"
  rule unparseTEAL(||)                            => "||"
  rule unparseTEAL(!)                             => "!"
  rule unparseTEAL(len)                           => "len"
  rule unparseTEAL(itob)                          => "itob"
  rule unparseTEAL(btoi)                          => "btoi"
  rule unparseTEAL(substring Start End)           => "substring" +&+ Int2String(Start:Int) +&+ Int2String(End:Int)
  rule unparseTEAL(getbyte)                       => "getbyte"
  rule unparseTEAL(setbyte)                       => "setbyte"
  rule unparseTEAL(concat)                        => "concat"
  rule unparseTEAL(extract Start Length)          => "extract" +&+ Int2String(Start:Int) +&+ Int2String(Length:Int)
  rule unparseTEAL(b+)                            => "b+"
  rule unparseTEAL(b-)                            => "b-"
  rule unparseTEAL(b/)                            => "b/"
  rule unparseTEAL(b*)                            => "b*"
  rule unparseTEAL(b<)                            => "b<"
  rule unparseTEAL(b>)                            => "b>"
  rule unparseTEAL(b<=)                           => "b<="
  rule unparseTEAL(b>=)                           => "b>="
  rule unparseTEAL(b==)                           => "b=="
  rule unparseTEAL(b!=)                           => "b!="
  rule unparseTEAL(b%)                            => "b%"
  rule unparseTEAL(b|)                            => "b|"
  rule unparseTEAL(b&)                            => "b&"
  rule unparseTEAL(b^)                            => "b^"
  rule unparseTEAL(b~)                            => "b~"
  rule unparseTEAL(substring3)                    => "substring3"
  rule unparseTEAL(extract3)                      => "extract3"
  rule unparseTEAL(extract_uint16)                => "extract_uint16"
  rule unparseTEAL(extract_uint32)                => "extract_uint32"
  rule unparseTEAL(extract_uint64)                => "extract_uint64"
  rule unparseTEAL(replace2 I:Int)                => "replace2" +&+ Int2String(I)
  rule unparseTEAL(replace3)                      => "replace3"
  rule unparseTEAL(intcblock Size IntConsts)      => "intcblock" +&+ Int2String(Size:Int) +&+ TValueList2String(IntConsts:TValueNeList)
  rule unparseTEAL(intc Idx)                      => "intc" +&+ Int2String(Idx:Int)
  rule unparseTEAL(intc_0)                        => "intc_0"
  rule unparseTEAL(intc_1)                        => "intc_1"
  rule unparseTEAL(intc_2)                        => "intc_2"
  rule unparseTEAL(intc_3)                        => "intc_3"
  rule unparseTEAL(pushint I:Int)                 => "pushint" +&+ Int2String(I)
  rule unparseTEAL(bytecblock Size ByteConsts)    => "bytecblock" +&+ Int2String(Size:Int) +&+ TValuePairList2String(ByteConsts:TValuePairNeList)
  rule unparseTEAL(bytec Idx)                     => "bytec" +&+ Int2String(Idx:Int)
  rule unparseTEAL(bytec_0)                       => "bytec_0"
  rule unparseTEAL(bytec_1)                       => "bytec_1"
  rule unparseTEAL(bytec_2)                       => "bytec_2"
  rule unparseTEAL(bytec_3)                       => "bytec_3"
  rule unparseTEAL(pushbytes ByteConst)           => "pushbytes" +&+ TValue2String(ByteConst:TBytesLiteral)
  rule unparseTEAL(int I:Int)                     => "int" +&+ Int2String(I)
  rule unparseTEAL(int I:TUInt64Token)            => "int" +&+ IntToken2String(I)
  rule unparseTEAL(byte ByteConst)                => "byte" +&+ TValue2String(ByteConst:TBytesLiteral)
  rule unparseTEAL(addr AddrConst)                => "addr" +&+ TValue2String(AddrConst:TAddressLiteral)
  rule unparseTEAL(method S:String)               => "method" +&+ S
  rule unparseTEAL(txn FieldName)                 => "txn" +&+ TealField2String(FieldName:TxnField)
  rule unparseTEAL(txn FieldName ArrIdx)          => "txn" +&+ TealField2String(FieldName:TxnaField) +&+ Int2String(ArrIdx:Int)
  rule unparseTEAL(gtxn TxnIdx TxnField)          => "gtxn" +&+ Int2String(TxnIdx:Int) +&+ TealField2String(TxnField:TxnField)
  rule unparseTEAL(gtxns TxnField)                => "gtxns" +&+ TealField2String(TxnField:TxnField)
  rule unparseTEAL(txna FieldName ArrIdx)         => "txna" +&+ TealField2String(FieldName:TxnaField) +&+ Int2String(ArrIdx:Int)
  rule unparseTEAL(txnas FieldName)               => "txnas" +&+ TealField2String(FieldName:TxnaField)
  rule unparseTEAL(gtxna TxnIdx FieldName ArrIdx) => "gtxna" +&+ Int2String(TxnIdx:Int) +&+ TealField2String(FieldName:TxnaField) +&+ Int2String(ArrIdx:Int)
  rule unparseTEAL(gtxnas TxnIdx FieldName)       => "gtxnas" +&+ Int2String(TxnIdx:Int) +&+ TealField2String(FieldName:TxnaField)
  rule unparseTEAL(gtxnsa FieldName ArrIdx)       => "gtxnsa" +&+ TealField2String(FieldName:TxnaField) +&+ Int2String(ArrIdx:Int)
  rule unparseTEAL(gtxnsas FieldName)             => "gtxnsas" +&+ TealField2String(FieldName:TxnaField)
  rule unparseTEAL(global FieldName)              => "global" +&+ TealField2String(FieldName:GlobalField)
  rule unparseTEAL(load SlotIdx)                  => "load" +&+ Int2String(SlotIdx:Int)
  rule unparseTEAL(loads)                         => "loads"
  rule unparseTEAL(store SlotIdx)                 => "store" +&+ Int2String(SlotIdx:Int)
  rule unparseTEAL(stores)                        => "stores"
  rule unparseTEAL(bnz Lbl)                       => "bnz" +&+ Label2String(Lbl:Label)
  rule unparseTEAL(bz Lbl)                        => "bz" +&+ Label2String(Lbl:Label)
  rule unparseTEAL(b Lbl)                         => "b" +&+ Label2String(Lbl:Label)
  rule unparseTEAL(Lbl :)                         => Label2String(Lbl) +String ":"
  rule unparseTEAL(return)                        => "return"
  rule unparseTEAL(assert)                        => "assert"
  rule unparseTEAL(callsub)                       => "callsub"
  rule unparseTEAL(retsub)                        => "retsub"
  rule unparseTEAL(proto N M)                     => "proto" +&+ Int2String(N) +&+ Int2String(M)
  rule unparseTEAL(dupn N)                        => "dupn" +&+ Int2String(N)
  rule unparseTEAL(frame_dig N)                   => "frame_dig" +&+ Int2String(N)
  rule unparseTEAL(frame_bury N)                  => "frame_bury" +&+ Int2String(N)
  rule unparseTEAL(pop)                           => "pop"
  rule unparseTEAL(dup)                           => "dup"
  rule unparseTEAL(dup2)                          => "dup2"
  rule unparseTEAL(dig N)                         => "dig" +&+ Int2String(N)
  rule unparseTEAL(cover N)                       => "cover" +&+ Int2String(N)
  rule unparseTEAL(uncover N)                     => "uncover" +&+ Int2String(N)
  rule unparseTEAL(bury N)                        => "bury" +&+ Int2String(N)
  rule unparseTEAL(popn N)                        => "popn" +&+ Int2String(N)
  rule unparseTEAL(select)                        => "select"
  rule unparseTEAL(swap)                          => "swap"
  rule unparseTEAL(ed25519verify)                 => "ed25519verify"
  rule unparseTEAL(arg ArgIdx:Int)                => "arg" +&+ Int2String(ArgIdx)
  rule unparseTEAL(args)                          => "args"
  rule unparseTEAL(arg_0)                         => "arg_0"
  rule unparseTEAL(arg_1)                         => "arg_1"
  rule unparseTEAL(arg_2)                         => "arg_2"
  rule unparseTEAL(arg_3)                         => "arg_3"
  rule unparseTEAL(balance)                       => "balance"
  rule unparseTEAL(app_global_del)                => "app_global_del"
  rule unparseTEAL(app_global_get)                => "app_global_get"
  rule unparseTEAL(asset_params_get FieldName)    => "asset_params_get" +&+ TealField2String(FieldName:AssetParamsField)
  rule unparseTEAL(acct_params_get FieldName)     => "acct_params_get" +&+ TealField2String(FieldName:AccountParamsField)
  rule unparseTEAL(app_params_get FieldName)      => "app_params_get" +&+ TealField2String(FieldName:AppParamsField)
  rule unparseTEAL(min_balance)                   => "min_balance"
  rule unparseTEAL(log)                           => "log"
  rule unparseTEAL(app_opted_in)                  => "app_opted_in"
  rule unparseTEAL(app_local_get)                 => "app_local_get"
  rule unparseTEAL(app_global_get_ex)             => "app_global_get_ex"
  rule unparseTEAL(app_global_put)                => "app_global_put"
  rule unparseTEAL(app_local_del)                 => "app_local_del"
  rule unparseTEAL(asset_holding_get FieldName)   => "asset_holding_get" +&+ TealField2String(FieldName:AssetHoldingField)
  rule unparseTEAL(app_local_get_ex)              => "app_local_get_ex"
  rule unparseTEAL(app_local_put)                 => "app_local_put"
  rule unparseTEAL(box_create)                    => "box_create"
  rule unparseTEAL(box_extract)                   => "box_extract"
  rule unparseTEAL(box_replace)                   => "box_replace"
  rule unparseTEAL(box_del)                       => "box_del"
  rule unparseTEAL(box_len)                       => "box_len"
  rule unparseTEAL(box_get)                       => "box_get"
  rule unparseTEAL(box_put)                       => "box_put"
  rule unparseTEAL(gaid N)                        => "gaid" +&+ Int2String(N)
  rule unparseTEAL(gload N M)                     => "gload" +&+ Int2String(N) +&+ Int2String(M)
  rule unparseTEAL(gaids)                         => "gaids"
  rule unparseTEAL(gloads N)                      => "gloads" +&+ Int2String(N)
  rule unparseTEAL(gloadss)                       => "gloadss"
  rule unparseTEAL(itxn_begin)                    => "itxn_begin"
  rule unparseTEAL(itxn_submit)                   => "itxn_submit"
  rule unparseTEAL(itxn_field FieldName)          => "itxn_field" +&+ TealField2String(FieldName:TxnField)
  rule unparseTEAL(itxn_next)                     => "itxn_next"
  rule unparseTEAL(itxn FieldName)                => "itxn" +&+ TealField2String(FieldName:TxnField)
  rule unparseTEAL(itxna FieldName N)             => "itxna" +&+ TealField2String(FieldName:TxnField) +&+ Int2String(N)
  rule unparseTEAL(gitxn T FieldName)             => "itxn" +&+ Int2String(T) +&+ TealField2String(FieldName:TxnField)
  rule unparseTEAL(gitxna T FieldName N)          => "itxna" +&+ Int2String(T) +&+ TealField2String(FieldName:TxnField) +&+ Int2String(N)
  rule unparseTEAL(itxnas FieldName)              => "itxnas" +&+ TealField2String(FieldName:TxnaField)
  rule unparseTEAL(gitxnas T FieldName)           => "gitxnas" +&+ Int2String(T) +&+ TealField2String(FieldName:TxnaField)
  syntax String  ::=
    left:
    String "+&+" String [function]
  rule S:String +&+ S2:String  => S +String " " +String S2
  syntax String  ::=
    "Label2String" "(" Label ")" [function, functional, hook(STRING.token2string), klabel(Label2String)]
  syntax String  ::=
    "TealField2String" "(" GlobalField ")" [function, klabel(TealField2String)]
  | "TealField2String" "(" AssetHoldingField ")" [function, klabel(TealField2String)]
  | "TealField2String" "(" AssetParamsField ")" [function, klabel(TealField2String)]
  | "TealField2String" "(" AppParamsField ")" [function, klabel(TealField2String)]
  | "TealField2String" "(" TxnField ")" [function, klabel(TealField2String)]
  | "TealField2String" "(" TxnaField ")" [function, klabel(TealField2String)]
  | "TealField2String" "(" AccountParamsField ")" [function, klabel(TealField2String)]
  rule TealField2String(MinTxnFee)                => "MinTxnFee"
  rule TealField2String(MinBalance)               => "MinBalance"
  rule TealField2String(MaxTxnLife)               => "MaxTxnLife"
  rule TealField2String(ZeroAddress)              => "ZeroAddress"
  rule TealField2String(GroupSize)                => "GroupSize"
  rule TealField2String(LogicSigVersion)          => "LogicSigVersion"
  rule TealField2String(Round)                    => "Round"
  rule TealField2String(LatestTimestamp)          => "LatestTimestamp"
  rule TealField2String(CurrentApplicationID)     => "CurrentApplicationID"
  rule TealField2String(CreatorAddress)           => "CreatorAddress"
  rule TealField2String(AssetBalance)             => "AssetBalance"
  rule TealField2String(AssetFrozen)              => "AssetFrozen"
  rule TealField2String(AssetTotal)               => "AssetTotal"
  rule TealField2String(AssetDecimals)            => "AssetDecimals"
  rule TealField2String(AssetDefaultFrozen)       => "AssetDefaultFrozen"
  rule TealField2String(AssetUnitName)            => "AssetUnitName"
  rule TealField2String(AssetName)                => "AssetName"
  rule TealField2String(AssetURL)                 => "AssetURL"
  rule TealField2String(AssetMetadataHash)        => "AssetMetadataHash"
  rule TealField2String(AssetManager)             => "AssetManager"
  rule TealField2String(AssetReserve)             => "AssetReserve"
  rule TealField2String(AssetFreeze)              => "AssetFreeze"
  rule TealField2String(AssetClawback)            => "AssetClawback"
  rule TealField2String(AppApprovalProgram)       => "AppApprovalProgram"
  rule TealField2String(AppClearStateProgram)     => "AppClearStateProgram"
  rule TealField2String(AppGlobalNumUint)         => "AppGlobalNumUint"
  rule TealField2String(AppGlobalNumByteSlice)    => "AppGlobalNumByteSlice"
  rule TealField2String(AppLocalNumUint)          => "AppLocalNumUint"
  rule TealField2String(AppLocalNumByteSlice)     => "AppLocalNumByteSlice"
  rule TealField2String(AppExtraProgramPages)     => "AppExtraProgramPages"
  rule TealField2String(AppCreator)               => "AppCreator"
  rule TealField2String(AppAddress)               => "AppAddress"
  rule TealField2String(TxID)                     => "TxID"
  rule TealField2String(Sender)                   => "Sender"
  rule TealField2String(Fee)                      => "Fee"
  rule TealField2String(FirstValid)               => "FirstValid"
  rule TealField2String(FirstValidTime)           => "FirstValidTime"
  rule TealField2String(LastValid)                => "LastValid"
  rule TealField2String(Note)                     => "Note"
  rule TealField2String(Lease)                    => "Lease"
  rule TealField2String(RekeyTo)                  => "RekeyTo"
  rule TealField2String(Type)                     => "Type"
  rule TealField2String(TypeEnum)                 => "TypeEnum"
  rule TealField2String(GroupIndex)               => "GroupIndex"
  rule TealField2String(StateProofPK)             => "StateProofPK"
  rule TealField2String(LastLog)                  => "LastLog"
  rule TealField2String(NumLogs)                  => "NumLogs"
  rule TealField2String(Logs)                     => "Logs"
  rule TealField2String(Receiver)                 => "Receiver"
  rule TealField2String(Amount)                   => "Amount"
  rule TealField2String(CloseRemainderTo)         => "CloseRemainderTo"
  rule TealField2String(VotePK)                   => "VotePK"
  rule TealField2String(SelectionPK)              => "SelectionPK"
  rule TealField2String(VoteFirst)                => "VoteFirst"
  rule TealField2String(VoteLast)                 => "VoteLast"
  rule TealField2String(VoteKeyDilution)          => "VoteKeyDilution"
  rule TealField2String(ConfigAsset)              => "ConfigAsset"
  rule TealField2String(ConfigAssetTotal)         => "ConfigAssetTotal"
  rule TealField2String(ConfigAssetDecimals)      => "ConfigAssetDecimals"
  rule TealField2String(ConfigAssetDefaultFrozen) => "ConfigAssetDefaultFrozen"
  rule TealField2String(ConfigAssetUnitName)      => "ConfigAssetUnitName"
  rule TealField2String(ConfigAssetName)          => "ConfigAssetName"
  rule TealField2String(ConfigAssetURL)           => "ConfigAssetURL"
  rule TealField2String(ConfigAssetMetaDataHash)  => "ConfigAssetMetaDataHash"
  rule TealField2String(ConfigAssetManager)       => "ConfigAssetManager"
  rule TealField2String(ConfigAssetReserve)       => "ConfigAssetReserve"
  rule TealField2String(ConfigAssetFreeze)        => "ConfigAssetFreeze"
  rule TealField2String(ConfigAssetClawback)      => "ConfigAssetClawback"
  rule TealField2String(XferAsset)                => "XferAsset"
  rule TealField2String(AssetAmount)              => "AssetAmount"
  rule TealField2String(AssetSender)              => "AssetSender"
  rule TealField2String(AssetReceiver)            => "AssetReceiver"
  rule TealField2String(AssetCloseTo)             => "AssetCloseTo"
  rule TealField2String(FreezeAsset)              => "FreezeAsset"
  rule TealField2String(FreezeAssetAccount)       => "FreezeAssetAccount"
  rule TealField2String(FreezeAssetFrozen)        => "FreezeAssetFrozen"
  rule TealField2String(ApplicationID)            => "ApplicationID"
  rule TealField2String(OnCompletion)             => "OnCompletion"
  rule TealField2String(NumAppArgs)               => "NumAppArgs"
  rule TealField2String(NumAccounts)              => "NumAccounts"
  rule TealField2String(NumAssets)                => "NumAssets"
  rule TealField2String(NumApplications)          => "NumApplications"
  rule TealField2String(ApprovalProgram)          => "ApprovalProgram"
  rule TealField2String(ClearStateProgram)        => "ClearStateProgram"
  rule TealField2String(ExtraProgramPages)        => "ExtraProgramPages"
  rule TealField2String(NumApprovalProgramPages   => "NumApprovalProgramPages"
  rule TealField2String(NumClearStateProgramPages)=> "NumClearStateProgramPages"
  rule TealField2String(LocalNumByteSlice)        => "LocalNumByteSlice"
  rule TealField2String(LocalNumUint)             => "LocalNumUint"
  rule TealField2String(GlobalNumByteSlice)       => "GlobalNumByteSlice"
  rule TealField2String(GlobalNumUint)            => "GlobalNumUint"
  rule TealField2String(ApplicationArgs)          => "ApplicationArgs"
  rule TealField2String(Accounts)                 => "Accounts"
  rule TealField2String(Applications)             => "Applications"
  rule TealField2String(Assets)                   => "Assets"
  rule TealField2String(AcctBalance)              => "AcctBalance"
  rule TealField2String(AcctMinBalance)           => "AcctMinBalance"
  rule TealField2String(AcctAuthAddr)             => "AcctAuthAddr"
  syntax String  ::=
    "TValue2String" "(" TValue ")" [function, klabel(TValue2String)]
  | "TValuePair2String" "(" TValuePair ")" [function, klabel(TValuePair2String)]
  rule TValue2String(I:Int)              => Int2String(I)
  rule TValue2String(S:String)           => "\"" +String S +String "\""
  rule TValue2String(H:HexToken)         => Hex2String(H)
  rule TValue2String(B:Bytes)            => "0x" +String Base2String(Bytes2Int(B,BE,Unsigned), 16)
  rule TValue2String(TA:TAddressLiteral) => TealAddress2String(TA)
  rule TValuePair2String((TV, TV2))      => "( " +String TValue2String(TV) +String ", " +String  TValue2String(TV2) +String " )"
  syntax String  ::=
    "TValueList2String" "(" TValueNeList ")" [function, klabel(TValueList2String)]
  | "TValuePairList2String" "(" TValuePairList ")" [function, klabel(TValuePairList2String)]
  rule TValueList2String(TV:TValue TVL:TValueNeList)           => TValue2String(TV) +&+ TValueList2String(TVL)
  rule TValueList2String(TV:TValue)                            => TValue2String(TV)
  rule TValuePairList2String(TV:TValuePair TVL:TValuePairNeList) => TValuePair2String(TV) +&+ TValuePairList2String(TVL)
  rule TValuePairList2String(TV:TValuePair)                    => TValuePair2String(TV)
  syntax String  ::=
    "IntToken2String" "(" TUInt64Token ")" [function, hook(STRING.token2string), klabel(IntToken2String)]
  rule IntToken2String(unknown)           => "unknown"
  rule IntToken2String(pay)               => "pay"
  rule IntToken2String(keyreg)            => "keyreg"
  rule IntToken2String(acfg)              => "acfg"
  rule IntToken2String(axfer)             => "axfer"
  rule IntToken2String(afrz)              => "afrz"
  rule IntToken2String(appl)              => "appl"
  rule IntToken2String(NoOp)              => "NoOp"
  rule IntToken2String(OptIn)             => "OptIn"
  rule IntToken2String(CloseOut)          => "CloseOut"
  rule IntToken2String(ClearState)        => "ClearState"
  rule IntToken2String(UpdateApplication) => "UpdateApplication"
  rule IntToken2String(DeleteApplication) => "DeleteApplication"
endmodule

module TXN-FIELDS
  imports public TEAL-FIELDS
  imports public TEAL-SYNTAX
  imports public BYTES
  imports public AVM-CONSTANTS
  configuration <txHeader>
        <fee>         NoTValue </fee>
        <firstValid>  NoTValue </firstValid>       // first round during which the transaction is valid
        <lastValid>   NoTValue </lastValid>        // the transaction is not valid beyond this round (round range max is 1000 rounds)
        <genesisHash> NoTValue </genesisHash>      // uniquely identifies the network
        <sender>      NoTValue </sender>
        <txType>      NoTValue </txType>
        <typeEnum>    NoTValue </typeEnum>
        <groupID>     ""       </groupID>
        <groupIdx>    NoTValue </groupIdx>
        <genesisID>   NoTValue </genesisID>        // a human-readable name: does not necessarily uniquely identify the network
        <lease>       NoTValue </lease>
        <note>        NoTValue </note>
        <rekeyTo>     PARAM_ZERO_ADDR </rekeyTo>
      </txHeader>
  configuration <payTxFields multiplicity="?">
        <receiver>         NoTValue </receiver>
        <amount>           NoTValue </amount>           // this is 0 if not specified
        <closeRemainderTo> NoTValue </closeRemainderTo> // close the sender account and transfer any remaining balance to this account
      </payTxFields>
  configuration <appCallTxFields multiplicity="?">
        <applicationID>        NoTValue    </applicationID>
        <onCompletion>         NoTValue    </onCompletion>
        <accounts>             .TValueList </accounts>
        <approvalProgramSrc>     (int 0):TealInputPgm </approvalProgramSrc>
        <clearStateProgramSrc>   (int 1):TealInputPgm </clearStateProgramSrc>
        <approvalProgram>      NoTValue      </approvalProgram>
        <clearStateProgram>    NoTValue      </clearStateProgram>
        <applicationArgs>      .TValueList </applicationArgs> // maximum size is 2KB, and all args are internally byte strings
        <foreignApps>          .TValueList </foreignApps>
        <foreignAssets>        .TValueList </foreignAssets>
        <boxReferences>        .TValuePairList </boxReferences>
        <globalStateSchema>
          <globalNui> NoTValue </globalNui>
          <globalNbs> NoTValue </globalNbs>
        </globalStateSchema>
        <localStateSchema>
          <localNui> NoTValue </localNui>
          <localNbs> NoTValue </localNbs>
        </localStateSchema>
        <extraProgramPages> NoTValue </extraProgramPages>
      </appCallTxFields>
  configuration <keyRegTxFields multiplicity="?">
      <votePk>           NoTValue </votePk>
      <selectionPK>      NoTValue </selectionPK>
      <voteFirst>        NoTValue </voteFirst>
      <voteLast>         NoTValue </voteLast>
      <voteKeyDilution>  NoTValue </voteKeyDilution>
      <nonparticipation> NoTValue </nonparticipation>
    </keyRegTxFields>
  configuration <assetConfigTxFields multiplicity="?">
      <configAsset> NoTValue </configAsset>           // the asset ID
      <assetParams>
        <configTotal>         0        </configTotal>
        <configDecimals>      0        </configDecimals>
        <configDefaultFrozen> 0        </configDefaultFrozen>
        <configUnitName>      .Bytes   </configUnitName>
        <configAssetName>     .Bytes   </configAssetName>
        <configAssetURL>      .Bytes   </configAssetURL>
        <configMetaDataHash>  .Bytes   </configMetaDataHash>
        <configManagerAddr>   PARAM_ZERO_ADDR </configManagerAddr>
        <configReserveAddr>   PARAM_ZERO_ADDR </configReserveAddr>
        <configFreezeAddr>    PARAM_ZERO_ADDR </configFreezeAddr>
        <configClawbackAddr>  PARAM_ZERO_ADDR </configClawbackAddr>
      </assetParams>
    </assetConfigTxFields>
  configuration <assetTransferTxFields multiplicity="?">
      <xferAsset>     0 </xferAsset>
      <assetAmount>   0 </assetAmount>
      <assetReceiver> .Bytes </assetReceiver>
      <assetASender>  .Bytes </assetASender>
      <assetCloseTo>  .Bytes </assetCloseTo>
    </assetTransferTxFields>
  configuration <assetFreezeTxFields multiplicity="?">
     <freezeAccount> PARAM_ZERO_ADDR </freezeAccount>
     <freezeAsset>   0 </freezeAsset>
     <assetFrozen>   0 </assetFrozen>
   </assetFreezeTxFields>
endmodule

module ALGO-TXN
  imports public TXN-FIELDS
  imports public TEAL-TYPES
  imports public SET
  imports public LIST
  imports public BYTES-HOOKED
  imports public GLOBALS
  configuration <transactions>
        <transaction multiplicity="*" type="Map">
          <txID> "" </txID>
          <txHeader/>
          <txnTypeSpecificFields>
            <payTxFields/>
            <appCallTxFields/>
            <keyRegTxFields/>
            <assetConfigTxFields/>
            <assetTransferTxFields/>
            <assetFreezeTxFields/>
          </txnTypeSpecificFields>
          <applyData>
            <txScratch>       .Map  </txScratch>
            <txConfigAsset>   0     </txConfigAsset>
            <txApplicationID> 0     </txApplicationID>
            <log>
              <logData> .TValueList </logData>
              <logSize> 0:TValue    </logSize>
            </log>
          </applyData>
          <txnExecutionContext> .K </txnExecutionContext>
          <resume> false </resume>
        </transaction>
      </transactions>
  syntax String  ::=
    "getTxID" "(" TransactionCell ")" [function, klabel(getTxID), total]
  rule getTxID(<transaction> <txID> ID </txID> ... </transaction>) => ID
  syntax String  ::=
    "getTxnGroupID" "(" String ")" [function, klabel(getTxnGroupID)]
  rule [[ getTxnGroupID(TXN_ID) => I ]]
       <transaction>
         <txID> TXN_ID </txID>
         <groupID> I </groupID>
         ...
       </transaction>
  syntax Int  ::=
    "getTxnGroupIndex" "(" String ")" [function, klabel(getTxnGroupIndex)]
  rule [[ getTxnGroupIndex(TXN_ID) => I ]]
       <transaction>
         <txID> TXN_ID </txID>
         <groupIdx> I </groupIdx>
         ...
       </transaction>
  syntax MaybeTValue  ::=
    "getTxnField" "(" String "," TxnField ")" [function, klabel(getTxnField), total]
  syntax MaybeTValue  ::=
    "getTxnField" "(" String "," TxnaField "," Int ")" [function, klabel(getTxnField), total]
  syntax TValueList  ::=
    "getTxnField" "(" String "," TxnaField ")" [function, klabel(getTxnField), total]
  rule [[ getTxnField(I, TxID) => normalize(I) ]]
       <transaction>
         <txID> I </txID>
         ...
       </transaction>
  rule [[ getTxnField(I, Sender) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <sender> X </sender>
         ...
       </transaction>
  rule [[ getTxnField(I, Fee) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <fee> X </fee>
         ...
       </transaction>
  rule [[ getTxnField(I, FirstValid) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <firstValid> X </firstValid>
         ...
       </transaction>
  rule [[ getTxnField(I, LastValid) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <lastValid> X </lastValid>
         ...
       </transaction>
  rule [[ getTxnField(I, Note)  => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <note> X </note>
         ...
       </transaction>
  rule [[ getTxnField(I, Lease)  => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <lease> X </lease>
         ...
       </transaction>
  rule [[ getTxnField(I, Type)  => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <txType> X </txType>
         ...
       </transaction>
  rule [[ getTxnField(I, TypeEnum)  => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <typeEnum> X </typeEnum>
         ...
       </transaction>
  rule [[ getTxnField(I, GroupIndex)  => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <groupIdx> X </groupIdx>
         ...
       </transaction>
  rule [[ getTxnField(I, RekeyTo)  => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <rekeyTo> X </rekeyTo>
         ...
       </transaction>
  rule [[ getTxnField(I, Receiver) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <receiver> X </receiver>
         ...
       </transaction>
  rule [[ getTxnField(I, Amount) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <amount> X </amount>
         ...
       </transaction>
  rule [[ getTxnField(I, CloseRemainderTo) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <closeRemainderTo> X </closeRemainderTo>
         ...
       </transaction>
  rule [[ getTxnField(I, VotePK) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <votePk> X </votePk>
         ...
       </transaction>
  rule [[ getTxnField(I, SelectionPK) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <selectionPK> X </selectionPK>
         ...
       </transaction>
  rule [[ getTxnField(I, VoteFirst) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <voteFirst> X </voteFirst>
         ...
       </transaction>
  rule [[ getTxnField(I, VoteLast) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <voteLast> X </voteLast>
         ...
       </transaction>
  rule [[ getTxnField(I, VoteKeyDilution) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <voteKeyDilution> X </voteKeyDilution>
         ...
       </transaction>
  rule [[ getTxnField(I, XferAsset) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <xferAsset> X </xferAsset>
         ...
       </transaction>
  rule [[ getTxnField(I, AssetAmount) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <assetAmount> X </assetAmount>
         ...
       </transaction>
  rule [[ getTxnField(I, AssetSender) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <assetASender> X </assetASender>
         ...
       </transaction>
  rule [[ getTxnField(I, AssetReceiver) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <assetReceiver> X </assetReceiver>
         ...
       </transaction>
  rule [[ getTxnField(I, AssetCloseTo) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <assetCloseTo> X </assetCloseTo>
         ...
       </transaction>
  rule [[ getTxnField(I, ApplicationID) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <applicationID> X </applicationID>
         ...
       </transaction>
  rule [[ getTxnField(I, OnCompletion) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <onCompletion> X </onCompletion>
         ...
       </transaction>
  rule [[ getTxnField(I, ApplicationArgs, J) => normalize(getTValueAt(J, X)) ]]
       <transaction>
         <txID> I </txID>
         <applicationArgs> X </applicationArgs>
         ...
       </transaction>
    requires 0 <=Int J andBool J <Int size(X)
  rule [[ getTxnField(I, ApplicationArgs) => X ]]
       <transaction>
         <txID> I </txID>
         <applicationArgs> X </applicationArgs>
         ...
       </transaction>
  rule [[ getTxnField(I, NumAppArgs) => size(X) ]]
       <transaction>
         <txID> I </txID>
         <applicationArgs> X </applicationArgs>
         ...
       </transaction>
  rule [[ getTxnField(I, Accounts, 0) => normalize(A) ]]
       <transaction>
         <txID> I </txID>
         <sender> A </sender>
         ...
       </transaction>
  rule [[ getTxnField(I, Accounts, J) => normalize(getTValueAt(J -Int 1, X)) ]]
       <transaction>
         <txID> I </txID>
         <accounts> X </accounts>
         ...
       </transaction>
    requires 0 <Int J andBool J <=Int size(X)
  rule [[ getTxnField(I, Accounts) => (A X) ]]
       <transaction>
         <txID> I </txID>
         <sender> A </sender>
         <accounts> X </accounts>
         ...
       </transaction>
  rule [[ getTxnField(I, NumAccounts) => size(X) ]]
       <transaction>
         <txID> I </txID>
         <accounts> X </accounts>
         ...
       </transaction>
  rule [[ getTxnField(I, ApprovalProgram) => X ]]
       <transaction>
         <txID> I </txID>
         <approvalProgram> X </approvalProgram>
         ...
       </transaction>
  rule [[ getTxnField(I, ClearStateProgram) => X ]]
       <transaction>
         <txID> I </txID>
         <clearStateProgram> X </clearStateProgram>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAsset) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configAsset> X </configAsset>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetTotal) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configTotal> X </configTotal>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetDecimals) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configDecimals> X </configDecimals>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetDefaultFrozen) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configDefaultFrozen> X </configDefaultFrozen>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetUnitName) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configUnitName> X </configUnitName>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetName) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configAssetName> X </configAssetName>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetURL) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configAssetURL> X </configAssetURL>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetMetaDataHash) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configMetaDataHash> X </configMetaDataHash>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetManager) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configManagerAddr> X </configManagerAddr>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetReserve) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configReserveAddr> X </configReserveAddr>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetFreeze) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configFreezeAddr> X </configFreezeAddr>
         ...
       </transaction>
  rule [[ getTxnField(I, ConfigAssetClawback) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <configClawbackAddr> X </configClawbackAddr>
         ...
       </transaction>
  rule [[ getTxnField(I, FreezeAsset) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <freezeAsset> X </freezeAsset>
         ...
       </transaction>
  rule [[ getTxnField(I, FreezeAssetAccount) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <freezeAccount> X </freezeAccount>
         ...
       </transaction>
  rule [[ getTxnField(I, FreezeAssetFrozen) => normalize(X) ]]
       <transaction>
         <txID> I </txID>
         <assetFrozen> X </assetFrozen>
         ...
       </transaction>
  rule [[ getTxnField(I, Applications, 0) => normalize(A) ]]
       <transaction>
         <txID> I </txID>
         ...
       </transaction>
       <currentApplicationID> A </currentApplicationID>
  rule [[ getTxnField(I, Applications, J) => normalize(getTValueAt(J -Int 1, X)) ]]
       <transaction>
         <txID> I </txID>
         <foreignApps> X </foreignApps>
         ...
       </transaction>
    requires 0 <=Int J andBool J <=Int size(X)
  rule [[ getTxnField(I, Applications) => (A X) ]]
       <transaction>
         <txID> I </txID>
         <foreignApps> X </foreignApps>
         ...
       </transaction>
       <currentApplicationID> A </currentApplicationID>
  rule [[ getTxnField(I, Assets, J) => normalize(getTValueAt(J, X)) ]]
       <transaction>
         <txID> I </txID>
         <foreignAssets> X </foreignAssets>
         ...
       </transaction>
    requires 0 <=Int J andBool J <Int size(X)
  rule [[ getTxnField(I, Assets) => X ]]
       <transaction>
         <txID> I </txID>
         <foreignAssets> X </foreignAssets>
         ...
       </transaction>
  rule [[ getTxnField(I, NumAssets) => size(X) ]]
       <transaction>
         <txID> I </txID>
         <foreignAssets> X </foreignAssets>
         ...
       </transaction>
  rule [[ getTxnField(I, LastLog) => MSG ]]
       <transaction>
         <txID> I </txID>
         <logData> _ MSG:TBytes </logData>
         ...
       </transaction>
  rule [[ getTxnField(I, LastLog) => MSG ]]
       <transaction>
         <txID> I </txID>
         <logData> MSG:TBytes </logData>
         ...
       </transaction>
  rule [[ getTxnField(I, NumLogs) => size(LOGS) ]]
       <transaction>
         <txID> I </txID>
         <logData> LOGS </logData>
         ...
       </transaction>
  rule [[ getTxnField(I, Logs, J) => normalize(getTValueAt(J, LOGS)) ]]
       <transaction>
         <txID> I </txID>
         <logData> LOGS </logData>
         ...
       </transaction>
  rule [[ getTxnField(I, Logs) => LOGS ]]
       <transaction>
         <txID> I </txID>
         <logData> LOGS </logData>
         ...
       </transaction>
  rule [[ getTxnField(I, CreatedApplicationID) => CREATED_APP ]]
       <transaction>
         <txID> I </txID>
         <txApplicationID> CREATED_APP </txApplicationID>
         ...
       </transaction>
  rule [[ getTxnField(I, CreatedAssetID) => CREATED_ASSET ]]
       <transaction>
         <txID> I </txID>
         <txConfigAsset> CREATED_ASSET </txConfigAsset>
         ...
       </transaction>
  rule getTxnField(_, _:TxnaField    ) => .TValueList             [owise]
  rule getTxnField(_, FIELD:TxnField ) => getDefaultValue(FIELD)  [owise]
  rule getTxnField(_, _:TxnaField, _ ) => NoTValue                [owise]
  syntax TValue  ::=
    "getDefaultValue" "(" TxnField ")" [function, klabel(getDefaultValue)]
  rule getDefaultValue(Sender)                    => PARAM_ZERO_ADDR
  rule getDefaultValue(Fee)                       => 0
  rule getDefaultValue(FirstValid)                => 0
  rule getDefaultValue(LastValid)                 => 0
  rule getDefaultValue(Note)                      => .Bytes
  rule getDefaultValue(Lease)                     => .Bytes
  rule getDefaultValue(Receiver)                  => PARAM_ZERO_ADDR
  rule getDefaultValue(Amount)                    => 0
  rule getDefaultValue(CloseRemainderTo)          => PARAM_ZERO_ADDR
  rule getDefaultValue(VotePK)                    => PARAM_ZERO_ADDR
  rule getDefaultValue(SelectionPK)               => PARAM_ZERO_ADDR
  rule getDefaultValue(VoteFirst)                 => 0
  rule getDefaultValue(VoteLast)                  => 0
  rule getDefaultValue(VoteKeyDilution)           => 0
  rule getDefaultValue(Type)                      => .Bytes
  rule getDefaultValue(TypeEnum)                  => 0
  rule getDefaultValue(XferAsset)                 => 0
  rule getDefaultValue(AssetAmount)               => 0
  rule getDefaultValue(AssetSender)               => PARAM_ZERO_ADDR
  rule getDefaultValue(AssetReceiver)             => PARAM_ZERO_ADDR
  rule getDefaultValue(AssetCloseTo)              => PARAM_ZERO_ADDR
  rule getDefaultValue(GroupIndex)                => 0
  rule getDefaultValue(TxID)                      => .Bytes
  rule getDefaultValue(ApplicationID)             => 0
  rule getDefaultValue(OnCompletion)              => 0
  rule getDefaultValue(NumAppArgs)                => 0
  rule getDefaultValue(NumAccounts)               => 0
  rule getDefaultValue(ApprovalProgram)           => .Bytes
  rule getDefaultValue(ClearStateProgram)         => .Bytes
  rule getDefaultValue(RekeyTo)                   => PARAM_ZERO_ADDR
  rule getDefaultValue(ConfigAsset)               => 0
  rule getDefaultValue(ConfigAssetTotal)          => 0
  rule getDefaultValue(ConfigAssetDecimals)       => 0
  rule getDefaultValue(ConfigAssetDefaultFrozen)  => 0
  rule getDefaultValue(ConfigAssetUnitName)       => .Bytes
  rule getDefaultValue(ConfigAssetName)           => .Bytes
  rule getDefaultValue(ConfigAssetURL)            => .Bytes
  rule getDefaultValue(ConfigAssetMetaDataHash)   => .Bytes
  rule getDefaultValue(ConfigAssetManager)        => PARAM_ZERO_ADDR
  rule getDefaultValue(ConfigAssetReserve)        => PARAM_ZERO_ADDR
  rule getDefaultValue(ConfigAssetFreeze)         => PARAM_ZERO_ADDR
  rule getDefaultValue(ConfigAssetClawback)       => PARAM_ZERO_ADDR
  rule getDefaultValue(FreezeAsset)               => 0
  rule getDefaultValue(FreezeAssetAccount)        => PARAM_ZERO_ADDR
  rule getDefaultValue(FreezeAssetFrozen)         => 0
  rule getDefaultValue(NumAssets)                 => 0
  rule getDefaultValue(NumApplications)           => 0
  rule getDefaultValue(GlobalNumUint)             => 0
  rule getDefaultValue(GlobalNumByteSlice)        => 0
  rule getDefaultValue(LocalNumUint)              => 0
  rule getDefaultValue(LocalNumByteSlice)         => 0
  rule getDefaultValue(ExtraProgramPages)         => 0
  rule getDefaultValue(Nonparticipation)          => 0
  rule getDefaultValue(NumLogs)                   => 0
  rule getDefaultValue(CreatedAssetID)            => 0
  rule getDefaultValue(CreatedApplicationID)      => 0
  rule getDefaultValue(LastLog)                   => .Bytes
  rule getDefaultValue(StateProofPK)              => .Bytes
  rule getDefaultValue(NumApprovalProgramPages)   => 0
  rule getDefaultValue(NumClearStateProgramPages) => 0
  syntax Bool  ::=
    Int "in_calledApps" "(" TransactionsCell ")" [function]
  rule I in_calledApps( <transactions>
                          <transaction>
                            <txnTypeSpecificFields>
                              <appCallTxFields>
                                <applicationID> APP_ID </applicationID> ...
                              </appCallTxFields>
                            </txnTypeSpecificFields> ...
                          </transaction>
                          REST
                        </transactions> )
       => I in_calledApps(<transactions> REST </transactions>)
    requires I =/=K APP_ID
  rule I in_calledApps( <transactions>
                          <transaction>
                            <txnTypeSpecificFields>
                              <appCallTxFields>
                                <applicationID> I </applicationID> ...
                              </appCallTxFields>
                            </txnTypeSpecificFields> ...
                          </transaction>
                          ...
                        </transactions> )
       => true
  rule _ in_calledApps( <transactions> .Bag </transactions> ) => false
  syntax Int  ::=
    "groupSize" "(" String "," TransactionsCell ")" [function, klabel(groupSize)]
  rule groupSize( GROUP_ID,
                  <transactions>
                    <transaction>
                      <groupID> GROUP_ID </groupID>
                      ...
                    </transaction>
                    REST
                  </transactions>)
       => 1 +Int groupSize(GROUP_ID, <transactions> REST </transactions>)
  rule groupSize( GROUP_ID,
                  <transactions>
                    <transaction>
                      <groupID> GROUP_ID' </groupID>
                      ...
                    </transaction>
                    REST
                  </transactions>)
       => groupSize(GROUP_ID, <transactions> REST </transactions>)
    requires GROUP_ID =/=K GROUP_ID'
  rule groupSize( _, <transactions> .Bag </transactions>) => 0
  syntax Bool  ::=
    String "in_txns" "(" TransactionsCell ")" [function]
  rule I in_txns( <transactions>
                    <transaction>
                      <txID> I </txID> ...
                    </transaction> ...
                  </transactions> )
       => true
  rule I in_txns( <transactions>
                    <transaction>
                      <txID> I' </txID> ...
                    </transaction> REST
                  </transactions> )
       => I in_txns( <transactions> REST </transactions> )
    requires I =/=K I'
  rule _ in_txns( <transactions> .Bag </transactions> ) => false
endmodule

module ADDITIONAL-FIELDS
  imports public TEAL-FIELDS
  syntax AssetField  ::=
    "Creator"
  syntax AccountField  ::=
    "Amount"
  | "Round"
  | "PendingRewards"
  | "Rewards"
  | "Status"
  syntax VersionField  ::=
    "Versions"
  | "GenesisID"
  | "GenesisHash"
  syntax TealField  ::=
    AssetHoldingField
  | AssetParamsField
  | AppParamsField
  | AssetField
  | AccountField
  | VersionField
endmodule

module AVM-CONSTANTS
  imports public INT
  imports public BYTES
  syntax Int  ::=
    "PARAM_MIN_BALANCE" [macro]
  | "PARAM_APP_PAGE_FLAT" [macro]
  | "PARAM_APP_OPTIN_FLAT" [macro]
  | "PARAM_MIN_BALANCE_PER_ENTRY" [macro]
  | "PARAM_UINT_MIN_BALANCE" [macro]
  | "PARAM_BYTES_MIN_BALANCE" [macro]
  | "PARAM_MIN_TXN_FEE" [macro]
  | "PARAM_MAX_TXN_LIFE" [macro]
  | "PARAM_MAX_LOG_CALLS" [macro]
  | "PARAM_MAX_LOG_SIZE" [macro]
  | "PARAM_MAX_LOCAL_KEYS" [macro]
  | "PARAM_MAX_GLOBAL_KEYS" [macro]
  | "PARAM_MAX_KEY_SIZE" [macro]
  | "PARAM_MAX_BYTE_VALUE_SIZE" [macro]
  | "PARAM_MAX_SUM_KEY_VALUE_SIZE" [macro]
  | "PARAM_MAX_BOX_SIZE" [macro]
  | "PARAM_DEFAULT_TEAL_VERSION" [macro]
  syntax Bytes  ::=
    "PARAM_ZERO_ADDR" [macro]
  rule PARAM_MIN_BALANCE => 100000
  rule PARAM_APP_PAGE_FLAT => 100000
  rule PARAM_APP_OPTIN_FLAT => 100000
  rule PARAM_MIN_BALANCE_PER_ENTRY => 25000
  rule PARAM_UINT_MIN_BALANCE => 3500
  rule PARAM_BYTES_MIN_BALANCE => 25000
  rule PARAM_MIN_TXN_FEE => 1000
  rule PARAM_MAX_TXN_LIFE => 1000
  rule PARAM_MAX_LOG_CALLS => 32
  rule PARAM_MAX_LOG_SIZE => 1024
  rule PARAM_MAX_GLOBAL_KEYS => 64
  rule PARAM_MAX_LOCAL_KEYS => 16
  rule PARAM_MAX_KEY_SIZE => 64
  rule PARAM_MAX_BYTE_VALUE_SIZE => 128
  rule PARAM_MAX_SUM_KEY_VALUE_SIZE => 128
  rule PARAM_MAX_BOX_SIZE => 32768
  rule PARAM_DEFAULT_TEAL_VERSION => 8
  rule PARAM_ZERO_ADDR => b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
endmodule

module GLOBALS
  imports public TEAL-CONSTANTS
  imports public TEAL-FIELDS
  imports public TEAL-TYPES
  imports public AVM-CONSTANTS
  syntax TValue  ::=
    "getGlobalField" "(" GlobalField ")" [function, klabel(getGlobalField)]
  rule getGlobalField(MinTxnFee)       => PARAM_MIN_TXN_FEE
  rule getGlobalField(MinBalance)      => PARAM_MIN_BALANCE
  rule getGlobalField(MaxTxnLife)      => PARAM_MAX_TXN_LIFE
  rule getGlobalField(ZeroAddress)     => b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
  rule getGlobalField(LogicSigVersion) => 2
  configuration <globals>
      <groupSize>                 0 </groupSize>
      <globalRound>               0 </globalRound>
      <latestTimestamp>           0 </latestTimestamp>
      <currentApplicationID>      0 </currentApplicationID>
      <currentApplicationAddress> .Bytes </currentApplicationAddress>
      <creatorAddress>            .Bytes </creatorAddress>
    </globals>
  rule [[ getGlobalField(GroupSize) => V ]]
       <globals>
         <groupSize> V </groupSize>
         ...
       </globals>
  rule [[ getGlobalField(Round) => V ]]
       <globals>
         <globalRound> V </globalRound>
         ...
       </globals>
  rule [[ getGlobalField(LatestTimestamp) => V ]]
       <globals>
         <latestTimestamp> V </latestTimestamp>
         ...
       </globals>
  rule [[ getGlobalField(CurrentApplicationID) => V ]]
       <globals>
         <currentApplicationID> V </currentApplicationID>
         ...
       </globals>
  rule [[ getGlobalField(CurrentApplicationAddress) => V ]]
       <globals>
         <currentApplicationAddress> V </currentApplicationAddress>
         ...
       </globals>
  rule [[ getGlobalField(CreatorAddress) => V ]]
       <globals>
         <creatorAddress> V </creatorAddress>
         ...
       </globals>
endmodule

module APPLICATIONS
  imports public ALGO-TXN
  imports public TEAL-SYNTAX
  configuration <appsCreated>
      <app multiplicity="*" type="Map">
        <appID>             NoTValue             </appID>
        <approvalPgmSrc>    (int 0):TealInputPgm </approvalPgmSrc>
        <clearStatePgmSrc>  (int 1):TealInputPgm </clearStatePgmSrc>
        <approvalPgm>       NoTValue             </approvalPgm>
        <clearStatePgm>     NoTValue             </clearStatePgm>
        <globalState>
          <globalNumInts>   NoTValue             </globalNumInts>
          <globalNumBytes>  NoTValue             </globalNumBytes>
          <globalBytes>     .Map                 </globalBytes>
          <globalInts>      .Map                 </globalInts>
        </globalState>
        <localState>
          <localNumInts>    NoTValue             </localNumInts>
          <localNumBytes>   NoTValue             </localNumBytes>
        </localState>
        <extraPages>        NoTValue             </extraPages>
      </app>
    </appsCreated>
  configuration <appsOptedIn>
      <optInApp multiplicity="*" type="Map">
        <optInAppID>   NoTValue </optInAppID>
        <localInts> .Map    </localInts>
        <localBytes> .Map    </localBytes>
      </optInApp>
    </appsOptedIn>
endmodule

module ASSETS
  imports public ALGO-TXN
  configuration <assetsCreated>
      <asset multiplicity="*" type="Map">
        <assetID>            NoTValue </assetID>
        <assetName>          NoTValue </assetName>
        <assetUnitName>      NoTValue </assetUnitName>
        <assetTotal>         NoTValue </assetTotal>
        <assetDecimals>      NoTValue </assetDecimals>
        <assetDefaultFrozen> NoTValue </assetDefaultFrozen>
        <assetURL>           NoTValue </assetURL>
        <assetMetaDataHash>  NoTValue </assetMetaDataHash>
        <assetManagerAddr>   NoTValue </assetManagerAddr>
        <assetReserveAddr>   NoTValue </assetReserveAddr>
        <assetFreezeAddr>    NoTValue </assetFreezeAddr>
        <assetClawbackAddr>  NoTValue </assetClawbackAddr>
      </asset>
    </assetsCreated>
  configuration <assetsOptedIn>
      <optInAsset multiplicity="*" type="Map">
        <optInAssetID>      NoTValue </optInAssetID>
        <optInAssetBalance> NoTValue </optInAssetBalance>
        <optInAssetFrozen>  NoTValue </optInAssetFrozen>
      </optInAsset>
    </assetsOptedIn>
endmodule

module ALGO-BLOCKCHAIN
  imports public GLOBALS
  imports public APPLICATIONS
  imports public ASSETS
  imports public ADDITIONAL-FIELDS
  imports public TEAL-TYPES-SYNTAX
  imports public MAP
  configuration <blockchain>
      <accountsMap>
        <account multiplicity="*" type="Map">
          <address>    "":TBytes </address>
          <balance>    0                  </balance>
          <minBalance> PARAM_MIN_BALANCE  </minBalance> // the default min balance is 0.1 Algo
          <round>      0                  </round>
          <preRewards> 0                  </preRewards>
          <rewards>    0                  </rewards>
          <status>     0                  </status>
          <key>        "":TBytes </key>
          <appsCreated/>
          <appsOptedIn/>
          <assetsCreated/>
          <assetsOptedIn/>
          <boxes>
            <box multiplicity="*" type="Map">
              <boxName> .Bytes </boxName>
              <boxData> .Bytes </boxData>
            </box>
          </boxes>
        </account>
      </accountsMap>
      <appCreator>   .Map </appCreator>   // AppID |-> Creator's address
      <assetCreator> .Map </assetCreator> // AssetID |-> Creator's address
      <blocks>       .Map </blocks>       // Int -> Block (Unused)
      <blockheight>  0    </blockheight>
      <nextAssetID>  1    </nextAssetID>
      <nextAppID>    1    </nextAppID>
      <nextTxnID>    0    </nextTxnID>
      <nextGroupID>  1    </nextGroupID>
      <txnIndexMap>
        <txnIndexMapGroup multiplicity="*" type="Map">
          <txnIndexMapGroupKey> "":String </txnIndexMapGroupKey>
          <txnIndexMapGroupValues> .Map </txnIndexMapGroupValues> // GroupIdx (offset) |-> Transaction ID
        </txnIndexMapGroup>
      </txnIndexMap>
    </blockchain>
  syntax String  ::=
    "getCurrentTxn" "(" ")" [function, klabel(getCurrentTxn)]
  syntax MaybeTValue  ::=
    "getAccountParamsField" "(" AccountParamsField "," TValue ")" [function, klabel(getAccountParamsField), total]
  rule [[ getAccountParamsField(AcctBalance, ADDR) => BAL ]]
       <account>
         <address> ADDR </address>
         <balance> BAL </balance>
         ...
       </account>
  rule [[ getAccountParamsField(AcctMinBalance, ADDR) => MIN_BAL ]]
       <account>
         <address> ADDR </address>
         <minBalance> MIN_BAL </minBalance>
         ...
       </account>
  rule [[ getAccountParamsField(AcctAuthAddr, ADDR) => KEY ]]
       <account>
         <address> ADDR </address>
         <key> KEY </key>
         ...
       </account>
  rule getAccountParamsField(_, _) => NoTValue   [owise]
  syntax MaybeTValue  ::=
    "getAppParamsField" "(" AppParamsField "," Int ")" [function, klabel(getAppParamsField), total]
  rule [[ getAppParamsField(AppApprovalProgram, APP) => X ]]
       <app>
         <appID> APP </appID>
         <approvalPgm> X </approvalPgm>
         ...
       </app>
  rule [[ getAppParamsField(AppClearStateProgram, APP) => X ]]
       <app>
         <appID> APP </appID>
         <clearStatePgm> X </clearStatePgm>
         ...
       </app>
  rule [[ getAppParamsField(AppGlobalNumUint, APP) => X ]]
       <app>
         <appID> APP </appID>
         <globalNumInts> X </globalNumInts>
         ...
       </app>
  rule [[ getAppParamsField(AppGlobalNumByteSlice, APP) => X ]]
       <app>
         <appID> APP </appID>
         <globalNumBytes> X </globalNumBytes>
         ...
       </app>
  rule [[ getAppParamsField(AppLocalNumUint, APP) => X ]]
       <app>
         <appID> APP </appID>
         <localNumInts> X </localNumInts>
         ...
       </app>
  rule [[ getAppParamsField(AppLocalNumByteSlice, APP) => X ]]
       <app>
         <appID> APP </appID>
         <localNumBytes> X </localNumBytes>
         ...
       </app>
  rule [[ getAppParamsField(AppExtraProgramPages, APP) => X ]]
       <app>
         <appID> APP </appID>
         <extraPages> X </extraPages>
         ...
       </app>
  rule [[ getAppParamsField(AppCreator, APP) => X ]]
       <account>
         <address> X </address>
         <appsCreated>
           <app>
             <appID> APP </appID>
             <extraPages> X </extraPages>
             ...
           </app>
           ...
         </appsCreated>
         ...
       </account>
  rule [[ getAppParamsField(AppAddress, APP) => getAppAddressBytes(APP) ]]
       <accountsMap> AM </accountsMap>
    requires APP in_apps(<accountsMap> AM </accountsMap>)
  rule getAppParamsField(_, _) => NoTValue  [owise]
  syntax MaybeTValue  ::=
    "getAccountField" "(" AccountField "," TValue ")" [function, klabel(getAccountField)]
  rule getAccountField(Amount, ADDR) => getAccountParamsField(AcctBalance, ADDR)
  rule [[ getAccountField(Round, ADDR) => V ]]
       <account>
         <address> ADDR </address>
         <round> V </round>
         ...
       </account>
  rule [[ getAccountField(PendingRewards, ADDR) => V ]]
       <account>
         <address> ADDR </address>
         <preRewards> V </preRewards>
         ...
       </account>
  rule [[ getAccountField(Rewards, ADDR) => V ]]
       <account>
         <address> ADDR </address>
         <rewards> V </rewards>
         ...
       </account>
  rule [[ getAccountField(Status, ADDR) => V ]]
       <account>
         <address> ADDR </address>
         <status> V </status>
         ...
       </account>
  rule [[ getAccountField(_, ADDR) => -1 ]]
       <accountsMap> AMAP </accountsMap>
    requires notBool (ADDR in_accounts(<accountsMap> AMAP </accountsMap>))
  syntax Bool  ::=
    "hasOptedInAsset" "(" TValue "," TValue ")" [function, klabel(hasOptedInAsset), total]
  rule [[ hasOptedInAsset(ASSET, ADDR) => true ]]
       <account>
         <address> ADDR </address>
         <assetsOptedIn>
           <optInAsset>
             <optInAssetID> ASSET </optInAssetID> ...
           </optInAsset> ...
         </assetsOptedIn> ...
       </account>
  rule hasOptedInAsset(_, _) => false  [owise]
  syntax TValue  ::=
    "getOptInAssetField" "(" AssetHoldingField "," TValue "," TValue ")" [function, klabel(getOptInAssetField)]
  rule [[ getOptInAssetField(AssetBalance, ADDR, ASSET) => V ]]
       <account>
         <address> ADDR </address>
         <assetsOptedIn>
           <optInAsset>
             <optInAssetID> ASSET </optInAssetID>
             <optInAssetBalance> V </optInAssetBalance> ...
           </optInAsset> ...
         </assetsOptedIn> ...
       </account>
  rule [[ getOptInAssetField(AssetFrozen, ADDR, ASSET) => V ]]
       <account>
         <address> ADDR </address>
         <assetsOptedIn>
           <optInAsset>
             <optInAssetID> ASSET </optInAssetID>
             <optInAssetFrozen>  V </optInAssetFrozen> ...
           </optInAsset> ...
         </assetsOptedIn> ...
       </account>
  rule [[ getOptInAssetField(_, ADDR, ASSET) => -1 ]]
       <account>
         <address> ADDR </address>
         <assetsOptedIn> OA </assetsOptedIn> ...
       </account>
    requires notBool (ASSET in_optedInAssets(<assetsOptedIn> OA </assetsOptedIn>))
  rule [[ getOptInAssetField(_, ADDR, _) => -1 ]]
       <accountsMap> AMAP </accountsMap>
    requires notBool (ADDR in_accounts(<accountsMap> AMAP </accountsMap>))
  syntax Bool  ::=
    "assetCreated" "(" TValue ")" [function, klabel(assetCreated)]
  rule [[ assetCreated(ASSET) => true ]]
       <assetCreator> AC </assetCreator>
    requires ASSET in_keys(AC)
  rule [[ assetCreated(ASSET) => false ]]
       <assetCreator> AC </assetCreator>
    requires notBool (ASSET in_keys(AC))
  syntax TValue  ::=
    "getAssetInfo" "(" AssetField "," TValue ")" [function, klabel(getAssetInfo)]
  rule [[ getAssetInfo(Creator, ASSET) => V ]]
       <assetCreator> ASSET |-> V ... </assetCreator>
  rule [[ getAssetInfo(Creator, ASSET) => -1 ]]
       <assetCreator> AMap </assetCreator>
    requires notBool (ASSET in_keys(AMap))
  syntax TValue  ::=
    "getAssetParamsField" "(" AssetParamsField "," TValue ")" [function, klabel(getAssetParamsField)]
  rule [[ getAssetParamsField(AssetTotal, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetTotal> V </assetTotal> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetDecimals, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetDecimals> V </assetDecimals> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetDefaultFrozen, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetDefaultFrozen> V </assetDefaultFrozen> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetUnitName, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetUnitName> V </assetUnitName> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetName, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetName> V </assetName> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetURL, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetURL> V </assetURL> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetMetadataHash, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetMetaDataHash> V </assetMetaDataHash> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetManager, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetManagerAddr> V </assetManagerAddr> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetReserve, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetReserveAddr> V </assetReserveAddr> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetFreeze, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetFreezeAddr> V </assetFreezeAddr> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetClawback, ASSET) => V ]]
       <assetsCreated>
         <asset>
           <assetID> ASSET </assetID>
           <assetClawbackAddr> V </assetClawbackAddr> ...
         </asset> ...
       </assetsCreated>
  rule [[ getAssetParamsField(AssetCreator, ASSET) => V ]]
       <assetCreator> ASSET |-> V ...</assetCreator>
  rule [[ getAssetParamsField(_, ASSET) => -1 ]]
      <accountsMap> AMAP </accountsMap>
    requires notBool ( ASSET in_assets(<accountsMap> AMAP </accountsMap>) )
  syntax Bool  ::=
    "hasOptedInApp" "(" TValue "," TValue ")" [function, klabel(hasOptedInApp)]
  rule [[ hasOptedInApp(APP, ADDR) => APP in_optedInApps( <appsOptedIn> O </appsOptedIn> ) ]]
       <account>
         <address> ADDR </address>
         <appsOptedIn> O </appsOptedIn> ...
       </account>
  rule [[ hasOptedInApp(_, ADDR) => false ]]
       <accountsMap> AMAP  </accountsMap>
    requires notBool (ADDR in_accounts(<accountsMap> AMAP </accountsMap>))
  syntax MaybeTValue  ::=
    "getAppLocal" "(" TValue "," TValue "," TValue ")" [function, klabel(getAppLocal), total]
  rule [[ getAppLocal(ADDR, APP, KEY) => V ]]
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localInts> KEY |-> V ... </localInts>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
  rule [[ getAppLocal(ADDR, APP, KEY) => V ]]
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localBytes> KEY |-> V ... </localBytes>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
  rule [[ getAppLocal(ADDR, APP, KEY) => -1 ]]
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localInts> MI </localInts>
             <localBytes> MB </localBytes>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
    requires notBool ((KEY in_keys(MI)) orBool (KEY in_keys(MB)))
  rule getAppLocal(_, _, _) => NoTValue  [owise]
  syntax TValue  ::=
    "getAppGlobal" "(" AppCell "," TValue ")" [function, klabel(getAppGlobal), total]
  rule getAppGlobal(<app>
                      <globalState>
                        <globalInts> GI:Map </globalInts>
                        <globalBytes> GB:Map </globalBytes>
                        ...
                      </globalState>
                      ...
                    </app>, KEY) =>
          {GI[KEY]}:>Int
    requires ((KEY in_keys(GI)) andThenBool (isInt(GI[KEY])))
     andBool notBool (KEY in_keys(GB))
  rule getAppGlobal(<app>
                      <globalState>
                        <globalInts> GI:Map </globalInts>
                        <globalBytes> GB:Map </globalBytes>
                        ...
                      </globalState>
                      ...
                    </app>, KEY) =>
          {GB[KEY]}:>Bytes
    requires ((KEY in_keys(GB)) andThenBool (isBytes(GB[KEY])))
     andBool notBool (KEY in_keys(GI))
  rule getAppGlobal(_, _) => -1  [owise]
  syntax Bool  ::=
    "appCreated" "(" TValue ")" [function, klabel(appCreated)]
  rule [[ appCreated(APP) => true ]]
       <appCreator> APP |-> _ ... </appCreator>
  rule [[ appCreated(APP) => false ]]
       <appCreator> AMap </appCreator>
    requires notBool (APP in_keys(AMap))
  syntax Bool  ::=
    TValue "in_accounts" "(" AccountsMapCell ")" [function]
  rule ADDR in_accounts( <accountsMap>
                           <account>
                             <address> ADDR </address> ...
                           </account> ...
                         </accountsMap> )
       => true
  rule ADDR in_accounts( <accountsMap>
                           <account>
                             <address> ADDR' </address> ...
                           </account> REST
                         </accountsMap> )
       => ADDR in_accounts (<accountsMap> REST </accountsMap>)
    requires ADDR =/=K ADDR'
  rule _ in_accounts( <accountsMap> .Bag </accountsMap> ) => false
  syntax Bool  ::=
    Bytes "in_boxes" "(" BoxesCell ")" [function]
  rule NAME in_boxes(
              <boxes>
                <box>
                  <boxName> NAME </boxName>
                  ...
                </box>
                ...
              </boxes>
            ) => true
  rule NAME in_boxes(
              <boxes>
                <box>
                  <boxName> NAME' </boxName>
                  ...
                </box>
                REST
              </boxes>
            ) => NAME in_boxes(<boxes> REST </boxes>)
    requires NAME =/=K NAME'
  rule _ in_boxes(<boxes> .Bag </boxes>) => false
  syntax Bool  ::=
    TValue "in_optedInApps" "(" AppsOptedInCell ")" [function]
  rule APP in_optedInApps(
             <appsOptedIn>
               <optInApp>
                 <optInAppID> APP </optInAppID> ...
               </optInApp> ...
             </appsOptedIn>) => true
  rule APP in_optedInApps(
             <appsOptedIn>
               <optInApp>
                 <optInAppID> APP' </optInAppID> ...
               </optInApp> REST
             </appsOptedIn>) => APP in_optedInApps(<appsOptedIn> REST </appsOptedIn>)
    requires APP =/=K APP'
  rule _ in_optedInApps(<appsOptedIn> .Bag </appsOptedIn>) => false
  syntax Bool  ::=
    TValue "in_optedInAssets" "(" AssetsOptedInCell ")" [function]
  rule ASSET in_optedInAssets(<assetsOptedIn>
                       <optInAsset>
                         <optInAssetID> ASSET </optInAssetID> ...
                       </optInAsset> ...
                     </assetsOptedIn>) => true
  rule ASSET in_optedInAssets(<assetsOptedIn>
                       <optInAsset>
                         <optInAssetID> ASSET' </optInAssetID> ...
                       </optInAsset> REST
                     </assetsOptedIn>)
       => ASSET in_optedInAssets(<assetsOptedIn> REST </assetsOptedIn>)
    requires ASSET =/=K ASSET'
  rule _ in_optedInAssets(<assetsOptedIn> .Bag </assetsOptedIn>) => false
  syntax Bool  ::=
    TValue "in_assets" "(" AccountsMapCell ")" [function]
  rule ASSET in_assets(<accountsMap>
                         <account>
                           <assetsCreated> ASSETS </assetsCreated> ...
                         </account> REST
                       </accountsMap> )
       => ASSET in_assets (<assetsCreated> ASSETS </assetsCreated>)
          orBool ASSET in_assets ( <accountsMap> REST </accountsMap> )
  rule _ in_assets( <accountsMap> .Bag </accountsMap> ) => false
  syntax Bool  ::=
    TValue "in_assets" "(" AssetsCreatedCell ")" [function]
  rule ASSET in_assets(<assetsCreated>
                         <asset>
                           <assetID> ASSET </assetID> ...
                         </asset> ...
                       </assetsCreated> ) => true
  rule ASSET in_assets(<assetsCreated>
                         <asset>
                           <assetID> ASSET' </assetID> ...
                         </asset> REST
                       </assetsCreated> )
       => ASSET in_assets(<assetsCreated> REST </assetsCreated>)
    requires ASSET =/=K ASSET'
  rule _ in_assets(<assetsCreated> .Bag </assetsCreated>) => false
  syntax Bool  ::=
    TValue "in_apps" "(" AccountsMapCell ")" [function, total]
  rule APP in_apps(<accountsMap>
                     <account>
                       <appsCreated> APPS </appsCreated> ...
                     </account> REST
                   </accountsMap> )
       => APP in_apps (<appsCreated> APPS </appsCreated>)
          orBool APP in_apps ( <accountsMap> REST </accountsMap> )
  rule _ in_apps( <accountsMap> .Bag </accountsMap> ) => false
  syntax Bool  ::=
    TValue "in_apps" "(" AppsCreatedCell ")" [function, total]
  rule APP in_apps(<appsCreated>
                     <app>
                       <appID> APP </appID> ...
                     </app> ...
                   </appsCreated> ) => true
  rule APP in_apps(<appsCreated>
                     <app>
                       <appID> APP' </appID> ...
                     </app> REST
                   </appsCreated> )
       => APP in_apps(<appsCreated> REST </appsCreated>)
    requires APP =/=K APP'
  rule _ in_apps(<appsCreated> .Bag </appsCreated>) => false
  syntax Bool  ::=
    String "in_transactions" "(" TransactionsCell ")" [function, total]
  rule TXN_ID in_transactions(<transactions>
                                <transaction>
                                  <txID> TXN_ID </txID> ...
                                </transaction> ...
                              </transactions> ) => true
  rule TXN_ID in_transactions(<transactions>
                                <transaction>
                                  <txID> TXN_ID' </txID> ...
                                </transaction> REST
                              </transactions>)
       => TXN_ID in_transactions(<transactions> REST </transactions>)
    requires TXN_ID =/=K TXN_ID'
  rule _ in_transactions(<transactions> .Bag </transactions>) => false
  syntax MaybeTValue  ::=
    "accountReference" "(" TValue ")" [function, klabel(accountReference), total]
  rule accountReference(A:TBytes ) => A requires accountAvailable(A)
  rule accountReference(I:Int    ) => getTxnField(getCurrentTxn(), Accounts, I)
  rule accountReference(_        ) => NoTValue   [owise]
  syntax MaybeTValue  ::=
    "appReference" "(" TUInt64 ")" [function, klabel(appReference), total]
  rule appReference(I) => I requires applicationAvailable(I)
  rule appReference(I) => getTxnField(getCurrentTxn(), Applications, I)   [owise]
  syntax MaybeTValue  ::=
    "asaReference" "(" TUInt64 ")" [function, klabel(asaReference), total]
  rule asaReference(I) => I requires assetAvailable(I)
  rule asaReference(I) => getTxnField(getCurrentTxn(), Assets, I)   [owise]
  syntax Bool  ::=
    "accountAvailable" "(" TBytes ")" [function, klabel(accountAvailable), total]
  rule accountAvailable(A) => true
    requires contains(getTxnField(getCurrentTxn(), Accounts), A)
  rule accountAvailable(A) => true
    requires A ==K getTxnField(getCurrentTxn(), Sender)
  rule accountAvailable(A) => true
    requires A ==K getGlobalField(CurrentApplicationAddress)
  rule accountAvailable(_) => false  [owise]
  syntax Bool  ::=
    "applicationAvailable" "(" TUInt64 ")" [function, klabel(applicationAvailable), total]
  rule applicationAvailable(A) => true
    requires contains(getTxnField(getCurrentTxn(), Applications), A)
  rule applicationAvailable(A) => true
    requires A ==K getGlobalField(CurrentApplicationID)
  rule applicationAvailable(_) => false  [owise]
  syntax Bool  ::=
    "assetAvailable" "(" TUInt64 ")" [function, klabel(assetAvailable), total]
  rule assetAvailable(A) => true
    requires contains(getTxnField(getCurrentTxn(), Assets), A)
  rule assetAvailable(_) => false  [owise]
  syntax Map  ::=
    "TValuePairList2Map" "(" TValuePairList "," TValueList "," Bytes ")" [function, klabel(TValuePairList2Map), total]
  rule TValuePairList2Map((A, B):TValuePair REST, APPS, DEFAULT) => ((A |-> getAppAddressBytes({getTValueAt(B -Int 1, APPS)}:>Int)) TValuePairList2Map(REST, APPS, DEFAULT))
    requires B >=Int 1
  rule TValuePairList2Map((A, B):TValuePair, APPS, _) => (A |-> getAppAddressBytes({getTValueAt(B -Int 1, APPS)}:>Int))
    requires B >=Int 1
  rule TValuePairList2Map((A, 0):TValuePair REST, APPS, DEFAULT) => ((A |-> DEFAULT) TValuePairList2Map(REST, APPS, DEFAULT))
  rule TValuePairList2Map((A, 0):TValuePair, _, DEFAULT) => (A |-> DEFAULT)
  rule TValuePairList2Map(.TValuePairList, _, _) => .Map
  syntax Map  ::=
    "getBoxRefs" "(" String ")" [function, klabel(getBoxRefs), total]
  syntax Map  ::=
    "getGroupBoxRefs" "(" String ")" [function, klabel(getGroupBoxRefs), total]
  syntax Map  ::=
    "getGroupBoxRefs" "(" Map ")" [function, klabel(getGroupBoxRefs), total]
  rule [[ getGroupBoxRefs(GROUP_ID) => getGroupBoxRefs(VALS) ]]
       <txnIndexMapGroup>
         <txnIndexMapGroupKey> GROUP_ID </txnIndexMapGroupKey>
         <txnIndexMapGroupValues> VALS </txnIndexMapGroupValues>
       </txnIndexMapGroup>
  rule getGroupBoxRefs( (_ |-> TXN_ID) REST) => getGroupBoxRefs(REST) getBoxRefs(TXN_ID)
  rule getGroupBoxRefs( .Map) => .Map
  rule [[ getBoxRefs(TXN_ID) => TValuePairList2Map(REFS, FA, getAppAddressBytes({getGlobalField(CurrentApplicationID)}:>Int)) ]]
       <transaction>
         <txID> TXN_ID </txID>
         <foreignApps> FA </foreignApps>
         <boxReferences> REFS </boxReferences>
         ...
       </transaction>
  rule [[ getBoxRefs(TXN_ID) => .Map ]]
       <transaction>
         <txID> TXN_ID </txID>
         <txnTypeSpecificFields>
           .AppCallTxFieldsCell
           ...
         </txnTypeSpecificFields>
         ...
       </transaction>
  syntax MaybeTValue  ::=
    "boxAcct" "(" Bytes ")" [function, klabel(boxAcct), total]
  rule boxAcct(NAME) => {getGroupBoxRefs(getTxnGroupID(getCurrentTxn()))[NAME]}:>Bytes
    requires NAME in_keys(getGroupBoxRefs(getTxnGroupID(getCurrentTxn())))
  rule boxAcct(_) => NoTValue  [owise]
  syntax MaybeTValue  ::=
    "getGroupFieldByIdx" "(" String "," Int "," TxnField ")" [function, klabel(getGroupFieldByIdx)]
  syntax MaybeTValue  ::=
    "getGroupFieldByIdx" "(" String "," Int "," TxnaField "," Int ")" [function, klabel(getGroupFieldByIdx)]
  rule [[ getGroupFieldByIdx(GROUP_ID, GROUP_INDEX, FIELD) => getTxnField({MV[GROUP_INDEX]}:>String, FIELD) ]]
        <txnIndexMapGroup>
          <txnIndexMapGroupKey> GROUP_ID </txnIndexMapGroupKey>
          <txnIndexMapGroupValues> MV </txnIndexMapGroupValues>
        </txnIndexMapGroup>
  rule [[ getGroupFieldByIdx(GROUP_ID, GROUP_INDEX, FIELD, FIELD_INDEX) => getTxnField( {MV[GROUP_INDEX]}:>String, FIELD, FIELD_INDEX) ]]
        <txnIndexMapGroup>
          <txnIndexMapGroupKey> GROUP_ID </txnIndexMapGroupKey>
          <txnIndexMapGroupValues> MV </txnIndexMapGroupValues>
        </txnIndexMapGroup>
  rule getGroupFieldByIdx(_, _, _) => NoTValue  [owise]
endmodule

module TEAL-STACK
  imports public INT
  imports public BOOL
  imports public TEAL-TYPES-SYNTAX
  syntax TStack  ::=
    ".TStack" [klabel(.TStack), smtlib(_dotTStack), symbol]
  | TValue ":" TStack [klabel(_:_TStack), smtlib(_TStack_)]
  syntax TStack  ::=
    "#take" "(" Int "," TStack ")" [function, klabel(takeTStack), total]
  rule [#take.zero]: #take(N, _Stack)          => .TStack
    requires N <=Int 0
  rule [#take.base]: #take(N, .TStack)         => .TStack
    requires N >Int 0
  rule [#take.recursive]: #take(N, (X : XS):TStack) => X : #take(N -Int 1, XS)
    requires N >Int 0
  syntax TStack  ::=
    "#drop" "(" Int "," TStack ")" [function, klabel(dropTStack), total]
  rule #drop(N, XS:TStack)       => XS
    requires N <=Int 0
  rule #drop(N, .TStack)         => .TStack
    requires N >Int 0
  rule #drop(N, (_ : XS):TStack) => #drop(N -Int 1, XS)
      requires N >Int 0
  syntax TValue  ::=
    TStack "[" Int "]" [function]
  rule (X : _):TStack [ N ] => X                  requires N ==Int 0
  rule XS             [ N ] => #drop(N, XS) [ 0 ] requires N  >Int 0
                                                   andBool N  <Int #sizeTStack(XS)
  syntax TValue  ::=
    TStack "{" Int "}" [function]
  rule (X : XS):TStack { N } => X
    requires N ==Int #sizeTStack(XS)
  rule XS              { N } => #drop((#sizeTStack(XS) -Int N) -Int 1, XS) [ 0 ]
    requires N  <Int #sizeTStack(XS)
  syntax TStack  ::=
    TStack "{" Int "<-" TValue "}" [function]
  rule XS:TStack { N <- M } => #take((#sizeTStack(XS) -Int N) -Int 1, XS) M : #drop(#sizeTStack(XS) -Int N, XS)
  syntax Int  ::=
    "#sizeTStack" "(" TStack ")" [function, klabel(#sizeTStack), smtlib(sizeTStack), total]
  | "#sizeTStack" "(" TStack "," Int ")" [function, klabel(sizeTStackAux), smtlib(sizeTStackAux), total]
  rule #sizeTStack ( XS ) => #sizeTStack(XS, 0)
  rule #sizeTStack ( .TStack, SIZE ) => SIZE
  rule #sizeTStack ( _ : XS, SIZE )     => #sizeTStack(XS, SIZE +Int 1)
  syntax TStack  ::=
    "#reverse" "(" TStack ")" [function, klabel(#reverse), total]
  | "#reverse" "(" TStack "," TStack ")" [function, klabel(#reverse), total]
  rule #reverse(XS)          => #reverse(XS, .TStack)
  rule #reverse(.TStack, YS) => YS
  rule #reverse(X : XS , YS) => #reverse(XS, X : YS)
  syntax TStack  ::=
    TStack TStack [function, total]
  | "#concatTStackImpl" "(" TStack "," TStack ")" [function, klabel(#concatTStackImpl), total]
  rule XS YS => #concatTStackImpl(#reverse(XS), YS)
  rule #concatTStackImpl(.TStack, YS) => YS
  rule #concatTStackImpl(X : XS , YS) => #concatTStackImpl(XS, X : YS)
endmodule

module AVM-PANIC
  imports public STRING
  imports public INT
  imports public AVM-CONFIGURATION
  syntax Int  ::=
    "SUCCESS" [macro]
  | "ZERO_STACK" [macro]
  | "BAD_STACK" [macro]
  | "INTERNAL_ERROR" [macro]
  | "STUCK" [macro]
  | "INVALID_JSON" [macro]
  syntax Int  ::=
    "INVALID_OP_FOR_MODE" [macro]
  | "ERR_OPCODE" [macro]
  | "INT_OVERFLOW" [macro]
  | "INT_UNDERFLOW" [macro]
  | "DIV_BY_ZERO" [macro]
  | "BYTES_OVERFLOW" [macro]
  | "TXN_ACCESS_FAILED" [macro]
  | "TXN_INVALID" [macro]
  | "INVALID_SCRATCH_LOC" [macro]
  | "TXN_OUT_OF_BOUNDS" [macro]
  | "FUTURE_TXN" [macro]
  | "INDEX_OUT_OF_BOUNDS" [macro]
  | "ILLEGAL_JUMP" [macro]
  | "ILL_TYPED_STACK" [macro]
  | "LOG_CALLS_EXCEEDED" [macro]
  | "LOG_SIZE_EXCEEDED" [macro]
  | "GLOBAL_BYTES_EXCEEDED" [macro]
  | "GLOBAL_INTS_EXCEEDED" [macro]
  | "LOCAL_BYTES_EXCEEDED" [macro]
  | "LOCAL_INTS_EXCEEDED" [macro]
  | "STACK_OVERFLOW" [macro]
  | "STACK_UNDERFLOW" [macro]
  | "ASSERTION_VIOLATION" [macro]
  | "IMPOSSIBLE_NEGATIVE_NUMBER" [macro]
  | "DUPLICATE_LABEL" [macro]
  | "CALLSTACK_UNDERFLOW" [macro]
  | "CALLSTACK_OVERFLOW" [macro]
  | "INVALID_ARGUMENT" [macro]
  | "ITXN_REENTRY" [macro]
  | "MATH_BYTES_ARG_TOO_LONG" [macro]
  | "INSUFFICIENT_FUNDS" [macro]
  | "KEY_TOO_LARGE" [macro]
  | "BYTE_VALUE_TOO_LARGE" [macro]
  | "KEY_VALUE_TOO_LARGE" [macro]
  | "BOX_TOO_LARGE" [macro]
  | "CHANGED_BOX_SIZE" [macro]
  | "BOX_NOT_FOUND" [macro]
  | "BOX_UNAVAILABLE" [macro]
  | "BOX_WRONG_LENGTH" [macro]
  | "BOX_OUT_OF_BOUNDS" [macro]
  | "BOX_CREATE_EXTERNAL" [macro]
  | "MIN_BALANCE_VIOLATION" [macro]
  | "UNSUPPORTED_TXN_TYPE" [macro]
  | "ASSET_FROZEN" [macro]
  | "ASSET_NOT_OPT_IN" [macro]
  | "UNKNOWN_ADDRESS" [macro]
  | "ASSET_NO_PERMISSION" [macro]
  | "TXN_DEQUE_ERROR" [macro]
  | "ASSET_NOT_FOUND" [macro]
  | "MISSING_APP_CREATOR" [macro]
  | "APP_ALREADY_ACTIVE" [macro]
  | "INSUFFICIENT_ASSET_BALANCE" [macro]
  syntax String  ::=
    "returnDesc" "(" Int ")" [function, klabel(returnDesc)]
  rule returnDesc(SUCCESS)                    => "success"
  rule returnDesc(ZERO_STACK)                 => "stack contained 0 at end of execution"
  rule returnDesc(BAD_STACK)                  => "stack contained no values, multiple values, or bytes at end of execution"
  rule returnDesc(STUCK)                      => "k execution stuck"
  rule returnDesc(INVALID_JSON)              => "invalid json"
  rule returnDesc(INVALID_OP_FOR_MODE)        => "invalid opcode for current execution mode"
  rule returnDesc(ERR_OPCODE)                 => "err opcode encountered"
  rule returnDesc(INT_OVERFLOW)               => "integer overflow"
  rule returnDesc(INT_UNDERFLOW)              => "integer underflow"
  rule returnDesc(DIV_BY_ZERO)                => "division by zero"
  rule returnDesc(BYTES_OVERFLOW)             => "resulting byte array too large"
  rule returnDesc(TXN_ACCESS_FAILED)          => "transaction field access failed"
  rule returnDesc(TXN_INVALID)                => "a transaction is malformed"
  rule returnDesc(INVALID_SCRATCH_LOC)        => "invalid scratch space location"
  rule returnDesc(TXN_OUT_OF_BOUNDS)          => "transaction index out of bounds"
  rule returnDesc(FUTURE_TXN)                 => "tried to access transaction that hasn't executed yet"
  rule returnDesc(INDEX_OUT_OF_BOUNDS)        => "array index out of bounds"
  rule returnDesc(ILLEGAL_JUMP)               => "illegal branch to a non-existing label"
  rule returnDesc(ILL_TYPED_STACK)            => "wrong argument type(s) for opcode"
  rule returnDesc(LOG_CALLS_EXCEEDED)         => "too many log calls in transaction"
  rule returnDesc(LOG_SIZE_EXCEEDED)          => "total size of log calls in transaction is too large"
  rule returnDesc(GLOBAL_BYTES_EXCEEDED)      => "tried to store too many byte values in global storage"
  rule returnDesc(GLOBAL_INTS_EXCEEDED)       => "tried to store too many int values in global storage"
  rule returnDesc(LOCAL_BYTES_EXCEEDED)       => "tried to store too many byte values in local storage"
  rule returnDesc(LOCAL_INTS_EXCEEDED)        => "tried to store too many int values in local storage"
  rule returnDesc(INVALID_ARGUMENT)           => "wrong argument range(s) for opcode"
  rule returnDesc(STACK_OVERFLOW)             => "stack overflow"
  rule returnDesc(STACK_UNDERFLOW)            => "stack underflow"
  rule returnDesc(ASSERTION_VIOLATION)        => "assertion violation"
  rule returnDesc(DUPLICATE_LABEL)            => "duplicate label"
  rule returnDesc(IMPOSSIBLE_NEGATIVE_NUMBER) => "impossible happened: negative number on stack"
  rule returnDesc(CALLSTACK_UNDERFLOW)        => "call stack underflow: illegal retsub"
  rule returnDesc(CALLSTACK_OVERFLOW)         => "call stack overflow: recursion is too deep"
  rule returnDesc(ITXN_REENTRY)               => "application called from itself"
  rule returnDesc(MATH_BYTES_ARG_TOO_LONG)    => "math attempted on large byte-array"
  rule returnDesc(INSUFFICIENT_FUNDS)         => "negative balance reached"
  rule returnDesc(KEY_TOO_LARGE)              => "key is too long"
  rule returnDesc(BYTE_VALUE_TOO_LARGE)       => "tried to store too large of a byte value"
  rule returnDesc(KEY_VALUE_TOO_LARGE)        => "sum of key length and value length is too high"
  rule returnDesc(ASSERTION_VIOLATION)        => "assertion violation"
  rule returnDesc(BOX_TOO_LARGE)              => "tried to create a box which is too large"
  rule returnDesc(CHANGED_BOX_SIZE)           => "called box_create on existing box with a different size"
  rule returnDesc(BOX_NOT_FOUND)              => "tried to access a box name that doesn't exist"
  rule returnDesc(BOX_UNAVAILABLE)            => "tried to access box not referenced in any transaction in this group"
  rule returnDesc(BOX_WRONG_LENGTH)           => "tried to replace a box byte array with one of a different length"
  rule returnDesc(BOX_OUT_OF_BOUNDS)          => "tried to access out of bounds of a box byte array"
  rule returnDesc(BOX_CREATE_EXTERNAL)        => "tried to create a box for which a reference already exists tied to another application"
  rule returnDesc(MIN_BALANCE_VIOLATION)      => "account's balance falls below its allowed minimum balance"
  rule returnDesc(UNSUPPORTED_TXN_TYPE)       => "attempt to execute an unsupported transaction type"
  rule returnDesc(ASSET_FROZEN)               => "attempt to send frozen asset holdings"
  rule returnDesc(ASSET_NOT_OPT_IN)           => "either sender or receiver have not opted into asset"
  rule returnDesc(UNKNOWN_ADDRESS)            => "address is not in the <accountsMap>"
  rule returnDesc(ASSET_NO_PERMISSION)        => "sender does not have permission to modify asset"
  rule returnDesc(TXN_DEQUE_ERROR)            => "txn deque error"
  rule returnDesc(ASSET_NOT_FOUND)            => "tried to modify an asset which hasn't been created"
  rule returnDesc(MISSING_APP_CREATOR)        => "Found app that is missing for <appCreator>"
  rule returnDesc(APP_ALREADY_ACTIVE)         => "attempt to #initApp that already is in <activeApps>"
  rule returnDesc(INSUFFICIENT_ASSET_BALANCE) => "tried to transfer more of an asset than owned"
  rule SUCCESS                    => 0
  rule ZERO_STACK                 => 1
  rule BAD_STACK                  => 2
  rule INTERNAL_ERROR             => 3
  rule STUCK                      => 4
  rule INVALID_JSON               => 5
  rule INVALID_OP_FOR_MODE        => 6
  rule ERR_OPCODE                 => 7
  rule INT_OVERFLOW               => 8
  rule INT_UNDERFLOW              => 9
  rule DIV_BY_ZERO                => 10
  rule BYTES_OVERFLOW             => 11
  rule TXN_ACCESS_FAILED          => 12
  rule TXN_INVALID                => 13
  rule INVALID_SCRATCH_LOC        => 14
  rule TXN_OUT_OF_BOUNDS          => 15
  rule FUTURE_TXN                 => 16
  rule INDEX_OUT_OF_BOUNDS        => 17
  rule ILLEGAL_JUMP               => 18
  rule ILL_TYPED_STACK            => 19
  rule LOG_CALLS_EXCEEDED         => 20
  rule LOG_SIZE_EXCEEDED          => 21
  rule GLOBAL_BYTES_EXCEEDED      => 22
  rule GLOBAL_INTS_EXCEEDED       => 23
  rule LOCAL_BYTES_EXCEEDED       => 24
  rule LOCAL_INTS_EXCEEDED        => 25
  rule INVALID_ARGUMENT           => 26
  rule STACK_OVERFLOW             => 27
  rule STACK_UNDERFLOW            => 28
  rule ASSERTION_VIOLATION        => 29
  rule DUPLICATE_LABEL            => 30
  rule IMPOSSIBLE_NEGATIVE_NUMBER => 31
  rule CALLSTACK_UNDERFLOW        => 32
  rule CALLSTACK_OVERFLOW         => 33
  rule ITXN_REENTRY               => 34
  rule MATH_BYTES_ARG_TOO_LONG    => 35
  rule INSUFFICIENT_FUNDS         => 36
  rule KEY_TOO_LARGE              => 37
  rule BYTE_VALUE_TOO_LARGE       => 38
  rule KEY_VALUE_TOO_LARGE        => 39
  rule TXN_DEQUE_ERROR            => 40
  rule BOX_TOO_LARGE              => 41
  rule CHANGED_BOX_SIZE           => 42
  rule BOX_NOT_FOUND              => 43
  rule BOX_UNAVAILABLE            => 44
  rule BOX_WRONG_LENGTH           => 45
  rule BOX_OUT_OF_BOUNDS          => 46
  rule BOX_CREATE_EXTERNAL        => 47
  rule MIN_BALANCE_VIOLATION      => 48
  rule UNSUPPORTED_TXN_TYPE       => 49
  rule ASSET_FROZEN               => 50
  rule ASSET_NOT_OPT_IN           => 51
  rule UNKNOWN_ADDRESS            => 52
  rule ASSET_NO_PERMISSION        => 53
  rule ASSET_NOT_FOUND            => 54
  rule MISSING_APP_CREATOR        => 55
  rule APP_ALREADY_ACTIVE         => 56
  rule INSUFFICIENT_ASSET_BALANCE => 57
  syntax KItem  ::=
    "#panic" "(" Int ")" [klabel(#panic)]
  syntax KItem  ::=
    "#stopIfError" "(" ")" [klabel(#stopIfError)]
  rule [panic]: <k> #panic(S) => #stopIfError() ... </k>
       <returncode> _ => S </returncode>
       <returnstatus> _ => returnDesc(S) </returnstatus>
  rule <k> #stopIfError() ~> X:TestingCommand => X:TestingCommand ~> #stopIfError() ... </k>
  rule <k> #stopIfError() ~> (ITEM:KItem => .K) ... </k>
       <returncode> RETURN_CODE </returncode>
    requires RETURN_CODE =/=Int 0
     andBool notBool(isTestingCommand(ITEM))
  rule <k> #stopIfError() => .K </k>
       <returncode> RETURN_CODE </returncode>
    requires RETURN_CODE =/=Int 0
  rule <k> #stopIfError() => .K ... </k>
       <returncode> RETURN_CODE </returncode>
       <returnstatus> _ => "Success" </returnstatus>
    requires RETURN_CODE ==Int 0
endmodule

module AVM-CONFIGURATION
  imports public JSON
  imports public INT
  imports public LIST
  imports public SET
  imports public ALGO-BLOCKCHAIN
  imports public TEAL-INTERPRETER-STATE
  imports public TEAL-SYNTAX
  imports public ID-SYNTAX
  configuration <kavm>
      <k> $PGM:JSON </k>
      <returncode exit=""> 4 </returncode> // the simulator exit code
      <returnstatus> "":String </returnstatus> // the exit status message

      // The transaction group as submitted
      <transactions/>

      // Transaction can create inner transactions, and we chose to treat them similarly to the outer ones.
      // We add them into an execution deque --- inner transactions are executed right after their parent one.
      // Initially, the execution deque will contain the transactions from the submitted group (up to `MaxTxGroupSize`, 16 currently).
      // Outer transactions are referred to by their actual `txID`s. Inner transaction will be assigned "fake" `txID`s,
      // starting from `MaxTxGroupSize` (currently 16).
      <avmExecution>

        // The ID of the transaction currently being executed
        <currentTx> "0" </currentTx>

        // The top of the deque is the currently executing transaction, followed by the next transaction which will be
        // executed when this one is (completely) finished, etc.
        <txnDeque>
          <deque>         .List </deque>
          <dequeIndexSet> .Set  </dequeIndexSet>
        </txnDeque>

        // The execution context of the current transaction.
        <currentTxnExecution>
          // Globals are mostly immutable during the group execution,
          // besides the application-related fields: CurrentApplicationID, CreatorID
          // and CurrentApplicationAddress
          <globals/>

          // the `<teal>` cell will control evaluation of TEAL code of the current transaction.
          // The semantics of TEAL has *read-only* access to the `<blockchain>` cell
          // and *read-write* access to the `<effects>` cell.
          <teal/>

          // the effects of the transaction. Upon approval of the transaction,
          // its effects will be applied onto the `<blockchain>` cell.
          // TODO: how to represent effects? We need to track changes to accounts, assets and apps.
          <effects> .List </effects>

          // The group ID of the last inner transaction group that was (directly) executed by the current transaction
          <lastTxnGroupID> "" </lastTxnGroupID>

        </currentTxnExecution>

        // The inner transaction group that is currently being constructed using `itxn_begin`, `itxn_next`, `itxn_field`, but
        // which has not yet been executed using `itxn_submit`
        <innerTransactions> .List </innerTransactions>

        // Applications which are currently on the call stack. This cell is needed so that we can check for re-entrant
        // app calls. The `<txnDeque>` is not sufficient for this because it contains transactions that were not yet called but
        // will be called further back in the call stack.
        <activeApps> .Set </activeApps>

        // Accounts for which a check will be made at the end of the top-level transaction group to ensure their balance is at
        // or above their minimum balance
        <touchedAccounts> .List </touchedAccounts>

      </avmExecution>

      // The blockchain state will be incrementally updated after
      // each transaction in the group. If one of the transactions fails,
      // the state will be rolled back to the one before execution the group.
      <blockchain/>

      // A ;-separated concatenation of their source code of TEAL contracts
      // should be supplied as `-cTEAL_PROGRAMS` configuration variuable
      // argument ot `krun`
      <tealPrograms> $TEAL_PROGRAMS:Map </tealPrograms>
    </kavm>
  syntax AVMSimulation
  syntax AlgorandCommand
  syntax TestingCommand
  syntax TxnCommand
  rule [[ getCurrentTxn() => I ]]
    <currentTx> I </currentTx>
endmodule

module TEAL-INTERPRETER-STATE
  imports public TEAL-SYNTAX
  imports public TEAL-STACK
  imports public MAP
  imports public INT
  imports public LIST
  syntax LabelMap  ::=
    Map
  syntax Bool  ::=
    Label "in_labels" LabelMap [function]
  rule L in_labels LL => L in_keys(LL)
  syntax Int  ::=
    "getLabelAddress" "(" Label ")" [function, klabel(getLabelAddress)]
  rule [[ getLabelAddress(L) => {LL[L]}:>Int ]]
       <labels> LL </labels>
  syntax LoadLabelsResult  ::=
    Map
  | "duplicate-label"
  | "no-labels"
  syntax CallStack  ::=
    List
  configuration <teal>
      <pc> 0 </pc>
      <program> .Map </program>
      <mode> undefined </mode>
      <version> 1 </version>               // the default TEAL version is 1 if no #pragma version is specified
      <stack> .TStack </stack>             // stores UInt64 or Bytes
      <stacksize> 0 </stacksize>           // current stack size
      <jumped> false </jumped>             // `true` if the previous opcode triggered a jump
      <labels> no-labels </labels>              // a map from labels seen so far in a program
                                           // to their corresponding program addresses, Label |-> Int
      <callStack> .List </callStack>
      <scratch> .Map </scratch>            // Int |-> TValue
      <intcblock> .Map </intcblock>        // (currently not used)
      <bytecblock> .Map </bytecblock>      // (currently not used)
    </teal>
  syntax TealExecutionOp  ::=
    "#initApp" "(" Int ")" [klabel(#initApp)]
  | "#initSmartSig" "(" ")" [klabel(#initSmartSig)]
  | "#restoreContext" "(" ")" [klabel(#restoreContext)]
  | "#initContext" "(" ")" [klabel(#initContext)]
  | "#startExecution" "(" ")" [klabel(#startExecution)]
  | "#finalizeExecution" "(" ")" [klabel(#finalizeExecution)]
  | "#fetchOpcode" "(" ")" [klabel(#fetchOpcode)]
  | "#incrementPC" "(" ")" [klabel(#incrementPC)]
endmodule

module AVM-TXN-DEQUE
  imports public LIST
  imports public SET
  imports public AVM-CONFIGURATION
  imports public AVM-PANIC
  syntax TxnDeque  ::=
    List
  syntax TxnDequeCommand  ::=
    "#pushTxnBack" "(" TxIDCell ")" [klabel(#pushTxnBack)]
  rule <k> #pushTxnBack(<txID> TXN_ID </txID>) => .K ... </k>
       <txnDeque>
         <deque> TXNS => TXNS ListItem(TXN_ID) </deque>
         <dequeIndexSet> INDICES => SetItem(TXN_ID) INDICES  </dequeIndexSet>
       </txnDeque>
       <transactions> TS </transactions>
       requires notBool (TXN_ID in INDICES)
        andBool TXN_ID in_txns(<transactions> TS </transactions>)
  rule <k> #pushTxnBack(<txID> TXN_ID </txID>) => #panic(TXN_DEQUE_ERROR) ... </k>
       <dequeIndexSet> INDICES </dequeIndexSet>
       requires TXN_ID in INDICES
  rule <k> #pushTxnBack(<txID> TXN_ID </txID>) => #panic(TXN_DEQUE_ERROR) ... </k>
       <transactions> TS </transactions>
    requires notBool (TXN_ID in_txns(<transactions> TS </transactions>))
  syntax TxnDequeCommand  ::=
    "#pushTxnFront" "(" TxIDCell ")" [klabel(#pushTxnFront)]
  rule <k> #pushTxnFront(<txID> TXN_ID </txID>) => .K ... </k>
       <txnDeque>
         <deque> TXNS => ListItem(TXN_ID) TXNS </deque>
         <dequeIndexSet> INDICES => SetItem(TXN_ID) INDICES  </dequeIndexSet>
       </txnDeque>
       <transactions> TS </transactions>
       requires notBool (TXN_ID in INDICES)
        andBool TXN_ID in_txns(<transactions> TS </transactions>)
  rule <k> #pushTxnFront(<txID> TXN_ID </txID>) => #panic(TXN_DEQUE_ERROR) ... </k>
       <dequeIndexSet> INDICES </dequeIndexSet>
       requires TXN_ID in INDICES
  rule <k> #pushTxnFront(<txID> TXN_ID </txID>) => #panic(TXN_DEQUE_ERROR) ... </k>
       <transactions> TS </transactions>
    requires notBool (TXN_ID in_txns(<transactions> TS </transactions>))
  syntax TxnDequeCommand  ::=
    "#getNextTxn" "(" ")" [klabel(#getNextTxn)]
  rule <k> #getNextTxn() => .K ... </k>
       <deque> ListItem(TXN_ID) _TXNS </deque>
       <currentTx> _ => TXN_ID </currentTx>
  rule <k> #getNextTxn() => #panic(TXN_DEQUE_ERROR) ... </k>
       <deque> .List </deque>
  syntax TxnDequeCommand  ::=
    "#popTxnFront" "(" ")" [klabel(#popTxnFront)]
  rule <k> #popTxnFront() => .K ... </k>
       <deque> ListItem(_TXN_ID) TXNS => TXNS </deque>
  rule <k> #popTxnFront() => .K ... </k>
       <deque> .List </deque>
  syntax String  ::=
    "getNextTxnID" "(" ")" [function, klabel(getNextTxnID)]
  rule [[ getNextTxnID() => TXN_ID ]]
       <deque> ListItem(TXN_ID) _ </deque>
endmodule

module AVM-LIMITS
  imports public TEAL-SYNTAX
  syntax Int  ::=
    "MAX_STACK_DEPTH" [macro]
  syntax Int  ::=
    "MAX_CALLSTACK_DEPTH" [macro]
  syntax Int  ::=
    "MAX_SCRATCH_SIZE" [macro]
  syntax Int  ::=
    "LogicSigMaxSize" [macro]
  syntax Int  ::=
    "LogicSigMaxCost" [macro]
  syntax Int  ::=
    "MaxAppProgramLen" [macro]
  syntax Int  ::=
    "MaxAppProgramCost" [macro]
  syntax Int  ::=
    "MAX_BYTEARRAY_LEN" [macro]
  syntax Int  ::=
    "MAX_BYTE_MATH_SIZE" [macro]
  syntax Int  ::=
    "MaxTxGroupSize" [macro]
  rule MAX_STACK_DEPTH     => 1000
  rule MAX_CALLSTACK_DEPTH => 32
  rule MAX_SCRATCH_SIZE    => 256
  rule LogicSigMaxSize     => 1000
  rule LogicSigMaxCost     => 20000
  rule MaxAppProgramLen    => 1024
  rule MaxAppProgramCost   => 700
  rule MAX_BYTEARRAY_LEN   => 4096
  rule MAX_BYTE_MATH_SIZE  => 64
  rule MaxTxGroupSize      => 16
endmodule

module TEAL-EXECUTION
  imports public AVM-CONFIGURATION
  imports public AVM-LIMITS
  imports public TEAL-OPCODES
  imports public TEAL-SYNTAX
  imports public TEAL-STACK
  imports public TEAL-TYPES
  imports public TEAL-INTERPRETER-STATE
  imports public AVM-PANIC
  rule <k> #initContext() => .K ...</k>
       <currentTxnExecution>
         <teal>
         _ => (
           <pc> 0 </pc>
           <program> .Map </program>
           <mode> undefined </mode>
           <version> 1 </version>
           <stack> .TStack </stack>
           <stacksize> 0 </stacksize>
           <jumped> false </jumped>
           <labels> .Map </labels>
           <callStack> .List </callStack>
           <scratch> .Map </scratch>
           <intcblock> .Map </intcblock>
           <bytecblock> .Map </bytecblock>
         )
         </teal>
         ...
       </currentTxnExecution>
  rule <k> #restoreContext() => .K ...</k>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <txnExecutionContext> (<currentTxnExecution> C </currentTxnExecution> => .K) ... </txnExecutionContext>
         ...
       </transaction>
       <currentTxnExecution> _ => C </currentTxnExecution>
  rule <k> #initApp(APP_ID) => .K ...</k>
       <currentApplicationID> _ => APP_ID </currentApplicationID>
       <currentApplicationAddress> _ => getAppAddressBytes(APP_ID) </currentApplicationAddress>
       <creatorAddress> _ => {AC [ APP_ID ]}:>Bytes </creatorAddress>
       <activeApps> (.Set => SetItem(APP_ID)) REST </activeApps>
       <lastTxnGroupID> _ => "" </lastTxnGroupID>
       <mode> _ => stateful </mode>
       <appCreator> AC </appCreator>
    requires notBool(APP_ID in REST) andBool (APP_ID in_keys(AC))
  rule <k> #initApp(APP_ID) => #panic(APP_ALREADY_ACTIVE) ... </k>
       <activeApps> REST </activeApps>
    requires APP_ID in REST
  rule <k> #initApp(APP_ID) => #panic(MISSING_APP_CREATOR) ... </k>
       <appCreator> AC </appCreator>
    requires notBool(APP_ID in_keys(AC))
  rule <k> #initSmartSig() => .K ... </k>
       <mode> _ => stateless </mode>
  syntax AlgorandCommand  ::=
    "#loadInputPgm" "(" TealInputPgm ")" [klabel(#loadInputPgm)]
  rule <k> #loadInputPgm(PRAGMAS:TealPragmas PGM:TealPgm) => #checkDuplicateLabels() ...</k>
       <program> _ => loadProgramCell(PGM, 0)      </program>
       <labels>  _ => loadLabelsCell(PGM, 0, .Map) </labels>
       <version> _ => loadVersionCell(PRAGMAS)     </version>
  rule <k> #loadInputPgm(PGM:TealPgm) => #checkDuplicateLabels() ...</k>
       <program> _ => loadProgramCell(PGM, 0)      </program>
       <labels>  _ => loadLabelsCell(PGM, 0, .Map) </labels>
       <version> _ => PARAM_DEFAULT_TEAL_VERSION   </version>
  syntax AlgorandCommand  ::=
    "#checkDuplicateLabels" "(" ")" [klabel(#checkDuplicateLabels)]
  rule <k> #checkDuplicateLabels() => #panic(DUPLICATE_LABEL) ... </k>
       <labels> duplicate-label </labels>
  rule <k> #checkDuplicateLabels() => .K ... </k>  [owise]
  syntax Int  ::=
    "loadVersionCell" "(" TealPragmas ")" [function, klabel(loadVersionCell), total]
  rule loadVersionCell ( #pragma version V _:TealPragmas ) => V
  rule loadVersionCell ( #pragma version V               ) => V
  syntax Map  ::=
    "loadProgramCell" "(" TealPgm "," Int ")" [function, klabel(loadProgramCell), total]
  rule loadProgramCell( Op:TealOpCodeOrLabel Pgm, PC ) => ((PC |-> Op) loadProgramCell( Pgm, PC +Int 1 ))
  rule loadProgramCell( Op:TealOpCodeOrLabel,     PC ) =>  (PC |-> Op)
  syntax LoadLabelsResult  ::=
    "loadLabelsCell" "(" TealPgm "," Int "," Map ")" [function, klabel(loadLabelsCell), total]
  rule loadLabelsCell( Op:TealOpCodeOrLabel Pgm, PC, LABELS ) => loadLabelsCell( Pgm, PC +Int 1, LABELS ) requires notBool(isLabelCode(Op))
  rule loadLabelsCell( Op:TealOpCodeOrLabel,     _ , LABELS ) => LABELS                                   requires notBool(isLabelCode(Op))
  rule loadLabelsCell( (L:):LabelCode Pgm, PC, LABELS ) => (loadLabelsCell( Pgm, PC +Int 1, (LABELS (L |-> PC)))) requires notBool (L in_labels LABELS)
  rule loadLabelsCell( (L:):LabelCode,     PC, LABELS ) => (L |-> PC) LABELS requires notBool (L in_labels LABELS)
  rule loadLabelsCell( (L:):LabelCode _,   _,  LABELS ) => duplicate-label requires (L in_labels LABELS)
  rule loadLabelsCell( (L:):LabelCode,     _,  LABELS ) => duplicate-label requires (L in_labels LABELS)
  rule <k> #startExecution() => #fetchOpcode() ... </k>
  rule <k> #fetchOpcode() => PGM[PC] ~> #incrementPC() ~> #fetchOpcode() ... </k>
       <pc> PC </pc>
       <program> PGM </program>
       <returncode> STATUS_CODE </returncode>
   requires isValidProgamAddress(PC) andBool STATUS_CODE ==Int 4
  rule <k> #fetchOpcode() => .K ... </k>
       <pc> PC </pc>
       <returncode> STATUS_CODE </returncode>
   requires STATUS_CODE =/=Int 4
   andBool isValidProgamAddress(PC)
  syntax Bool  ::=
    "isValidProgamAddress" "(" Int ")" [function, klabel(isValidProgamAddress)]
  rule [[ isValidProgamAddress(ADDR) => true ]]
       <program> PGM </program>
    requires 0 <=Int ADDR andBool ADDR <Int size(PGM)
  rule isValidProgamAddress(_) => false  [owise]
  rule <k> #fetchOpcode() => #finalizeExecution() ... </k>
       <pc> PC </pc>
       <program> PGM </program>
   requires PC ==Int size(PGM)
  rule <k> #incrementPC() => .K ... </k>
       <pc> PC => PC +Int #if JUMPED #then 0 #else 1 #fi </pc>
       <jumped> JUMPED => false </jumped>
  syntax KItem  ::=
    "#deactivateApp" "(" ")" [klabel(#deactivateApp)]
  syntax KItem  ::=
    "#checkStack" "(" ")" [klabel(#checkStack)]
  rule <k> #finalizeExecution() => #saveScratch() ~> #deactivateApp() ~> #checkStack() ... </k>
    requires getTxnField(getCurrentTxn(), TypeEnum) ==K (@ appl)
  rule <k> #deactivateApp() => .K ... </k>
       <currentApplicationID> APP_ID </currentApplicationID>
       <activeApps> (SetItem(APP_ID) => .Set) ... </activeApps>
  rule <k> #checkStack() => .K ... </k>
       <stack> I : .TStack </stack>
       <stacksize> SIZE </stacksize>
    requires I >Int 0 andBool SIZE ==Int 1
  rule <k> #checkStack() => #panic(ZERO_STACK) ... </k>
       <stack> I : .TStack </stack>
       <stacksize> _ </stacksize>
    requires 0 >=Int I
  rule <k> #checkStack() => #panic(BAD_STACK) ... </k>
       <stack> _ </stack>
       <stacksize> SIZE </stacksize>
    requires SIZE >Int 1
  rule <k> #checkStack() => #panic(BAD_STACK) ... </k>
       <stack> .TStack </stack>
  rule <k> #checkStack() => #panic(BAD_STACK) ... </k>
       <stack> (_:Bytes) : .TStack </stack>
       <stacksize> _ </stacksize>
  syntax KItem  ::=
    "#saveScratch" "(" ")" [klabel(#saveScratch)]
  rule <k> #saveScratch() => .K ...</k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID> TXN_ID </txID>
         <txScratch> _ => SCRATCH </txScratch>
         ...
       </transaction>
       <scratch> SCRATCH </scratch>
endmodule

module AVM-INITIALIZATION
  imports public INT
  imports public LIST
  imports public STRING
  imports public BYTES
  imports public ALGO-BLOCKCHAIN
  imports public AVM-CONFIGURATION
  imports public AVM-TXN-DEQUE
  imports public TEAL-CONSTANTS
  imports public TEAL-TYPES
  imports public ALGO-TXN
  syntax Int  ::=
    "countTxns" "(" TransactionsCell ")" [function, klabel(countTxns), total]
  rule countTxns(<transactions> <transaction> _ </transaction> REST </transactions>)
       => 1 +Int countTxns(<transactions> REST </transactions>)
  rule countTxns(<transactions> .Bag </transactions>)
       => 0
  syntax Int  ::=
    "countTxnsInGroup" "(" TransactionsCell "," String ")" [function, klabel(countTxnsInGroup), total]
  rule countTxnsInGroup(<transactions> <transaction> <groupID> GROUP </groupID> ... </transaction> REST </transactions>, GROUP)
       => 1 +Int countTxnsInGroup(<transactions> REST </transactions>, GROUP)
  rule countTxnsInGroup(<transactions> <transaction> <groupID> GROUP' </groupID> ... </transaction> REST </transactions>, GROUP)
       => countTxnsInGroup(<transactions> REST </transactions>, GROUP)
    requires GROUP' =/=K GROUP
  rule countTxnsInGroup(<transactions> .Bag </transactions>, _)
       => 0
  syntax AlgorandCommand  ::=
    "#initGlobals" "(" ")" [klabel(#initGlobals)]
  rule <k> #initGlobals() => .K ... </k>
       <globals>
         <groupSize>            _ => countTxns(<transactions> TXNS </transactions>) </groupSize>
         <globalRound>          _ => 6 </globalRound>
         <latestTimestamp>      _ => 50  </latestTimestamp>
         <currentApplicationID> _ => 0 </currentApplicationID>
         <currentApplicationAddress> _ => .Bytes </currentApplicationAddress>
         <creatorAddress> _ => .Bytes </creatorAddress>
       </globals>
       <transactions> TXNS </transactions>
  syntax AlgorandCommand  ::=
    "#initTxnIndexMap" "(" ")" [klabel(#initTxnIndexMap)]
  rule <k> #initTxnIndexMap() => #initTxnIndexMap(collectTxnIds(<transactions> TXNS </transactions>)) ... </k>
       <transactions> TXNS </transactions>
  syntax AlgorandCommand  ::=
    "#initTxnIndexMap" "(" List ")" [klabel(#initTxnIndexMap)]
  rule <k> #initTxnIndexMap(ListItem(TXN_ID) REST) => #initTxnIndexMap(ListItem(TXN_ID) REST) ... </k>
       <transaction>
         <txID> TXN_ID </txID>
         <groupID> GROUP_ID </groupID>
         ...
       </transaction>
       <txnIndexMap>
          ITEMS =>
          <txnIndexMapGroup>
            <txnIndexMapGroupKey> GROUP_ID </txnIndexMapGroupKey>
            <txnIndexMapGroupValues> .Map </txnIndexMapGroupValues>
          </txnIndexMapGroup>
          ITEMS
       </txnIndexMap>
    requires notBool (group_id_in_index_map(GROUP_ID))
  rule <k> #initTxnIndexMap(ListItem(TXN_ID) REST) => #initTxnIndexMap(REST) ... </k>
       <transaction>
         <txID> TXN_ID </txID>
         <groupID> GROUP_ID </groupID>
         <groupIdx> GROUP_IDX </groupIdx>
         ...
       </transaction>
       <txnIndexMap>
          <txnIndexMapGroup>
            <txnIndexMapGroupKey> GROUP_ID </txnIndexMapGroupKey>
            <txnIndexMapGroupValues> VALUES => VALUES[GROUP_IDX <- TXN_ID] </txnIndexMapGroupValues>
          </txnIndexMapGroup>
          ...
       </txnIndexMap>
  rule <k> #initTxnIndexMap(.List) => .K ... </k>
  syntax List  ::=
    "collectTxnIds" "(" TransactionsCell ")" [function, klabel(collectTxnIds), total]
  rule collectTxnIds(<transactions> .Bag </transactions>) => .List
  rule collectTxnIds(<transactions> <transaction> <txID> TXN_ID </txID> ... </transaction> TXNS </transactions>)
    => ListItem(TXN_ID) collectTxnIds(<transactions> TXNS </transactions>)
  syntax Bool  ::=
    "group_id_in_index_map" "(" String ")" [function, total]
  rule [[ group_id_in_index_map(GROUP_ID) => true ]]
       <txnIndexMapGroupKey> GROUP_ID </txnIndexMapGroupKey>
  rule group_id_in_index_map(_GROUP_ID) => false  [owise]
endmodule

module ALGO-ITXN
  imports public ALGO-TXN
  imports public AVM-CONFIGURATION
  imports public AVM-TXN-DEQUE
  imports public TEAL-TYPES
  imports public TEAL-FIELDS
  imports public TEAL-EXECUTION
  imports public MAP
  imports public AVM-INITIALIZATION
  syntax KItem  ::=
    "#setItxnField" "(" TxnFieldTop "," TValue ")" [klabel(#setItxnField)]
  rule <k> #setItxnField(Sender, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <sender> _ => VAL </sender> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Fee, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <fee> _ => VAL </fee> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Note, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <note> _ => VAL </note> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(RekeyTo, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <rekeyTo> _ => VAL </rekeyTo> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Type, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction>
                   <txType> _ => VAL </txType>
                   <typeEnum> _=> typeString2Enum(VAL) </typeEnum>
                    ...
                  </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(TypeEnum, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction>
                   <txType> _ => typeEnum2String(VAL) </txType>
                   <typeEnum> _ => VAL </typeEnum>
                   ...
                  </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(_:TxnPayField, _) ... </k>
       <innerTransactions>
         ...
         ListItem(
         <transaction>
           .PayTxFieldsCell =>
           <payTxFields>
             <receiver>         .Bytes </receiver>
             <amount>           0      </amount>
             <closeRemainderTo> .Bytes </closeRemainderTo>
           </payTxFields>
           ...
         </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Receiver, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <receiver> _ => VAL </receiver> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Amount, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <amount> _ => VAL </amount> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(CloseRemainderTo, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <closeRemainderTo> _ => VAL </closeRemainderTo> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(_:TxnKeyregField, _) ... </k>
       <innerTransactions>
         ...
         ListItem(
         <transaction>
           .KeyRegTxFieldsCell =>
           <keyRegTxFields>
             <votePk>           .Bytes </votePk>
             <selectionPK>      .Bytes </selectionPK>
             <voteFirst>        0      </voteFirst>
             <voteLast>         0      </voteLast>
             <voteKeyDilution>  0      </voteKeyDilution>
             <nonparticipation> 0      </nonparticipation>
           </keyRegTxFields>
           ...
         </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(VotePK, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <votePk> _ => VAL </votePk> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(SelectionPK, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <selectionPK> _ => VAL </selectionPK> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(VoteFirst, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <voteFirst> _ => VAL </voteFirst> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(VoteLast, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <voteLast> _ => VAL </voteLast> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(VoteKeyDilution, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <voteKeyDilution> _ => VAL </voteKeyDilution> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Nonparticipation, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <nonparticipation> _ => VAL </nonparticipation> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(_:TxnAcfgField, _) ... </k>
       <innerTransactions>
         ...
         ListItem(
         <transaction>
           .AssetConfigTxFieldsCell =>
           <assetConfigTxFields>
             <configAsset> 0 </configAsset>
             <assetParams>
               <configTotal>         0                           </configTotal>
               <configDecimals>      0                           </configDecimals>
               <configDefaultFrozen> 0                           </configDefaultFrozen>
               <configUnitName>      .Bytes                      </configUnitName>
               <configAssetName>     .Bytes                      </configAssetName>
               <configAssetURL>      .Bytes                      </configAssetURL>
               <configMetaDataHash>  .Bytes                      </configMetaDataHash>
               <configManagerAddr>   PARAM_ZERO_ADDR             </configManagerAddr>
               <configReserveAddr>   PARAM_ZERO_ADDR             </configReserveAddr>
               <configFreezeAddr>    PARAM_ZERO_ADDR             </configFreezeAddr>
               <configClawbackAddr>  PARAM_ZERO_ADDR             </configClawbackAddr>
             </assetParams>
           </assetConfigTxFields>
           ...
         </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAsset, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configAsset> _ => VAL </configAsset> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetTotal, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configTotal> _ => VAL </configTotal> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetDecimals, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configDecimals> _ => VAL </configDecimals> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetDefaultFrozen, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configDefaultFrozen> _ => VAL </configDefaultFrozen> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetUnitName, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configUnitName> _ => VAL </configUnitName> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetName, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configAssetName> _ => VAL </configAssetName> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetURL, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configAssetURL> _ => VAL </configAssetURL> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetMetaDataHash, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configMetaDataHash> _ => VAL </configMetaDataHash> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetManager, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configManagerAddr> _ => VAL </configManagerAddr> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetReserve, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configReserveAddr> _ => VAL </configReserveAddr> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetFreeze, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configFreezeAddr> _ => VAL </configFreezeAddr> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ConfigAssetClawback, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <configClawbackAddr> _ => VAL </configClawbackAddr> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(_:TxnAxferField, _) ... </k>
       <innerTransactions>
         ...
         ListItem(
         <transaction>
           .AssetTransferTxFieldsCell =>
           <assetTransferTxFields>
             <xferAsset>     0                           </xferAsset>
             <assetAmount>   0                           </assetAmount>
             <assetReceiver> {getGlobalField(ZeroAddress)}:>Bytes </assetReceiver>
             <assetASender>  {getGlobalField(ZeroAddress)}:>Bytes </assetASender>
             <assetCloseTo>  {getGlobalField(ZeroAddress)}:>Bytes </assetCloseTo>
           </assetTransferTxFields>
           ...
         </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(XferAsset, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <xferAsset> _ => VAL </xferAsset> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(AssetAmount, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <assetAmount> _ => VAL </assetAmount> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(AssetSender, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <assetASender> _ => VAL </assetASender> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(AssetReceiver, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <assetReceiver> _ => VAL </assetReceiver> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(AssetCloseTo, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <assetCloseTo> _ => VAL </assetCloseTo> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(_:TxnAfrzField, _) ... </k>
       <innerTransactions>
         ...
         ListItem(
         <transaction>
           .AssetFreezeTxFieldsCell =>
           <assetFreezeTxFields>
             <freezeAccount> {getGlobalField(ZeroAddress)}:>Bytes </freezeAccount>
             <freezeAsset>   0                           </freezeAsset>
             <assetFrozen>   0                           </assetFrozen>
           </assetFreezeTxFields>
           ...
         </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(FreezeAsset, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <freezeAsset> _ => VAL </freezeAsset> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(FreezeAssetAccount, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <freezeAccount> _ => VAL </freezeAccount> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(FreezeAssetFrozen, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <assetFrozen> _ => VAL </assetFrozen> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(FIELD, _) ... </k>
       <innerTransactions>
         ...
         ListItem(
         <transaction>
           .AppCallTxFieldsCell =>
           <appCallTxFields>
             <applicationID>        0                    </applicationID>
             <onCompletion>         0                    </onCompletion>
             <accounts>             .TValueList          </accounts>
             <approvalProgramSrc>   (int 0):TealInputPgm </approvalProgramSrc>
             <clearStateProgramSrc> (int 0):TealInputPgm </clearStateProgramSrc>
             <approvalProgram>      .Bytes               </approvalProgram>
             <clearStateProgram>    .Bytes               </clearStateProgram>
             <applicationArgs>      .TValueList          </applicationArgs>
             <foreignApps>          .TValueList          </foreignApps>
             <foreignAssets>        .TValueList          </foreignAssets>
             <boxReferences>         .TValuePairList     </boxReferences>
             <globalStateSchema>
               <globalNui> 0 </globalNui>
               <globalNbs> 0 </globalNbs>
             </globalStateSchema>
             <localStateSchema>
               <localNui> 0 </localNui>
               <localNbs> 0 </localNbs>
             </localStateSchema>
             <extraProgramPages>    0                    </extraProgramPages>
           </appCallTxFields>
           ...
         </transaction>)
       </innerTransactions>
    requires isTxnApplField(FIELD) orBool isTxnaField(FIELD)
  rule <k> #setItxnField(ApplicationID, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <applicationID> _ => VAL </applicationID> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(OnCompletion, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <onCompletion> _ => VAL </onCompletion> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ApprovalProgram, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <approvalProgram> _ => VAL </approvalProgram> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ClearStateProgram, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <clearStateProgram> _ => VAL </clearStateProgram> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(ApplicationArgs, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <applicationArgs> APP_ARGS => append(VAL, APP_ARGS) </applicationArgs> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Accounts, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <accounts> ACCOUNTS => append(VAL, ACCOUNTS) </accounts> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Applications, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <foreignApps> APPS => append(VAL, APPS) </foreignApps> ... </transaction>)
       </innerTransactions>
  rule <k> #setItxnField(Assets, VAL) => .K ... </k>
       <innerTransactions>
         ...
         ListItem(<transaction> <foreignAssets> ASSETS => append(VAL, ASSETS) </foreignAssets> ... </transaction>)
       </innerTransactions>
  syntax KItem  ::=
    "#checkItxn" "(" TransactionCell ")" [klabel(#checkItxn)]
  rule <k> #checkItxn(TXN) => (#checkItxnFieldsCoherent(TXN) ~> #checkForReentrance(TXN)) ...</k>
  syntax KItem  ::=
    "#checkForReentrance" "(" TransactionCell ")" [klabel(#checkForReentrance)]
  rule <k> #checkForReentrance(
             <transaction>
               <txID> _TX_ID </txID>
               <txnTypeSpecificFields>
                 <appCallTxFields>
                   <applicationID> APP_ID </applicationID>
                   ...
                 </appCallTxFields>
               </txnTypeSpecificFields>
               ...
             </transaction>) => .
             ...
       </k>
       <activeApps> AA </activeApps>
    requires notBool(APP_ID in AA )
  rule <k> #checkForReentrance(
             <transaction>
               <txID> _TX_ID </txID>
               <txnTypeSpecificFields>
                 <appCallTxFields>
                   <applicationID> APP_ID </applicationID>
                   ...
                 </appCallTxFields>
               </txnTypeSpecificFields>
               ...
             </transaction>) => #panic(ITXN_REENTRY)
             ...
       </k>
       <activeApps> AA </activeApps>
    requires APP_ID in AA
  rule <k> #checkForReentrance(_) => .K ...</k>   [owise]
  syntax KItem  ::=
    "#checkItxnFieldsCoherent" "(" TransactionCell ")" [klabel(#checkItxnFieldsCoherent)]
  rule <k> #checkItxnFieldsCoherent(
         <transaction>
           <txnTypeSpecificFields>
             <payTxFields> _ </payTxFields>
           </txnTypeSpecificFields>
           ...
         </transaction>) => .K ...
       </k>
  rule <k> #checkItxnFieldsCoherent(
         <transaction>
           <txnTypeSpecificFields>
             <appCallTxFields> _ </appCallTxFields>
           </txnTypeSpecificFields>
           ...
         </transaction>) => .K ...
       </k>
  rule <k> #checkItxnFieldsCoherent(
         <transaction>
           <txnTypeSpecificFields>
             <keyRegTxFields> _ </keyRegTxFields>
           </txnTypeSpecificFields>
           ...
         </transaction>) => .K ...
       </k>
  rule <k> #checkItxnFieldsCoherent(
         <transaction>
           <txnTypeSpecificFields>
             <assetConfigTxFields> _ </assetConfigTxFields>
           </txnTypeSpecificFields>
           ...
         </transaction>) => .K ...
       </k>
  rule <k> #checkItxnFieldsCoherent(
         <transaction>
           <txnTypeSpecificFields>
             <assetTransferTxFields> _ </assetTransferTxFields>
           </txnTypeSpecificFields>
           ...
         </transaction>) => .K ...
       </k>
  rule <k> #checkItxnFieldsCoherent(
         <transaction>
           <txnTypeSpecificFields>
             <assetFreezeTxFields> _ </assetFreezeTxFields>
           </txnTypeSpecificFields>
           ...
         </transaction>) => .K ...
       </k>
  rule <k> #checkItxnFieldsCoherent(<transaction> _T </transaction>) => #panic(TXN_INVALID) ...</k>  [owise]
  syntax KItem  ::=
    "#checkItxns" "(" List ")" [klabel(#checkItxns)]
  rule <k> #checkItxns((ListItem(T:TransactionCell) REST)) => (#checkItxn(T) ~> #checkItxns(REST)) ...</k>
  rule <k> #checkItxns(.List) => .K ...</k>
  syntax AlgorandCommand  ::=
    "#evalTxGroup" "(" ")" [klabel(#evalTxGroup)]
  syntax KItem  ::=
    "#executeItxnGroup" "(" ")" [klabel(#executeItxnGroup)]
  rule <k> #executeItxnGroup() => (#saveState() ~> #pushItxns() ~> #evalTxGroup()) ...</k>
  syntax KItem  ::=
    "#pushItxns" "(" ")" [klabel(#pushItxns)]
  rule <k> #pushItxns() => (#pushTxnFront(<txID> Int2String(TXN_ID) </txID>) ~> #pushItxns()) ...</k>
       <innerTransactions> _OTHER_ITXNS:List (ListItem(
         <transaction>
           <txID> _ </txID>
           <txHeader>
             <groupID> GROUP_ID </groupID>
             TX_HEADER
           </txHeader>
           TXN_BODY
         </transaction>
         ) => .List)
       </innerTransactions>
       <transactions>
         (.Bag =>
         <transaction>
           <txID> Int2String(TXN_ID) </txID>
           <txHeader>
             <groupID> GROUP_ID </groupID>
             TX_HEADER
           </txHeader>
           TXN_BODY
         </transaction>)
         TXNS
       </transactions>
       <nextTxnID> TXN_ID => TXN_ID +Int 1 </nextTxnID>
  requires notBool (Int2String(TXN_ID) in_transactions(<transactions> TXNS </transactions>))
  rule <k> #pushItxns() => .K ...</k>
       <innerTransactions> .List </innerTransactions>
  syntax KItem  ::=
    "#saveState" "(" ")" [klabel(#saveState)]
  rule <k> #saveState() => .K ...</k>
       <currentTxnExecution> C </currentTxnExecution>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID> TXN_ID </txID>
         <txnExecutionContext>
           _ => <currentTxnExecution> C </currentTxnExecution>
         </txnExecutionContext>
         ...
       </transaction>
  syntax KItem  ::=
    "#loadFromGroupInner" "(" Int "," TxnField ")" [klabel(#loadFromGroupInner)]
  syntax KItem  ::=
    "#loadFromGroupInner" "(" Int "," TxnaField "," Int ")" [klabel(#loadFromGroupInner)]
  rule <k> #loadFromGroupInner(GROUP_IDX, FIELD) => .K ...</k>
       <lastTxnGroupID> LAST_GROUP </lastTxnGroupID>
       <stack> XS => ({getTxnField(TX_ID, FIELD)}:>TValue : XS) </stack>
       <stacksize> SS => SS +Int 1 </stacksize>
       <transaction>
         <txID> TX_ID </txID>
         <groupID> LAST_GROUP </groupID>
         <groupIdx> GROUP_IDX </groupIdx>
         ...
       </transaction>
    requires isTValue(getTxnField(TX_ID, FIELD))
  rule <k> #loadFromGroupInner(GROUP_IDX, FIELD, IDX) => .K ...</k>
       <lastTxnGroupID> LAST_GROUP </lastTxnGroupID>
       <stack> XS => ({getTxnField(TX_ID, FIELD, IDX)}:>TValue : XS) </stack>
       <stacksize> SS => SS +Int 1 </stacksize>
       <transaction>
         <txID> TX_ID </txID>
         <groupID> LAST_GROUP </groupID>
         <groupIdx> GROUP_IDX </groupIdx>
         ...
       </transaction>
    requires isTValue(getTxnField(TX_ID, FIELD, IDX))
  syntax Int  ::=
    "getLastItxnGroupIdx" "(" ")" [function, klabel(getLastItxnGroupIdx)]
  rule [[ getLastItxnGroupIdx() => countTxnsInGroup(<transactions> TXNS </transactions>, GROUP) -Int 1 ]]
       <transactions> TXNS </transactions>
       <lastTxnGroupID> GROUP </lastTxnGroupID>
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

module TXN-ARGS
  imports public TEAL-TYPES
  imports public DOMAINS
  configuration <args> .Map </args>
  syntax MaybeTValue  ::=
    "getArgument" "(" Int ")" [function, klabel(getArgument)]
  rule [[ getArgument(I) => A ]]
       <args> ... I |-> A ... </args>
  rule [[ getArgument(I) => NoTValue ]]
       <args> Args </args>
    requires notBool (I in_keys(Args))
endmodule

module TEAL-DRIVER
  imports public AVM-CONFIGURATION
  imports public AVM-LIMITS
  imports public ALGO-ITXN
  imports public GLOBALS
  imports public TEAL-INTERPRETER-STATE
  imports public TEAL-EXECUTION
  imports public TEAL-STACK
  imports public KRYPTO
  imports public AVM-PANIC
  rule <k> NoOpCode  => .K ... </k>
  rule <k> err => #panic(ERR_OPCODE) ... </k>
  rule <k> sha256 => .K ... </k>
       <stack> B : XS => String2Bytes(Sha256raw(Bytes2String(B))) : XS </stack>
  rule <k> keccak256 => .K ... </k>
       <stack> B : XS => String2Bytes(Keccak256raw(Bytes2String(B))) : XS </stack>
  rule <k> sha512_256 => .K ... </k>
       <stack> B : XS => String2Bytes(Sha512_256raw(Bytes2String(B))) : XS </stack>
  rule <k> + => .K ... </k>
       <stack> I2 : I1 : XS => (I1 +Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I1 +Int I2 <=Int MAX_UINT64
  rule <k> + => #panic(INT_OVERFLOW) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 +Int I2 >Int MAX_UINT64
  rule <k> - => .K ... </k>
       <stack> I2 : I1 : XS => (I1 -Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I1 >=Int I2
  rule <k> - => #panic(INT_UNDERFLOW) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 <Int I2
  rule <k> * => .K ... </k>
       <stack> I2 : I1 : XS => (I1 *Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I1 *Int I2 <=Int MAX_UINT64
  rule <k> * => #panic(INT_OVERFLOW) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 *Int I2 >Int MAX_UINT64
  rule <k> / => .K ... </k>
       <stack> I2 : I1 : XS => (I1 /Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I2 >Int 0
  rule <k> / => #panic(DIV_BY_ZERO) ... </k>
       <stack> I2 : (_:TValue) : _ </stack>
    requires I2 <=Int 0
  rule <k> % => .K ... </k>
       <stack> I2 : I1 : XS => (I1 %Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I2 >Int 0
  rule <k> % => #panic(DIV_BY_ZERO) ... </k>
       <stack> I2 : (_:TValue) : _ </stack>
    requires I2 <=Int 0
  rule <k> exp => .K ... </k>
       <stack> I2 : I1 : XS => (I1 ^Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I1 ^Int I2 <=Int MAX_UINT64
     andBool notBool (I1 ==Int 0 andBool I2 ==Int 0)
  rule <k> exp => #panic(INVALID_ARGUMENT) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 ==Int 0 andBool I2 ==Int 0
  rule <k> exp => #panic(INT_OVERFLOW) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 ^Int I2 >Int MAX_UINT64
  rule <k> divmodw => .K ... </k>
       <stack> I4 : I3 : I2 : I1 : XS =>
               #fun(NUMERATOR
            => #fun(DENOMINATOR
            => #fun(QUOTIENT
            => #fun(REMAINDER
            =>   lowerU64(REMAINDER) : upperU64(REMAINDER) :
                 lowerU64(QUOTIENT)  : upperU64(QUOTIENT)  : XS
               )(NUMERATOR %Int DENOMINATOR)
               )(NUMERATOR /Int DENOMINATOR)
               )(asUInt128(I3, I4))
               )(asUInt128(I1, I2))
       </stack>
    requires notBool (I4 ==Int 0 andBool I3 ==Int 0)
  rule <k> divmodw => #panic(DIV_BY_ZERO) ... </k>
       <stack> I4 : I3 : _ : _ : _ </stack>
    requires I4 ==Int 0 andBool I3 ==Int 0
  rule <k> divw => .K ... </k>
       <stack> I3 : I2 : I1 : XS =>
               #fun(NUMERATOR
            => #fun(DENOMINATOR
            => #fun(QUOTIENT
            => QUOTIENT : XS
               )(NUMERATOR /Int DENOMINATOR)
               )(I3)
               )(asUInt128(I1, I2))
       </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires I3 =/=Int 0
     andBool (asUInt128(I1, I2) /Int I3) <=Int MAX_UINT64
  rule <k> divw => #panic(INT_OVERFLOW) ... </k>
       <stack> I3 : I2 : I1 : _ </stack>
    requires I3 =/=Int 0
     andBool (asUInt128(I1, I2) /Int I3) >Int MAX_UINT64
  rule <k> divw => #panic(DIV_BY_ZERO) ... </k>
       <stack> 0 : _ : _ : _ </stack>
  rule <k> divw => #panic(ILL_TYPED_STACK) ... </k>
       <stack> I3 : I2 : I1 : _ </stack>
    requires isBytes(I1) orBool isBytes(I2) orBool isBytes(I3)
  syntax Int  ::=
    "asUInt128" "(" TUInt64 "," TUInt64 ")" [function, klabel(asUInt128), total]
  rule asUInt128(I1, I2) => (I1 <<Int 64) +Int I2
  rule <k> addw => .K ... </k>
       <stack> I2 : I1 : XS => lowerU64(I1 +Int I2) : upperU64(I1 +Int I2) : XS </stack>
  rule <k> mulw => .K ... </k>
       <stack> I2 : I1 : XS => lowerU64(I1 *Int I2) : upperU64(I1 *Int I2) : XS </stack>
  rule <k> expw => .K ... </k>
       <stack> I2 : I1 : XS => lowerU64(I1 ^Int I2) : upperU64(I1 ^Int I2) : XS </stack>
    requires I1 ^Int I2 <=Int MAX_UINT128
     andBool notBool (I1 ==Int 0 andBool I2 ==Int 0)
  rule <k> expw => #panic(INVALID_ARGUMENT) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 ==Int 0 andBool I2 ==Int 0
  rule <k> expw => #panic(INT_OVERFLOW) ... </k>
       <stack> I2 : I1 : _ </stack>
    requires I1 ^Int I2 >Int MAX_UINT128
  rule <k> sqrt => .K ... </k>
       <stack> X : XS => sqrtTUInt64(X) : XS </stack>
    requires X >=Int 0 andBool X <=Int MAX_UINT64
  rule <k> sqrt => #panic(INVALID_ARGUMENT) ... </k>
       <stack> X : _ </stack>
    requires notBool( X >=Int 0 andBool X <=Int MAX_UINT64)
  rule <k> bsqrt => .K ... </k>
       <stack> B:Bytes : XS => Int2Bytes(sqrtUInt(Bytes2Int(B, BE, Unsigned)), BE, Unsigned) : XS </stack>
  rule <k> bsqrt => #panic(INVALID_ARGUMENT) ... </k>
       <stack> _:Int : _ </stack>
  syntax Int  ::=
    "sqrtUInt" "(" Int ")" [function, klabel(sqrtUInt)]
  syntax Int  ::=
    "sqrtUInt" "(" Int "," Int "," Int ")" [function, klabel(sqrtUInt)]
  rule sqrtUInt(X) => X requires X <=Int 1 andBool X >=Int 0
  rule sqrtUInt(X) => sqrtUInt(X, X /Int 2, ((X /Int 2) +Int (X /Int (X /Int 2))) /Int 2) requires X >Int 1
  rule sqrtUInt(_, X0, X1) => X0 requires X1 >=Int X0
  rule sqrtUInt(X, X0, X1) => sqrtUInt(X, X1, (X1 +Int (X /Int X1)) /Int 2) requires X1 <Int X0
  syntax Int  ::=
    "sqrtTUInt64" "(" TUInt64 ")" [function, klabel(sqrtTUInt64)]
  | "sqrtTUInt64" "(" TUInt64 "," TUInt64 "," TUInt64 "," Int ")" [function, klabel(sqrtTUInt64)]
  rule sqrtTUInt64(SQ) => sqrtTUInt64(SQ, 0, 0, 0)
    requires SQ >=Int 0 andBool SQ <=Int MAX_UINT64
  rule sqrtTUInt64(SQ, REM, ROOT, I) =>
       #fun(ROOT'
    => #fun(REM'
    => #if   ROOT' <Int REM'
       #then sqrtTUInt64((SQ <<Int 2) %Int (MAX_UINT64 +Int 1)
                        , REM' -Int (ROOT' |Int 1)
                        , ROOT' +Int 2
                        , I +Int 1)
       #else sqrtTUInt64((SQ <<Int 2) %Int (MAX_UINT64 +Int 1)
                        , REM'
                        , ROOT'
                        , I +Int 1)
       #fi
       )((REM <<Int 2) |Int (SQ >>Int (64 -Int 2)))
       )(ROOT <<Int 1)
    requires I >=Int 0 andBool I <Int 32
  rule sqrtTUInt64(_, _  , ROOT, I) => ROOT >>Int 1
    requires I >=Int 32
  rule <k> < => .K ... </k>
       <stack> I2 : I1 : XS => bool2Int (I1 <Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> > => .K ... </k>
       <stack> I2 : I1 : XS => bool2Int (I1 >Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> <= => .K ... </k>
       <stack> I2 : I1 : XS => bool2Int (I1 <=Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> >= => .K ... </k>
       <stack> I2 : I1 : XS => bool2Int (I1 >=Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> == => .K ... </k>
       <stack> (I2:Int) : (I1:Int) : XS => bool2Int (I1 ==Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> == => .K ... </k>
       <stack> (B2:Bytes) : (B1:Bytes) : XS => bool2Int (B1 ==K B2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> != => .K ... </k>
       <stack> (I2:Int) : (I1:Int) : XS => bool2Int (I1 =/=K I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> != => .K ... </k>
       <stack> (B2:Bytes) : (B1:Bytes) : XS =>
               bool2Int (B1 =/=K B2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> && => .K ... </k>
       <stack> I2 : I1 : XS =>
               bool2Int (I1 >Int 0 andBool I2 >Int 0) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> || => .K ... </k>
       <stack> I2 : I1 : XS =>
               bool2Int (I1 >Int 0 orBool I2 >Int 0) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> ! => .K ... </k>
       <stack> I : XS => bool2Int (I ==Int 0) : XS </stack>
  rule <k> | => .K ... </k>
       <stack> I2 : I1 : XS => (I1 |Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> & => .K ... </k>
       <stack> I2 : I1 : XS => (I1 &Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> ^ => .K ... </k>
       <stack> I2 : I1 : XS => (I1 xorInt I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> shl => .K ... </k>
       <stack> I2 : I1 : XS => ((I1 <<Int I2) %Int (MAX_UINT64 +Int 1)) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I2 >=Int 0 andBool I2 <Int 64
  rule <k> shl => #panic(INVALID_ARGUMENT) ... </k>
       <stack> I2 : _ : _ </stack>
    requires notBool (I2 >=Int 0 andBool I2 <Int 64)
  rule <k> shr => .K ... </k>
       <stack> I2 : I1 : XS => (I1 >>Int I2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I2 >=Int 0 andBool I2 <Int 64
  rule <k> shr => #panic(INVALID_ARGUMENT) ... </k>
       <stack> I2 : _ : _ </stack>
    requires notBool (I2 >=Int 0 andBool I2 <Int 64)
  rule <k> ~ => .K ... </k>
       <stack> I : XS => (I xorInt MAX_UINT64) : XS </stack>
  rule <k> ~ => #panic(ILL_TYPED_STACK) ... </k>
       <stack> _:Bytes : _ </stack>
  rule <k> bitlen => .K ... </k>
       <stack> (I:Int) : XS => 0 : XS </stack>
    requires I ==Int 0
  rule <k> bitlen => .K ... </k>
       <stack> (I:Int) : XS => log2Int(I) +Int 1 : XS </stack>
    requires 0 <Int I andBool I <=Int MAX_UINT64
  rule <k> bitlen => .K ... </k>
       <stack> (B:Bytes) : XS => 0 : XS </stack>
    requires lengthBytes(B) <=Int MAX_BYTEARRAY_LEN
     andBool Bytes2Int(B, BE, Unsigned) ==Int 0
  rule <k> bitlen => .K ... </k>
       <stack> (B:Bytes) : XS => log2Int(Bytes2Int(B, BE, Unsigned)) +Int 1 : XS </stack>
    requires lengthBytes(B) <=Int MAX_BYTEARRAY_LEN
     andBool Bytes2Int(B, BE, Unsigned) >Int 0
  rule <k> len => .K ... </k>
       <stack> B : XS => lengthBytes(B) : XS </stack>
  rule <k> itob => .K ... </k>
       <stack> I : XS => padLeftBytes(Int2Bytes(I, BE, Unsigned), 8, 0) : XS </stack>
  rule <k> btoi => .K ... </k>
       <stack> B : XS => Bytes2Int(B, BE, Unsigned) : XS </stack>
    requires Bytes2Int(B, BE, Unsigned) <=Int MAX_UINT64
  rule <k> btoi => #panic(INT_OVERFLOW) ... </k>
       <stack> B : _ </stack>
    requires Bytes2Int(B, BE, Unsigned) >Int MAX_UINT64
  rule <k> concat => .K ... </k>
       <stack> B2 : B1 : XS => (B1 +Bytes B2) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(B1 +Bytes B2) <=Int MAX_BYTEARRAY_LEN
  rule <k> concat => #panic(BYTES_OVERFLOW) ... </k>
       <stack> B2 : B1 : _ </stack>
    requires lengthBytes(B1 +Bytes B2) >Int MAX_BYTEARRAY_LEN
  rule <k> substring START END => .K ... </k>
       <stack> B : XS => substrBytes(B, START, END) : XS </stack>
    requires 0 <=Int START andBool START <=Int END andBool END <=Int lengthBytes(B)
  rule <k> substring START END => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> (B:Bytes) : _ </stack>
    requires 0 >Int START orBool START >Int END orBool END >Int lengthBytes(B)
  rule <k> substring3 => .K ... </k>
       <stack> B : START : END : XS => substrBytes(B, START, END) : XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires 0 <=Int START andBool START <=Int END andBool END <=Int lengthBytes(B)
  rule <k> substring3 => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> (B:Bytes) : START : END : _ </stack>
    requires 0 >Int START orBool START >Int END orBool END >Int lengthBytes(B)
  rule <k> bzero => .K ... </k>
       <stack> X : XS => padLeftBytes(.Bytes, X, 0) : XS </stack>
    requires X <=Int MAX_BYTEARRAY_LEN
  rule <k> bzero => #panic(INVALID_ARGUMENT) ... </k>
       <stack> X : _ </stack>
    requires X >Int MAX_BYTEARRAY_LEN
  rule <k> extract S L => .K ... </k>
       <stack> ARRAY : XS => substrBytes(ARRAY, S, S +Int L) : XS </stack>
    requires 0 <=Int S andBool S <=Int 255
     andBool 0 <Int L andBool L <=Int 255
     andBool L <=Int lengthBytes(ARRAY)
     andBool S +Int L <=Int lengthBytes(ARRAY)
  rule <k> extract S L => .K ... </k>
       <stack> ARRAY : XS => substrBytes(ARRAY, S, lengthBytes(ARRAY)) : XS </stack>
    requires 0 <=Int S andBool S <=Int 255
     andBool 0 ==Int L
     andBool S <=Int lengthBytes(ARRAY)
  rule <k> extract S L => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> ARRAY : _ </stack>
      requires S >Int lengthBytes(ARRAY)
        orBool S +Int L >Int lengthBytes(ARRAY)
  rule <k> extract S L => #panic(INVALID_ARGUMENT) ... </k>
      requires 0 >Int S orBool S >Int MAX_UINT8
       orBool  0 >Int L orBool L >Int MAX_UINT8
  rule <k> extract3 => .K ... </k>
       <stack> C : B : ARRAY : XS => substrBytes(ARRAY, B, B +Int C) : XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires B <=Int lengthBytes(ARRAY)
     andBool B +Int C <=Int lengthBytes(ARRAY)
  rule <k> extract3 => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> C : B : ARRAY : _ </stack>
      requires B >Int lengthBytes(ARRAY)
        orBool B +Int C >Int lengthBytes(ARRAY)
  rule <k> extract_uint16 => .K ... </k>
       <stack> B : ARRAY : XS =>
               Bytes2Int(substrBytes(ARRAY, B, B +Int 2), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires B <=Int lengthBytes(ARRAY)
     andBool B +Int 2 <=Int lengthBytes(ARRAY)
  rule <k> extract_uint16 => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> B : ARRAY : _ </stack>
      requires B >Int lengthBytes(ARRAY)
        orBool B +Int 2 >Int lengthBytes(ARRAY)
  rule <k> extract_uint32 => .K ... </k>
       <stack> B : ARRAY : XS =>
               Bytes2Int(substrBytes(ARRAY, B, B +Int 4), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires B <=Int lengthBytes(ARRAY)
     andBool B +Int 4 <=Int lengthBytes(ARRAY)
  rule <k> extract_uint32 => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> B : ARRAY : _ </stack>
      requires B >Int lengthBytes(ARRAY)
        orBool B +Int 4 >Int lengthBytes(ARRAY)
  rule <k> extract_uint64 => .K ... </k>
       <stack> B : ARRAY : XS =>
               Bytes2Int(substrBytes(ARRAY, B, B +Int 8), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires B <=Int lengthBytes(ARRAY)
     andBool B +Int 8 <=Int lengthBytes(ARRAY)
  rule <k> extract_uint64 => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> B : ARRAY : _ </stack>
      requires B >Int lengthBytes(ARRAY)
        orBool B +Int 8 >Int lengthBytes(ARRAY)
  rule <k> replace2 START:Int => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS => replaceAtBytes(A, START, B) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires START +Int lengthBytes(B) <=Int lengthBytes(A)
  rule <k> replace2 START:Int => #panic(BYTES_OVERFLOW) ... </k>
       <stack> B:Bytes : A:Bytes : _ </stack>
       <stacksize> _ </stacksize>
    requires START +Int lengthBytes(B) >Int lengthBytes(A)
  rule <k> replace3 => .K ... </k>
       <stack> B:Bytes : START:Int : A:Bytes : XS => replaceAtBytes(A, START, B) : XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires START +Int lengthBytes(B) <=Int lengthBytes(A)
  rule <k> replace3 => #panic(BYTES_OVERFLOW) ... </k>
       <stack> B:Bytes : START:Int : A:Bytes : _ </stack>
       <stacksize> _ </stacksize>
    requires START +Int lengthBytes(B) >Int lengthBytes(A)
  rule <k> OP:MathByteOpCode => #panic(MATH_BYTES_ARG_TOO_LONG) ... </k>
       <stack> B:Bytes : A:Bytes : _ </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires (lengthBytes(A) >Int MAX_BYTE_MATH_SIZE
      orBool lengthBytes(B) >Int MAX_BYTE_MATH_SIZE)
     andBool notBool(isUnaryLogicalMathByteOpCode(OP))
  rule <k> _OP:UnaryLogicalMathByteOpCode => #panic(MATH_BYTES_ARG_TOO_LONG) ... </k>
       <stack> A:Bytes : _ </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) >Int MAX_BYTE_MATH_SIZE
  rule <k> b+ => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               Int2Bytes(Bytes2Int(A, BE, Unsigned) +Int Bytes2Int(B, BE, Unsigned), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b- => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               Int2Bytes(Bytes2Int(A, BE, Unsigned) -Int Bytes2Int(B, BE, Unsigned), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
     andBool Bytes2Int(A, BE, Unsigned) -Int Bytes2Int(B, BE, Unsigned) >=Int 0
  rule <k> b- => #panic(INT_UNDERFLOW) ... </k>
       <stack> B:Bytes : A:Bytes : _ </stack>
    requires Bytes2Int(A, BE, Unsigned) -Int Bytes2Int(B, BE, Unsigned) <Int 0
  rule <k> b/ => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               Int2Bytes(Bytes2Int(A, BE, Unsigned) /Int Bytes2Int(B, BE, Unsigned), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
     andBool Bytes2Int(B, BE, Unsigned) >Int 0
  rule <k> b/ => #panic(DIV_BY_ZERO) ... </k>
       <stack> B:Bytes : _:Bytes : _  </stack>
    requires Bytes2Int(B, BE, Unsigned) ==Int 0
  rule <k> b% => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               Int2Bytes(Bytes2Int(A, BE, Unsigned) %Int Bytes2Int(B, BE, Unsigned), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
     andBool Bytes2Int(B, BE, Unsigned) >Int 0
  rule <k> b% => #panic(DIV_BY_ZERO) ... </k>
       <stack> B:Bytes : _:Bytes : _  </stack>
    requires Bytes2Int(B, BE, Unsigned) ==Int 0
  rule <k> b* => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               Int2Bytes(Bytes2Int(A, BE, Unsigned) *Int Bytes2Int(B, BE, Unsigned), BE, Unsigned) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b< => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               bool2Int (Bytes2Int(A, BE, Unsigned) <Int Bytes2Int(B, BE, Unsigned)) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b> => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               bool2Int (Bytes2Int(A, BE, Unsigned) >Int Bytes2Int(B, BE, Unsigned)) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b<= => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               bool2Int (Bytes2Int(A, BE, Unsigned) <=Int Bytes2Int(B, BE, Unsigned)) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b>= => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               bool2Int (Bytes2Int(A, BE, Unsigned) >=Int Bytes2Int(B, BE, Unsigned)) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b== => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               bool2Int (Bytes2Int(A, BE, Unsigned) ==Int Bytes2Int(B, BE, Unsigned)) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> b!= => .K ... </k>
       <stack> B:Bytes : A:Bytes : XS =>
               bool2Int (Bytes2Int(A, BE, Unsigned) =/=Int Bytes2Int(B, BE, Unsigned)) : XS
       </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires lengthBytes(A) <=Int MAX_BYTE_MATH_SIZE
     andBool lengthBytes(B) <=Int MAX_BYTE_MATH_SIZE
  rule <k> OP:BinaryLogicalMathByteOpCode => .K ... </k>
       <stack> B : A : XS => BytesBitwiseOp(A, B, OP) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  syntax Bytes  ::=
    "BytesBitwiseOp" "(" Bytes "," Bytes "," BinaryLogicalMathByteOpCode ")" [function, klabel(BytesBitwiseOp)]
  rule BytesBitwiseOp(A, B, b|) =>
    padLeftBytes(Int2Bytes(Bytes2Int(A, BE, Unsigned) |Int Bytes2Int(B, BE, Unsigned), BE, Unsigned)
                , maxInt(lengthBytes(A), lengthBytes(B)), 0)
  rule BytesBitwiseOp(A, B, b&) =>
    padLeftBytes(Int2Bytes(Bytes2Int(A, BE, Unsigned) &Int Bytes2Int(B, BE, Unsigned), BE, Unsigned)
                , maxInt(lengthBytes(A), lengthBytes(B)), 0)
  rule BytesBitwiseOp(A, B, b^) =>
    padLeftBytes(Int2Bytes(Bytes2Int(A, BE, Unsigned) xorInt Bytes2Int(B, BE, Unsigned), BE, Unsigned)
                , maxInt(lengthBytes(A), lengthBytes(B)), 0)
  rule <k> b~ => .K ... </k>
       <stack> A : XS => BytesBitwiseOp(A, padLeftBytes(.Bytes, lengthBytes(A), 255), b^) : XS </stack>
  rule <k> getbyte => .K ... </k>
       <stack> B : ARRAY : XS => ARRAY[B] : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires 0 <=Int B andBool B <Int lengthBytes(ARRAY)
  rule <k> getbyte => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> B : ARRAY : _ </stack>
    requires 0 >Int B orBool B >=Int lengthBytes(ARRAY)
  rule <k> setbyte => .K ... </k>
       <stack> C : B : ARRAY : XS => ARRAY[B <- C] : XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires 0 <=Int B andBool B <Int lengthBytes(ARRAY)
             andBool 0 <=Int C andBool C <=Int MAX_UINT8
  rule <k> setbyte => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> B : ARRAY : _ </stack>
    requires 0 >Int B orBool B >=Int lengthBytes(ARRAY)
  rule <k> setbyte => #panic(ILL_TYPED_STACK) ... </k>
       <stack> C : _ : _ : _ </stack>
    requires 0 >Int C orBool C >Int MAX_UINT8
  rule <k> setbit => .K ... </k>
      <stack> C : B : ARRAY:Bytes : XS => setBitInBytes(ARRAY, B, C) : XS </stack>
      <stacksize> S => S -Int 2 </stacksize>
   requires 0 <=Int B andBool B <Int lengthBytes(ARRAY) *Int 8
    andBool 0 <=Int C andBool C <Int 2
  rule <k> setbit => #panic(ILL_TYPED_STACK) ... </k>
      <stack> C : _ : _:Bytes : _ </stack>
   requires notBool (0 <=Int C andBool C <Int 2)
  rule <k> setbit => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
      <stack> _ : B : ARRAY:Bytes : _ </stack>
   requires notBool (0 <=Int B andBool B <Int lengthBytes(ARRAY) *Int 8)
  syntax Bytes  ::=
    "setBitInBytes" "(" Bytes "," Int "," Int ")" [function, klabel(setBitInBytes)]
  rule setBitInBytes(ARRAY, B, V) =>
         ARRAY[B divInt 8 <- setBitUInt8( ARRAY[B divInt 8]
                                        , 7 -Int B modInt 8
                                        , V)]
  syntax Int  ::=
    "setBitUInt8" "(" Int "," Int "," Int ")" [function, klabel(setBitUInt8)]
  | "setBitUInt64" "(" Int "," Int "," Int ")" [function, klabel(setBitUInt64)]
  rule setBitUInt8(X, B, 0) => X &Int (~Int (1 <<Int B))
   requires 0 <=Int X andBool X <=Int MAX_UINT8
    andBool 0 <=Int B andBool B <Int 8
  rule setBitUInt8(X, B, 1) => X |Int (1 <<Int B)
   requires 0 <=Int X andBool X <=Int MAX_UINT8
    andBool 0 <=Int B andBool B <Int 8
  rule setBitUInt64(X, B, 0) => X &Int (~Int (1 <<Int B))
   requires 0 <=Int X andBool X <=Int MAX_UINT64
    andBool 0 <=Int B andBool B <Int 64
  rule setBitUInt64(X, B, 1) => X |Int (1 <<Int B)
   requires 0 <=Int X andBool X <=Int MAX_UINT64
    andBool 0 <=Int B andBool B <Int 64
  rule <k> setbit => .K ... </k>
       <stack> C : B : I:Int : XS => setBitUInt64(I, B, C) : XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires 0 <=Int I andBool I <=Int MAX_UINT64
     andBool 0 <=Int B andBool B <Int 64
     andBool 0 <=Int C andBool C <Int 2
  rule <k> setbit => #panic(ILL_TYPED_STACK) ... </k>
       <stack> C : _ : _:Int : _ </stack>
    requires notBool (0 <=Int C andBool C <Int 2)
  rule <k> setbit => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> _ : B : _:Int : _ </stack>
    requires notBool (0 <=Int B andBool B <Int 64)
  rule <k> getbit => .K ... </k>
      <stack> B : ARRAY:Bytes : XS => getBitFromBytes(ARRAY, B) : XS </stack>
      <stacksize> S => S -Int 1 </stacksize>
    requires 0 <=Int B andBool B <Int lengthBytes(ARRAY) *Int 8
  rule <k> getbit => #panic(INDEX_OUT_OF_BOUNDS) </k>
      <stack> B : ARRAY:Bytes : _ </stack>
    requires notBool (0 <=Int B andBool B <Int lengthBytes(ARRAY) *Int 8)
  syntax Int  ::=
    "getBitFromBytes" "(" Bytes "," Int ")" [function, klabel(getBitFromBytes)]
  rule getBitFromBytes(ARRAY, B) =>
      bitRangeInt( ARRAY[B divInt 8]
                 , 7 -Int B modInt 8
                 , 1)
  rule <k> getbit => .K ... </k>
       <stack> B : I:Int : XS => bitRangeInt(I, B, 1) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires 0 <=Int I andBool I <=Int MAX_UINT64 andBool
             0 <=Int B andBool B <Int 64
  rule <k> getbit => #panic(INDEX_OUT_OF_BOUNDS) ... </k>
       <stack> B : _:Int : _  </stack>
    requires notBool (0 <=Int B andBool B <Int 64)
  rule <k> intcblock N VL => .K ... </k>
       <intcblock> _ => genIntcBlockMap(N, 0, VL) </intcblock>
  rule <k> intc I => .K ... </k>
       <intcblock> INTS  </intcblock>
       <stack> XS => ({INTS[I]}:>TValue) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
     andBool (I:Int in_keys(INTS))
  rule <k> intc_0 => intc 0 ... </k>
  rule <k> intc_1 => intc 1 ... </k>
  rule <k> intc_2 => intc 2 ... </k>
  rule <k> intc_3 => intc 3 ... </k>
  rule <k> bytecblock N VPL => .K ... </k>
       <bytecblock> _ => genBytecBlockMap(N, 0, VPL) </bytecblock>
  rule <k> bytec I => .K ... </k>
       <bytecblock> I |-> V ... </bytecblock>
       <stack> XS => V : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> bytec_0 => bytec 0 ... </k>
  rule <k> bytec_1 => bytec 1 ... </k>
  rule <k> bytec_2 => bytec 2 ... </k>
  rule <k> bytec_3 => bytec 3 ... </k>
  rule <k> pushint I => .K ... </k>
       <stack> XS => normalizeI(I) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> pushbytes B => .K ... </k>
       <stack> XS => normalize(B) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> addr B => .K ... </k>
       <stack> XS => normalize(B) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> int I => .K ... </k>
       <stack> XS => normalizeI(I) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> byte B => .K ... </k>
       <stack> XS => normalize(B) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> method METHOD => .K ... </k>
       <stack> XS => methodSelector(METHOD) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> _:PseudoOpCode => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  syntax Map  ::=
    "genIntcBlockMap" "(" Int "," Int "," TValueNeList ")" [function, klabel(genIntcBlockMap)]
  rule genIntcBlockMap(N, I, V VL) =>
         I |-> V
         genIntcBlockMap(N -Int 1, I +Int 1, VL)
    requires N >Int 1
  rule genIntcBlockMap(1, I, V) => I |-> V
  syntax Map  ::=
    "genBytecBlockMap" "(" Int "," Int "," TValuePairNeList ")" [function, klabel(genBytecBlockMap)]
  rule genBytecBlockMap(N, I, (_, V) VPL) =>
         I |-> V
         genBytecBlockMap(N -Int 1, I +Int 1, VPL)
    requires N >Int 1
  rule genBytecBlockMap(1, I, (_, V)) => I |-> V
  syntax TBytes  ::=
    "methodSelector" "(" TBytes ")" [function, klabel(methodSelector), total]
  rule methodSelector(METHOD) => substrBytes(String2Bytes(Sha512_256raw(METHOD)), 0, 4)
  rule <k> bnz L => jump(L) ... </k>
       <stack> I : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I >Int 0
  rule <k> bnz _ => .K ... </k>
       <stack> I : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I <=Int 0
  rule <k> bz L => jump(L) ... </k>
       <stack> I : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I <=Int 0
  rule <k> bz _ => .K ... </k>
       <stack> I : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires I >Int 0
  rule <k> b L => jump(L) ... </k>
  rule <k> return ~> #incrementPC() ~> #fetchOpcode() => #finalizeExecution() ... </k>
        <stack> (I:Int) : _XS => I : .TStack </stack>
        <stacksize> _ => 1 </stacksize>
  rule <k> (_ :):LabelCode => .K ... </k>
  rule <k> assert => .K ... </k>
       <stack> (X:Int) : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires X >Int 0
  rule <k> assert => #panic(ASSERTION_VIOLATION) ... </k>
       <stack> (X:Int) : _ </stack>
    requires X ==Int 0
  rule <k> assert => #panic(IMPOSSIBLE_NEGATIVE_NUMBER) ... </k>
       <stack> (X:Int) : _ </stack>
    requires X <Int 0
  syntax KItem  ::=
    "jump" "(" Label ")" [klabel(jump)]
  rule <k> jump(L) => .K ... </k>
       <pc> _ => getLabelAddress(L) </pc>
       <jumped> _ => true </jumped>
       <labels> LL </labels>
    requires L in_labels LL
  rule <k> jump(L) => #panic(ILLEGAL_JUMP) ... </k>
       <labels> LL </labels>
    requires notBool (L in_labels LL)
  syntax StackFrame  ::=
    "frame" "(" Int "," Int "," Int "," Int ")" [klabel(frame)]
  | "frame" "(" Int "," Int ")" [klabel(frame)]
  syntax Int  ::=
    "getStackPtr" "(" ")" [function, klabel(getStackPtr)]
  rule [[ getStackPtr() => PTR ]]
       <callStack> ListItem(frame(_, PTR, _, _)) ... </callStack>
  rule [[ getStackPtr() => PTR ]]
       <callStack> ListItem(frame(_, PTR)) ... </callStack>
  rule <k> callsub TARGET => callSubroutine(TARGET) ... </k>
  rule <k> retsub => returnSubroutine() ... </k>
  syntax KItem  ::=
    "callSubroutine" "(" Label ")" [klabel(callSubroutine)]
  rule <k> callSubroutine(TARGET) => .K ... </k>
       <pc> PC => getLabelAddress(TARGET) </pc>
       <jumped> _ => true </jumped>
       <labels> LL </labels>
       <stack> S </stack>
       <callStack> XS => ListItem(frame(PC +Int 1, #sizeTStack(S))) XS </callStack>
    requires  (TARGET in_labels LL)
      andBool (size(XS) <Int MAX_CALLSTACK_DEPTH)
  rule <k> callSubroutine(_TARGET) => #panic(CALLSTACK_OVERFLOW) ... </k>
       <callStack> XS </callStack>
    requires size(XS) >=Int MAX_CALLSTACK_DEPTH
  rule <k> callSubroutine(TARGET) => #panic(ILLEGAL_JUMP) ... </k>
       <labels> LL </labels>
    requires notBool(TARGET in_labels LL)
  syntax KItem  ::=
    "returnSubroutine" "(" ")" [klabel(returnSubroutine)]
  rule <k> returnSubroutine() => .K ... </k>
       <pc> _ => RETURN_PC </pc>
       <jumped> _ => true </jumped>
       <stack> S => #let CLRSTCK = #drop((#sizeTStack(S) -Int STACK_PTR) -Int RETS, S) #in
             (#take(RETS, CLRSTCK) #drop(ARGS +Int RETS, CLRSTCK))
       </stack>
       <stacksize> SIZE => SIZE -Int (#sizeTStack(S) -Int STACK_PTR) -Int RETS </stacksize>
       <callStack> ListItem(frame(RETURN_PC, STACK_PTR, ARGS, RETS)) XS => XS </callStack>
  rule <k> returnSubroutine() => .K ... </k>
       <pc> _ => RETURN_PC </pc>
       <jumped> _ => true </jumped>
       <callStack> ListItem(frame(RETURN_PC, _)) XS => XS </callStack>
  rule <k> returnSubroutine() => #panic(CALLSTACK_UNDERFLOW) ... </k>
       <pc> _ </pc>
       <callStack> .List </callStack>
  rule <k> proto ARGS RETS => .K ... </k>
       <callStack> ListItem(frame(_, _, _ => ARGS, _ => RETS)) ... </callStack>
    requires (ARGS >=Int 0) andBool (RETS >=Int 0)
  rule <k> proto ARGS RETS => .K ... </k>
       <callStack> ListItem(frame(RETURN_PC, STACK_PTR) => frame(RETURN_PC, STACK_PTR, ARGS, RETS)) ... </callStack>
    requires (ARGS >=Int 0) andBool (RETS >=Int 0)
  rule <k> frame_dig N => .K ... </k>
       <stack> XS => XS{getStackPtr() +Int N} : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> frame_bury N => .K ... </k>
       <stack> X : XS => XS{getStackPtr() +Int N <- X} </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> pop => .K ... </k>
       <stack> _ : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> dup => .K ... </k>
       <stack> X : XS => X : X : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> dup => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> dup2 => .K ... </k>
       <stack> V2 : V1 : XS => V2 : V1 : V2 : V1 : XS </stack>
       <stacksize> S => S +Int 2 </stacksize>
    requires S +Int 1 <Int MAX_STACK_DEPTH
  rule <k> dup2 => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S +Int 1 >=Int MAX_STACK_DEPTH
  rule <k> dig N => .K ... </k>
       <stack> STACK => STACK[N]:STACK </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH andBool
             0 <=Int N andBool N <Int S
  rule <k> dig _ => #panic(STACK_OVERFLOW) ... </k>
       <stack> _ </stack>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> dig N => #panic(STACK_UNDERFLOW) ... </k>
       <stack> _ </stack>
       <stacksize> S </stacksize>
    requires notBool (0 <=Int N andBool N <Int S)
  rule <k> cover N => .K ... </k>
       <stack> X : STACK => #take(N, STACK) (X : #drop(N, STACK)) </stack>
       <stacksize> S </stacksize>
    requires 0 <=Int N andBool N <Int S
  rule <k> cover N => #panic(STACK_UNDERFLOW) ... </k>
       <stack> _ </stack>
       <stacksize> S </stacksize>
    requires notBool (0 <=Int N andBool N <Int S)
  rule <k> uncover N => .K ... </k>
       <stack> STACK => STACK [ N ] : (#take(N, STACK) #drop(N +Int 1, STACK)) </stack>
       <stacksize> S </stacksize>
    requires 0 <=Int N andBool N <Int S
  rule <k> uncover N => #panic(STACK_UNDERFLOW) ... </k>
       <stack> _ </stack>
       <stacksize> S </stacksize>
    requires notBool (0 <=Int N andBool N <Int S)
  rule <k> swap => .K ... </k>
       <stack> X : Y : XS => Y : X : XS </stack>
  rule <k> swap => #panic(STACK_UNDERFLOW) ... </k>
       <stack> _:.TStack </stack>
  rule <k> select => .K ... </k>
       <stack> A : B : _ : XS =>
               B : XS
       </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires int2Bool(A)
  rule <k> select => .K ... </k>
       <stack> A : _ : C : XS =>
               C : XS
       </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires notBool (int2Bool(A))
  rule <k> bury N:Int => .K ... </k>
       <stack> A:TValue : STACK => (#take(N -Int 1, STACK) A : #drop(N, STACK)) </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires 0 <Int N andBool N <Int S
  rule <k> bury N:Int => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires notBool(0 <Int N andBool N <Int S)
  rule <k> popn N:Int => .K ... </k>
       <stack> STACK => #drop(N, STACK) </stack>
       <stacksize> S => S -Int N </stacksize>
    requires N <=Int S
  rule <k> popn N:Int => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires N >Int S
  rule <k> dupn N => dupn (N -Int 1) ... </k>
       <stack> X : XS => X : X : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires N >Int 0
     andBool S <Int MAX_STACK_DEPTH
  rule <k> dupn 0 => .K ... </k>
  rule <k> dupn N => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S +Int N >Int MAX_STACK_DEPTH
  rule <k> txn I => gtxn getTxnGroupIndex(getCurrentTxn()) I ... </k>
  rule <k> txn I J => txna I J ... </k>
  rule <k> gtxn G I => loadFromGroup(G, I) ... </k>
  rule <k> gtxns I => loadFromGroup(G, I) ... </k>
       <stack> G : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> txna I J => gtxna getTxnGroupIndex(getCurrentTxn()) I J ... </k>
  rule <k> txnas I => gtxnas getTxnGroupIndex(getCurrentTxn()) I ... </k>
  rule <k> gtxna G I J => loadFromGroup(G, I, J) ... </k>
  rule <k> gtxnas G I => loadFromGroup(G, I, J) ... </k>
       <stack> J : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> gtxnsa I J => loadFromGroup(G, I, J) ... </k>
       <stack> G : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> gtxnsas I => loadFromGroup(G, I, J) ... </k>
       <stack> J : G : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
  rule <k> global I => .K ... </k>
       <stack> XS => getGlobalField(I) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
  rule <k> _:BlockchainOpCode => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  syntax KItem  ::=
    "loadFromGroup" "(" Int "," TxnField ")" [klabel(loadFromGroup)]
  rule <k> loadFromGroup(GROUP_IDX, FIELD) => .K ... </k>
       <stacksize> S => S +Int 1 </stacksize>
       <stack> XS => fromMaybeTVal(getGroupFieldByIdx(GROUP_ID, GROUP_IDX, FIELD)) : XS </stack>
       <currentTx> CURRENT_TX_ID </currentTx>
       <transaction>
         <txID> CURRENT_TX_ID </txID>
         <groupID> GROUP_ID </groupID>
         <groupIdx> CURRENT_GROUP_IDX </groupIdx>
         ...
       </transaction>
    requires isTValue(getGroupFieldByIdx(GROUP_ID, GROUP_IDX, FIELD))
    andBool    S <Int MAX_STACK_DEPTH
    andBool    (notBool(isTxnDynamicField(FIELD))
    orElseBool GROUP_IDX <Int (CURRENT_GROUP_IDX))
  rule <k> loadFromGroup(GROUP_IDX, _:TxnDynamicField) => #panic(FUTURE_TXN) ...</k>
       <currentTx> CURRENT_TX_ID </currentTx>
       <transaction>
         <txID> CURRENT_TX_ID </txID>
         <groupIdx> CURRENT_GROUP_IDX </groupIdx>
         ...
       </transaction>
    requires GROUP_IDX >=Int CURRENT_GROUP_IDX
  rule <k> loadFromGroup(_, _) => #panic(STACK_OVERFLOW) ...</k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> loadFromGroup(GROUP_IDX, FIELD) => #panic(TXN_ACCESS_FAILED) ...</k>
       <currentTx> CURRENT_TX_ID </currentTx>
       <transaction>
         <txID> CURRENT_TX_ID </txID>
         <groupID> GROUP_ID </groupID>
         ...
       </transaction>
    requires notBool(isTValue(getGroupFieldByIdx(GROUP_ID, GROUP_IDX, FIELD)))
  syntax TValue  ::=
    "fromMaybeTVal" "(" MaybeTValue ")" [function, klabel(fromMaybeTVal)]
  rule fromMaybeTVal(V:TValue) => V
  syntax KItem  ::=
    "loadFromGroup" "(" Int "," TxnaField "," Int ")" [klabel(loadFromGroup)]
  rule <k> loadFromGroup(GROUP_IDX, FIELD, IDX) => .K ...</k>
       <stack> XS => fromMaybeTVal(getGroupFieldByIdx(GROUP_ID, GROUP_IDX, FIELD, IDX)) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <currentTx> CURRENT_TX_ID </currentTx>
       <transaction>
         <txID> CURRENT_TX_ID </txID>
         <groupID> GROUP_ID </groupID>
         <groupIdx> CURRENT_GROUP_IDX </groupIdx>
         ...
       </transaction>
    requires   isTValue(getGroupFieldByIdx(GROUP_ID, GROUP_IDX, FIELD, IDX))
    andBool    S <Int MAX_STACK_DEPTH
    andBool    (notBool(isTxnaDynamicField(FIELD))
    orElseBool GROUP_IDX <Int CURRENT_GROUP_IDX)
  rule <k> loadFromGroup(GROUP_IDX, _:TxnaDynamicField, _) => #panic(FUTURE_TXN) ...</k>
       <currentTx> CURRENT_TX_ID </currentTx>
       <transaction>
         <txID> CURRENT_TX_ID </txID>
         <groupIdx> CURRENT_GROUP_IDX </groupIdx>
         ...
       </transaction>
    requires GROUP_IDX >=Int CURRENT_GROUP_IDX
  rule <k> loadFromGroup(_, _, _) => #panic(STACK_OVERFLOW) ...</k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> loadFromGroup(GROUP_IDX, FIELD, IDX) => #panic(TXN_ACCESS_FAILED) ...</k>
       <currentTx> CURRENT_TX_ID </currentTx>
       <transaction>
         <txID> CURRENT_TX_ID </txID>
         <groupID> GROUP_ID </groupID>
         ...
       </transaction>
    requires   notBool(isTValue(getGroupFieldByIdx(GROUP_ID, GROUP_IDX, FIELD, IDX)))
  rule <k> load I => .K ... </k>
       <stack> XS => ({M[I]}:>TValue) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <scratch> M </scratch>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool I in_keys(M)
     andBool S <Int MAX_STACK_DEPTH
  rule <k> load I => .K ... </k>
       <stack> XS => 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <scratch> M => M[I <- 0] </scratch>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool notBool (I in_keys(M))
     andBool S <Int MAX_STACK_DEPTH
  rule <k> store I => .K ... </k>
       <stack> V : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
       <scratch> M => M[I <- V] </scratch>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
  rule <k> load I => #panic(INVALID_SCRATCH_LOC) ... </k>
    requires I <Int 0 orBool I >=Int MAX_SCRATCH_SIZE
  rule <k> load _ => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> store I => #panic(INVALID_SCRATCH_LOC) ... </k>
    requires I <Int 0 orBool I >=Int MAX_SCRATCH_SIZE
  rule <k> loads => .K ... </k>
       <stack> I : XS => ({M[I]}:>TValue) : XS </stack>
       <scratch> M </scratch>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool I in_keys(M)
  rule <k> loads => .K ... </k>
       <stack> I : XS => 0 : XS </stack>
       <scratch> M </scratch>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool notBool(I in_keys(M))
  rule <k> loads => #panic(INVALID_SCRATCH_LOC) ... </k>
       <stack> I : _ </stack>
    requires I <Int 0 orBool I >=Int MAX_SCRATCH_SIZE
  rule <k> stores => .K ... </k>
       <stack> V : I : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
       <scratch> M => M[I <- V] </scratch>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
  rule <k> stores => #panic(INVALID_SCRATCH_LOC) ... </k>
       <stack> _ : I : _ </stack>
    requires I <Int 0 orBool I >=Int MAX_SCRATCH_SIZE
  rule <k> balance => #balance getAccountParamsField(AcctBalance, {accountReference(A)}:>TValue) ... </k>
       <stack> (A:TValue) : _ </stack>
    requires isTValue(accountReference(A))
  rule <k> balance => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (A:TValue) : _ </stack>
    requires notBool isTValue(accountReference(A))
  syntax KItem  ::=
    "#balance" MaybeTValue
  rule <k> #balance BAL:TUInt64 => .K ...</k>
       <stack> _ : XS => BAL : XS </stack>
  rule <k> #balance _ => #panic(TXN_ACCESS_FAILED) </k>   [owise]
  rule <k> min_balance => #min_balance getAccountParamsField(AcctMinBalance, {accountReference(A)}:>TValue) ... </k>
       <stack> (A:TValue) : _ </stack>
    requires isTValue(accountReference(A))
  rule <k> min_balance => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (A:TValue) : _ </stack>
    requires notBool isTValue(accountReference(A))
  syntax KItem  ::=
    "#min_balance" MaybeTValue
  rule <k> #min_balance MIN_BAL:TUInt64 => .K ...</k>
       <stack> _ : XS => MIN_BAL : XS </stack>
  rule <k> #min_balance _ => #panic(TXN_ACCESS_FAILED) </k>   [owise]
  rule <k> log => .K ...</k>
       <stack> (MSG:TBytes : XS) => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <logData> LOG => append(MSG, LOG) </logData>
         <logSize> SIZE => SIZE +Int lengthBytes({MSG}:>Bytes) </logSize>
         ...
       </transaction>
    requires size(LOG) <Int PARAM_MAX_LOG_CALLS
  rule <k> log => #panic(ILL_TYPED_STACK) ...</k>
        <stack> _:TUInt64 : _ </stack>
  rule <k> log => #panic(LOG_CALLS_EXCEEDED) ...</k>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <logData> LOG </logData>
         ...
       </transaction>
    requires size(LOG) >=Int PARAM_MAX_LOG_CALLS
  rule <k> log => #panic(LOG_SIZE_EXCEEDED) ...</k>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <logSize> SIZE </logSize>
         ...
       </transaction>
    requires SIZE >=Int PARAM_MAX_LOG_SIZE
  rule <k> app_opted_in =>
           #app_opted_in hasOptedInApp({appReference(APP)}:>TValue, {accountReference(A)}:>TValue) ... </k>
       <stack> (APP:Int) : (A:TValue) : _ </stack>
    requires isTValue(appReference(APP)) andBool isTValue(accountReference(A))
  rule <k> app_opted_in  => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> APP:Int : A:TValue : _:TStack </stack>
    requires notBool (isTValue(appReference(APP)) andBool isTValue(accountReference(A)))
  rule <k> app_opted_in => #panic(ILL_TYPED_STACK) ... </k>
       <stack> _:TBytes : _:TValue : _:TStack </stack>
  syntax KItem  ::=
    "#app_opted_in" Bool
  rule <k> #app_opted_in B => .K ... </k>
       <stack> _ : _ : XS => (#if B #then 1 #else 0 #fi) : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> app_local_get =>
           #app_local_get getAppLocal({accountReference(A)}:>TValue
                                     , getGlobalField(CurrentApplicationID), KEY) ... </k>
       <stack> (KEY:Bytes) : (A:TValue) : _ </stack>
    requires isTValue(accountReference(A))
  rule <k> app_local_get => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (_:Bytes) : (A:TValue) : _ </stack>
    requires notBool isTValue(accountReference(A))
  rule <k> app_local_get => #panic(ILL_TYPED_STACK) ... </k>
       <stack> _:TUInt64 : _ : _ </stack>
  syntax KItem  ::=
    "#app_local_get" MaybeTValue
  rule <k> #app_local_get V:TValue => .K ... </k>
       <stack> _ : _ : XS => V : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires (notBool isInt(V)) orElseBool {V}:>Int >=Int 0
  syntax KItem  ::=
    "#app_local_get" MaybeTValue
  rule <k> #app_local_get V:TValue => .K ... </k>
       <stack> _ : _ : XS => 0 : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires isInt(V) andThenBool {V}:>Int <Int 0
  rule <k> #app_local_get NoTValue => #panic(TXN_ACCESS_FAILED) ... </k>
  rule <k> app_local_get_ex =>
           #app_local_get_ex getAppLocal({accountReference(A)}:>TValue, {appReference(APP)}:>TValue, KEY) ... </k>
       <stack> (KEY:Bytes) : (APP:TUInt64) : (A:TValue) : _ </stack>
    requires isTValue(accountReference(A)) andBool isTValue(appReference(APP))
  rule <k> app_local_get_ex => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (_:Bytes) : (APP:TUInt64) : (A:TValue) : _ </stack>
    requires notBool (isTValue(accountReference(A)) andBool isTValue(appReference(APP)))
  rule <k> app_local_get_ex => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (KEY:TValue) : (APP:TValue) : (_:TValue) : _ </stack>
    requires isInt(KEY) orBool isBytes(APP)
  syntax KItem  ::=
    "#app_local_get_ex" MaybeTValue
  rule <k> #app_local_get_ex V => .K ... </k>
       <stack> _ : _ : _ : XS => 1 : V : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires (notBool isInt(V)) orElseBool {V}:>Int >=Int 0
  rule <k> #app_local_get_ex V => .K ... </k>
       <stack> _ : _ : _ : XS => 0 : 0 : XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires isInt(V) andThenBool {V}:>Int <Int 0
  rule <k> #app_local_get_ex NoTValue => #panic(TXN_ACCESS_FAILED) ... </k>
  syntax Int  ::=
    "getLocalByteLimit" "(" Int ")" [function, klabel(getLocalByteLimit)]
  rule [[ getLocalByteLimit(APP) => X ]]
       <app>
         <appID> APP </appID>
         <localNumBytes> X </localNumBytes>
         ...
       </app>
  syntax Int  ::=
    "getLocalIntLimit" "(" Int ")" [function, klabel(getLocalIntLimit)]
  rule [[ getLocalIntLimit(APP) => X ]]
       <app>
         <appID> APP </appID>
         <localNumInts> X </localNumInts>
         ...
       </app>
  rule <k> app_local_put => #app_local_put {accountReference(A)}:>TValue
                                           getGlobalField(CurrentApplicationID) ... </k>
       <stack> (_:TValue) : (_:Bytes) : (A:TValue) : _ </stack>
    requires isTValue(accountReference(A))
  rule <k> app_local_put => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (_:TValue) : (_:Bytes) : (A:TValue) : _ </stack>
    requires notBool isTValue(accountReference(A))
  rule <k> app_local_put => #panic(ILL_TYPED_STACK) ...  </k>
       <stack> _:TValue : _:TUInt64 : _:TValue : _ </stack>
  syntax KItem  ::=
    "#app_local_put" TValue TValue
  rule <k> #app_local_put ADDR APP => .K ... </k>
       <stack> (NEWVAL:Int) : (KEY:Bytes) : _ : XS => XS </stack>
       <stacksize> S => S -Int 3 </stacksize>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localInts> MI => MI[KEY <- NEWVAL] </localInts>
             <localBytes> MB => MB[KEY <- undef]  </localBytes>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
    requires size(MI[KEY <- NEWVAL]) <=Int getLocalIntLimit(APP)
     andBool lengthBytes(KEY) <=Int PARAM_MAX_KEY_SIZE
     andBool lengthBytes(KEY) +Int sizeInBytes(NEWVAL) <=Int PARAM_MAX_SUM_KEY_VALUE_SIZE
  rule <k> #app_local_put ADDR APP => .K ... </k>
       <stack> (NEWVAL:Bytes) : (KEY:Bytes) : _ : XS => XS </stack>
       <stacksize> S => S -Int 3 </stacksize>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localInts> MI => MI[KEY <- undef] </localInts>
             <localBytes> MB => MB[KEY <- NEWVAL] </localBytes>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
    requires size(MB[KEY <- NEWVAL]) <=Int getLocalByteLimit(APP)
     andBool lengthBytes(KEY) <=Int PARAM_MAX_KEY_SIZE
     andBool lengthBytes(KEY) +Int sizeInBytes(NEWVAL) <=Int PARAM_MAX_SUM_KEY_VALUE_SIZE
     andBool lengthBytes(NEWVAL) <=Int PARAM_MAX_BYTE_VALUE_SIZE
  rule <k> #app_local_put _ _ => #panic(KEY_TOO_LARGE) ... </k>
       <stack> _ : (KEY:Bytes) : _ : _ </stack>
    requires lengthBytes(KEY) >Int PARAM_MAX_KEY_SIZE
  rule <k> #app_local_put _ _ => #panic(KEY_VALUE_TOO_LARGE) ... </k>
       <stack> (NEWVAL:TValue) : (KEY:Bytes) : _ : _ </stack>
    requires lengthBytes(KEY) +Int sizeInBytes(NEWVAL) >Int PARAM_MAX_SUM_KEY_VALUE_SIZE
  rule <k> #app_local_put _ _ => #panic(BYTE_VALUE_TOO_LARGE) ... </k>
       <stack> (NEWVAL:Bytes) : _ : _ : _ </stack>
    requires lengthBytes(NEWVAL) >Int PARAM_MAX_BYTE_VALUE_SIZE
  rule <k> #app_local_put ADDR APP => #panic(LOCAL_INTS_EXCEEDED) ... </k>
       <stack> (NEWVAL:Int) : (KEY:Bytes) : _ : _ </stack>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localInts> M </localInts>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
    requires size(M[KEY <- NEWVAL]) >Int getLocalIntLimit(APP)
  rule <k> #app_local_put ADDR APP => #panic(LOCAL_BYTES_EXCEEDED) ... </k>
       <stack> (NEWVAL:Bytes) : (KEY:Bytes) : _ : _ </stack>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localBytes> M </localBytes>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
    requires size(M[KEY <- NEWVAL]) >Int getLocalByteLimit(APP)
  rule <k> #app_local_put ADDR APP => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> _ : _ : _ : XS => XS </stack>
       <stacksize> S => S -Int 3 </stacksize>
       <account>
         <address> ADDR </address>
         <appsOptedIn> OA </appsOptedIn> ...
       </account>
    requires notBool (APP in_optedInApps(<appsOptedIn> OA </appsOptedIn>))
  rule <k> #app_local_put ADDR _ => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> _ : _ : _ : XS => XS </stack>
       <stacksize> S => S -Int 3 </stacksize>
       <accountsMap> AMAP  </accountsMap>
    requires notBool (ADDR in_accounts(<accountsMap> AMAP </accountsMap>))
  rule <k> app_local_del => #app_local_del {accountReference(A)}:>TValue
                                           getGlobalField(CurrentApplicationID) ... </k>
       <stack> (_:Bytes) : (A:TValue) : _ </stack>
    requires isTValue(accountReference(A))
  rule <k> app_local_del => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (_:Bytes ) : (A:TValue) : _ </stack>
    requires notBool isTValue(accountReference(A))
  rule <k> app_local_del => #panic(ILL_TYPED_STACK) ... </k>
       <stack> _:TUInt64 : _ : _ </stack>
  syntax KItem  ::=
    "#app_local_del" TValue TValue
  rule <k> #app_local_del ADDR APP => .K ... </k>
       <stack> (KEY:Bytes) : _ : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           <optInApp>
             <optInAppID> APP </optInAppID>
             <localInts> MI => MI[KEY <- undef] </localInts>
             <localBytes> MB => MB[KEY <- undef] </localBytes>
             ...
           </optInApp> ...
         </appsOptedIn> ...
       </account>
  rule <k> #app_local_del ADDR APP => #panic(TXN_ACCESS_FAILED) ... </k>
       <account>
         <address> ADDR </address>
         <appsOptedIn> OA </appsOptedIn> ...
       </account>
    requires notBool (APP in_optedInApps(<appsOptedIn> OA </appsOptedIn>))
  rule <k> #app_local_del ADDR _ => #panic(TXN_ACCESS_FAILED) ... </k>
       <accountsMap> AMAP  </accountsMap>
    requires notBool (ADDR in_accounts(<accountsMap> AMAP </accountsMap>))
  rule <k> app_global_get =>
           #app_global_get getAppGlobal(getAppCell({AC[{getGlobalField(CurrentApplicationID)}:>Int]}:>Bytes, {getGlobalField(CurrentApplicationID)}:>Int), KEY) ... </k>
       <stack> (KEY:Bytes) : _ </stack>
       <appCreator>
         AC
       </appCreator>
  syntax KItem  ::=
    "#app_global_get" TValue
  rule <k> #app_global_get V => .K ... </k>
       <stack> (_:Bytes) : XS => V : XS </stack>
    requires (notBool isInt(V)) orElseBool {V}:>Int >=Int 0
  rule <k> #app_global_get V => .K ... </k>
       <stack> (_:Bytes) : XS => 0 : XS </stack>
    requires isInt(V) andThenBool {V}:>Int <Int 0
  syntax KItem  ::=
    "testAbc" "(" Bytes "," Int ")" [klabel(testAbc)]
  rule <k> testAbc(CREATOR_ADDR, APP_ID) => getAppCell(CREATOR_ADDR, APP_ID) ... </k>
  syntax AppCell  ::=
    "getAppCell" "(" Bytes "," Int ")" [function, klabel(getAppCell)]
  rule [[ getAppCell(CREATOR_ADDR, APP_ID) => <app> <appID> APP_ID </appID> APP_DATA </app> ]]
       <account>
         <address> CREATOR_ADDR </address>
         <app>
           <appID> APP_ID </appID>
           APP_DATA
         </app>
         ...
       </account>
  rule getAppCell(_, APP_ID) => <app> <appID> APP_ID </appID> ... </app>  [owise]
  rule <k> app_global_get_ex =>
           #app_global_get_ex getAppGlobal(getAppCell({AC[{appReference(APP)}:>Int]}:>Bytes, {appReference(APP)}:>Int), KEY) ... </k>
       <stack> (KEY:Bytes) : (APP:TUInt64) : _ </stack>
       <appCreator>
         AC
       </appCreator>

    requires isTValue(appReference(APP))
  rule <k> app_global_get_ex => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (_:Bytes) : (APP:TUInt64) : _ </stack>
    requires notBool isTValue(appReference(APP))
  rule <k> app_global_get_ex => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (KEY:TValue) : (I:TValue):_ </stack>
    requires isInt(KEY) orBool isBytes(I)
  syntax KItem  ::=
    "#app_global_get_ex" TValue
  rule <k> #app_global_get_ex V  => .K ... </k>
       <stack> (_:Bytes) : (_:TUInt64) : XS => 1 : V : XS </stack>
    requires (notBool isInt(V)) orElseBool {V}:>Int >=Int 0
  rule <k> #app_global_get_ex V => .K ... </k>
       <stack> (_:Bytes) : (_:TUInt64) : XS => 0 : 0 : XS </stack>
    requires isInt(V) andThenBool {V}:>Int <Int 0
  rule <k> app_global_put => #app_global_put getGlobalField(CurrentApplicationID) ... </k>
       <stack> (_:TValue) : (_:Bytes) : _ </stack>
  syntax KItem  ::=
    "#app_global_put" TValue
  rule <k> #app_global_put APP => .K ... </k>
       <stack> (NEWVAL:Int) : (KEY:Bytes) : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
       <app>
         <appID> APP </appID>
         <globalState>
           <globalInts> MI => MI[KEY <- NEWVAL] </globalInts>
           <globalBytes> MB => MB[KEY <- undef] </globalBytes>
           <globalNumInts>    GLOBAL_INTS </globalNumInts>
           ...
         </globalState>
         ...
       </app>
    requires size(MI[KEY <- NEWVAL]) <=Int GLOBAL_INTS
     andBool lengthBytes(KEY) <=Int PARAM_MAX_KEY_SIZE
     andBool lengthBytes(KEY) +Int sizeInBytes(NEWVAL) <=Int PARAM_MAX_SUM_KEY_VALUE_SIZE
  rule <k> #app_global_put APP => .K ... </k>
       <stack> (NEWVAL:Bytes) : (KEY:Bytes) : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
       <app>
         <appID> APP </appID>
         <globalState>
           <globalInts> MI => MI[KEY <- undef] </globalInts>
           <globalBytes> MB => MB[KEY <- NEWVAL] </globalBytes>
           <globalNumBytes>   GLOBAL_BYTES </globalNumBytes>
           ...
         </globalState>
         ...
       </app>
    requires size(MB[KEY <- NEWVAL]) <=Int GLOBAL_BYTES
     andBool lengthBytes(KEY) <=Int PARAM_MAX_KEY_SIZE
     andBool lengthBytes(KEY) +Int sizeInBytes(NEWVAL) <=Int PARAM_MAX_SUM_KEY_VALUE_SIZE
     andBool lengthBytes(NEWVAL) <=Int PARAM_MAX_BYTE_VALUE_SIZE
  rule <k> #app_global_put _ => #panic(KEY_TOO_LARGE) ... </k>
       <stack> _ : (KEY:Bytes) : _ </stack>
    requires lengthBytes(KEY) >Int PARAM_MAX_KEY_SIZE
  rule <k> #app_global_put _ => #panic(KEY_VALUE_TOO_LARGE) ... </k>
       <stack> (NEWVAL:TValue) : (KEY:Bytes) : _ </stack>
    requires lengthBytes(KEY) +Int sizeInBytes(NEWVAL) >Int PARAM_MAX_SUM_KEY_VALUE_SIZE
  rule <k> #app_global_put _ => #panic(BYTE_VALUE_TOO_LARGE) ... </k>
       <stack> (NEWVAL:Bytes) : _ : _ </stack>
    requires lengthBytes(NEWVAL) >Int PARAM_MAX_BYTE_VALUE_SIZE
  rule <k> #app_global_put APP => #panic(GLOBAL_INTS_EXCEEDED) ... </k>
       <stack> (NEWVAL:Int) : (KEY:Bytes) : _ </stack>
       <app>
         <appID> APP </appID>
         <globalState>
           <globalInts> M </globalInts>
           <globalNumInts>    GLOBAL_INTS </globalNumInts>
           <globalNumBytes>   _ </globalNumBytes>
           ...
         </globalState>
         ...
       </app>
    requires size(M[KEY <- NEWVAL]) >Int GLOBAL_INTS
  rule <k> #app_global_put APP => #panic(GLOBAL_BYTES_EXCEEDED) ... </k>
       <stack> (NEWVAL:Bytes) : (KEY:Bytes) : _ </stack>
       <app>
         <appID> APP </appID>
         <globalState>
           <globalBytes> M </globalBytes>
           <globalNumInts>    _ </globalNumInts>
           <globalNumBytes>   GLOBAL_BYTES </globalNumBytes>
           ...
         </globalState>
         ...
       </app>
    requires size(M[KEY <- NEWVAL]) >Int GLOBAL_BYTES
  rule <k> #app_global_put APP => .K ... </k>
       <stack> (_:TValue) : (_:Bytes) : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
       <accountsMap> AMAP  </accountsMap>
    requires notBool (APP in_apps(<accountsMap> AMAP </accountsMap>))
  rule <k> app_global_del => #app_global_del getGlobalField(CurrentApplicationID) ... </k>
       <stack> (_:Bytes) : _ </stack>
  syntax KItem  ::=
    "#app_global_del" TValue
  rule <k> #app_global_del APP => .K ... </k>
       <stack> (KEY:Bytes) : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
       <appsCreated>
         <app>
           <appID> APP </appID>
           <globalState>
             <globalInts> MI => MI[KEY <- undef] </globalInts>
             <globalBytes> MB => MB[KEY <- undef] </globalBytes>
             ...
           </globalState>
           ...
         </app>
         ...
       </appsCreated>
  rule <k> #app_global_del APP => .K ... </k>
       <stack> (_:Bytes) : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
       <accountsMap> AMAP  </accountsMap>
    requires notBool (APP in_apps(<accountsMap> AMAP </accountsMap>))
  rule <k> asset_holding_get FIELD =>
           #asset_holding_get getOptInAssetField(FIELD,
                                {accountReference(A)}:>TValue,
                                {asaReference(ASSET)}:>TValue)
           ...
       </k>
       <stack> (ASSET:TUInt64) : (A:TValue): _ </stack>
    requires isTValue(accountReference(A)) andBool isTValue(asaReference(ASSET))
  rule <k> asset_holding_get _ => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (ASSET:TUInt64) : (A:TValue) : _ </stack>
    requires notBool (isTValue(accountReference(A)) andBool isTValue(asaReference(ASSET)))
  rule <k> asset_holding_get _ => #panic(ILL_TYPED_STACK) ... </k>
       <stack> _:TBytes : _ : _ </stack>
  syntax KItem  ::=
    "#asset_holding_get" TValue
  rule <k> #asset_holding_get RET => .K ... </k>
       <stack> (_:Int) : _ : XS => 1 : RET : XS </stack>
    requires {RET}:>Int >=Int 0
  rule <k> #asset_holding_get RET => .K ... </k>
       <stack> (_:Int) : _ : XS => 0 : 0 : XS </stack>
    requires {RET}:>Int <Int 0
  rule <k> asset_params_get FIELD =>
           #asset_params_get getAssetParamsField(FIELD, {asaReference(A)}:>TValue)
       ...
       </k>
       <stack> (A:TUInt64) : XS => XS </stack>
       <stacksize> S </stacksize>
    requires S <Int MAX_STACK_DEPTH
     andBool isTValue(asaReference(A))
  rule <k> asset_params_get _ => #panic(TXN_ACCESS_FAILED) ... </k>
       <stack> (A:TUInt64) : _ </stack>
       <stacksize> S </stacksize>
    requires S <Int MAX_STACK_DEPTH
     andBool (notBool isTValue(asaReference(A)))
  rule <k> asset_params_get _ => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> asset_params_get _ => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Bytes) : _ </stack>
  syntax KItem  ::=
    "#asset_params_get" TValue
  rule <k> #asset_params_get RET => .K ... </k>
       <stack> XS => 1 : RET : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
     andBool (notBool (isInt(RET)) orElseBool {RET}:>Int >=Int 0 )
  rule <k> #asset_params_get RET => .K ... </k>
       <stack> XS => 0 : 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
     andBool (isInt(RET) andThenBool {RET}:>Int <Int 0)
  rule <k> app_params_get FIELD => .K ...</k>
       <stack> APP:Int : XS => 1 : {getAppParamsField(FIELD, APP)}:>TValue : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires isTValue(getAppParamsField(FIELD, APP))
     andBool S <Int MAX_STACK_DEPTH
  rule <k> app_params_get FIELD => .K ...</k>
       <stack> APP:Int : XS => 0 : 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires notBool(isTValue(getAppParamsField(FIELD, APP)))
  rule <k> app_params_get _ => #panic(STACK_OVERFLOW) ...</k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> app_params_get _ => #panic(STACK_UNDERFLOW) ...</k>
       <stacksize> S </stacksize>
    requires S <Int 1
  rule <k> app_params_get _ => #panic(ILL_TYPED_STACK) ...</k>
       <stack> _:Bytes : _ </stack>
  rule <k> acct_params_get FIELD => .K ...</k>
       <stack> ACCT : XS => 1 : {getAccountParamsField(FIELD, {accountReference(ACCT)}:>TValue)}:>TValue : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires (isTValue(accountReference(ACCT))
 andThenBool isTValue(getAccountParamsField(FIELD, {accountReference(ACCT)}:>TValue))
 andThenBool isInt(getAccountParamsField(AcctBalance, ACCT))
 andThenBool {getAccountParamsField(AcctBalance, ACCT)}:>Int >Int 0)
     andBool S <Int MAX_STACK_DEPTH
  rule <k> acct_params_get FIELD => .K ...</k>
       <stack> ACCT : XS => 0 : {getAccountParamsField(FIELD, {accountReference(ACCT)}:>TValue)}:>TValue : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires (isTValue(accountReference(ACCT))
 andThenBool isTValue(getAccountParamsField(FIELD, {accountReference(ACCT)}:>TValue))
 andThenBool isInt(getAccountParamsField(AcctBalance, ACCT))
 andThenBool {getAccountParamsField(AcctBalance, ACCT)}:>Int <=Int 0)
     andBool S <Int MAX_STACK_DEPTH
  rule <k> acct_params_get _ => #panic(TXN_ACCESS_FAILED) ...</k>
       <stack> ACCT : _ </stack>
    requires notBool(isTValue(accountReference(ACCT)))
  rule <k> acct_params_get _ => #panic(STACK_OVERFLOW) ...</k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> acct_params_get _ => #panic(STACK_UNDERFLOW) ...</k>
       <stacksize> S </stacksize>
    requires S <Int 1
  rule <k> box_create => #createBox(NAME, {boxAcct(NAME)}:>Bytes, SIZE) ... </k>
       <stack> SIZE:Int : NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires isBytes(boxAcct(NAME))
  syntax KItem  ::=
    "#createBox" "(" Bytes "," Bytes "," Int ")"
  rule <k> #createBox(NAME, ADDR, SIZE) => .K ... </k>
       <stack> XS => 1 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           (.Bag =>
           <box>
             <boxName> NAME </boxName>
             <boxData> padLeftBytes(.Bytes, SIZE, 0) </boxData>
           </box>)
           REST
         </boxes>
         <minBalance> MIN_BALANCE => MIN_BALANCE +Int (2500 +Int (400 *Int (lengthBytes(NAME) +Int SIZE))) </minBalance>
         ...
       </account>
    requires SIZE <=Int PARAM_MAX_BOX_SIZE
     andBool notBool(NAME in_boxes(<boxes> REST </boxes>))
     andBool ADDR ==K getGlobalField(CurrentApplicationAddress)
  rule <k> #createBox(NAME, ADDR, SIZE) => .K ... </k>
       <stack> XS => 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           <box>
             <boxName> NAME </boxName>
             <boxData> BYTES </boxData>
           </box>
           ...
         </boxes>
         ...
       </account>
    requires SIZE <=Int PARAM_MAX_BOX_SIZE
     andBool lengthBytes(BYTES) ==Int SIZE
  rule <k> #createBox(NAME, ADDR, SIZE) => #panic(CHANGED_BOX_SIZE) ... </k>
       <account>
         <address> ADDR </address>
         <boxes>
           <box>
             <boxName> NAME </boxName>
             <boxData> BYTES </boxData>
           </box>
           ...
         </boxes>
         ...
       </account>
    requires SIZE <=Int PARAM_MAX_BOX_SIZE
     andBool lengthBytes(BYTES) =/=Int SIZE
  rule <k> #createBox(_, ADDR, _) => #panic(BOX_CREATE_EXTERNAL) ... </k>
    requires ADDR =/=K getGlobalField(CurrentApplicationAddress)
  rule <k> box_create => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> _:Int : NAME:Bytes : _</stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_create => #panic(BOX_TOO_LARGE) ... </k>
       <stack> SIZE:Int : _ : _ </stack>
    requires SIZE >Int PARAM_MAX_BOX_SIZE
  rule <k> box_create => #panic(ILL_TYPED_STACK) ... </k>
       <stack> SIZE : NAME : _ </stack>
    requires isBytes(SIZE) orBool isInt(NAME)
  rule <k> box_create => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 2
  syntax KItem  ::=
    "#boxReplace" "(" Bytes "," Bytes "," Int "," Bytes ")"
  rule <k> box_replace => #boxReplace(NAME, {boxAcct(NAME)}:>Bytes, OFFSET, VAL) ... </k>
       <stack> VAL:Bytes : OFFSET:Int : NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 3 </stacksize>
    requires isBytes(boxAcct(NAME))
  rule <k> #boxReplace(NAME, ADDR, OFFSET, VAL) => .K ...</k>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES => replaceAtBytes(BYTES, OFFSET, VAL) </boxData>
         </box>
         ...
       </account>
    requires (lengthBytes(VAL) +Int OFFSET) <Int lengthBytes(BYTES)
  rule <k> #boxReplace(NAME, ADDR, OFFSET, VAL) => #panic(BOX_OUT_OF_BOUNDS) ...</k>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES </boxData>
         </box>
         ...
       </account>
    requires (lengthBytes(VAL) +Int OFFSET) >=Int lengthBytes(BYTES)
  rule <k> #boxReplace(NAME, ADDR, _, _) => #panic(BOX_NOT_FOUND) ...</k>
       <account>
         <address> ADDR </address>
         <boxes>
           BOXES
         </boxes>
         ...
       </account>
    requires notBool(NAME in_boxes(<boxes> BOXES </boxes>))
  rule <k> box_replace => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> _:Bytes : _:Int : NAME:Bytes : _ </stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_replace => #panic(ILL_TYPED_STACK) ... </k>
       <stack> VAL : OFFSET : NAME : _ </stack>
    requires isInt(VAL) orBool isBytes(OFFSET) orBool isInt(NAME)
  rule <k> box_replace => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 3
  syntax KItem  ::=
    "#boxPut" "(" Bytes "," Bytes "," Bytes ")"
  rule <k> box_put => #boxPut(NAME, {boxAcct(NAME)}:>Bytes, VAL) ... </k>
       <stack> VAL:Bytes : NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
    requires isBytes(boxAcct(NAME))
  rule <k> #boxPut(NAME, ADDR, VAL) => .K ...</k>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES => VAL </boxData>
         </box>
         ...
       </account>
    requires lengthBytes(VAL) ==Int lengthBytes(BYTES)
  rule <k> #boxPut(NAME, ADDR, VAL) => #panic(BOX_WRONG_LENGTH) ...</k>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES </boxData>
         </box>
         ...
       </account>
    requires lengthBytes(VAL) =/=Int lengthBytes(BYTES)
  rule <k> #boxPut(NAME, ADDR, VAL) => #createBox(NAME, ADDR, lengthBytes(VAL)) ~> #boxPut(NAME, ADDR, VAL) ...</k>
       <account>
         <address> ADDR </address>
         <boxes>
           BOXES
         </boxes>
         ...
       </account>
    requires notBool(NAME in_boxes(<boxes> BOXES </boxes>))
  rule <k> box_put => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> _:Bytes : NAME:Bytes : _ </stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_put => #panic(ILL_TYPED_STACK) ... </k>
       <stack> VAL : NAME : _ </stack>
    requires isInt(VAL) orBool isInt(NAME)
  rule <k> box_put => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 2
  syntax KItem  ::=
    "#boxExtract" "(" Bytes "," Bytes "," Int "," Int ")"
  rule <k> box_extract => #boxExtract(NAME, {boxAcct(NAME)}:>Bytes, OFFSET, LENGTH) ... </k>
       <stack> LENGTH:Int : OFFSET:Int : NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 3 </stacksize>
    requires isBytes(boxAcct(NAME))
  rule <k> #boxExtract(NAME, ADDR, OFFSET, LENGTH) => .K ... </k>
       <stack> XS => substrBytes(BYTES, OFFSET, OFFSET +Int LENGTH) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES </boxData>
         </box>
         ...
       </account>
    requires (LENGTH +Int OFFSET) <Int lengthBytes(BYTES)
  rule <k> #boxExtract(NAME, ADDR, OFFSET, LENGTH) => #panic(BOX_OUT_OF_BOUNDS) ... </k>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES </boxData>
         </box>
         ...
       </account>
    requires (LENGTH +Int OFFSET) >=Int lengthBytes(BYTES)
  rule <k> #boxExtract(NAME, ADDR, _, _) => #panic(BOX_NOT_FOUND) ... </k>
       <account>
         <address> ADDR </address>
         <boxes>
           BOXES
         </boxes>
         ...
       </account>
    requires notBool(NAME in_boxes(<boxes> BOXES </boxes>))
  rule <k> box_extract => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> _:Int : _:Int : NAME:Bytes : _ </stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_extract => #panic(ILL_TYPED_STACK) ... </k>
       <stack> LENGTH : OFFSET : NAME : _ </stack>
    requires isBytes(LENGTH) orBool isBytes(OFFSET) orBool isInt(NAME)
  rule <k> box_extract => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 3
  syntax KItem  ::=
    "#boxGet" "(" Bytes "," Bytes ")"
  rule <k> box_get => #boxGet(NAME, {boxAcct(NAME)}:>Bytes) ... </k>
       <stack> NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires isBytes(boxAcct(NAME))
  rule <k> #boxGet(NAME, ADDR) => .K ... </k>
       <stack> XS => 1 : BYTES : XS </stack>
       <stacksize> S => S +Int 2 </stacksize>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES </boxData>
         </box>
         ...
       </account>
    requires lengthBytes(BYTES) <Int MAX_BYTEARRAY_LEN
  rule <k> #boxGet(NAME, ADDR) => .K ... </k>
       <stack> XS => 0 : .Bytes : XS </stack>
       <stacksize> S => S +Int 2 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           BOXES
         </boxes>
         ...
       </account>
    requires notBool(NAME in_boxes(<boxes> BOXES </boxes>))
  rule <k> #boxGet(NAME, ADDR) => #panic(BYTES_OVERFLOW) ... </k>
       <account>
         <address> ADDR </address>
         <box>
           <boxName> NAME </boxName>
           <boxData> BYTES </boxData>
         </box>
         ...
       </account>
    requires lengthBytes(BYTES) >=Int MAX_BYTEARRAY_LEN
  rule <k> box_get => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> NAME:Bytes : _ </stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_get => #panic(ILL_TYPED_STACK) ... </k>
       <stack> NAME : _ </stack>
    requires isInt(NAME)
  rule <k> box_get => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 1
  syntax KItem  ::=
    "#boxLen" "(" Bytes "," Bytes ")"
  rule <k> box_len => #boxLen(NAME, {boxAcct(NAME)}:>Bytes) ... </k>
       <stack> NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires isBytes(boxAcct(NAME))
  rule <k> #boxLen(NAME, ADDR) => .K ... </k>
       <stack> XS => 1 : lengthBytes(BYTES) : XS </stack>
       <stacksize> S => S +Int 2 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           <box>
             <boxName> NAME </boxName>
             <boxData> BYTES </boxData>
           </box>
           ...
         </boxes>
         ...
       </account>
  rule <k> #boxLen(NAME, ADDR) => .K ... </k>
       <stack> XS => 0 : 0 : XS </stack>
       <stacksize> S => S +Int 2 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           BOXES
         </boxes>
         ...
       </account>
    requires notBool(NAME in_boxes(<boxes> BOXES </boxes>))
  rule <k> box_len => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> NAME:Bytes : _ </stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_len => #panic(ILL_TYPED_STACK) ... </k>
       <stack> NAME : _ </stack>
    requires isInt(NAME)
  rule <k> box_len => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 1
  syntax KItem  ::=
    "#boxDel" "(" Bytes "," Bytes ")"
  rule <k> box_del => #boxDel(NAME, {boxAcct(NAME)}:>Bytes) ... </k>
       <stack> NAME:Bytes : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
    requires isBytes(boxAcct(NAME))
  rule <k> #boxDel(NAME, ADDR) => .K ... </k>
       <stack> XS => 1 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           ((<box>
             <boxName> NAME </boxName>
             <boxData> BYTES </boxData>
           </box>) => .Bag)
           ...
         </boxes>
         <minBalance> MIN_BALANCE => MIN_BALANCE -Int (2500 +Int (400 *Int (lengthBytes(NAME) +Int
         lengthBytes(BYTES)))) </minBalance>
         ...
       </account>
  rule <k> #boxDel(NAME, ADDR) => .K ... </k>
       <stack> XS => 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <account>
         <address> ADDR </address>
         <boxes>
           BOXES
         </boxes>
         ...
       </account>
    requires notBool(NAME in_boxes(<boxes> BOXES </boxes>))
  rule <k> box_del => #panic(BOX_UNAVAILABLE) ... </k>
       <stack> NAME:Bytes : _ </stack>
    requires boxAcct(NAME) ==K NoTValue
  rule <k> box_del => #panic(ILL_TYPED_STACK) ... </k>
       <stack> NAME : _ </stack>
    requires isInt(NAME)
  rule <k> box_del => #panic(STACK_UNDERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S <Int 1
  rule <k> gaid T:Int => .K ... </k>
       <stack> XS => {getGroupFieldByIdx( getTxnGroupID(getCurrentTxn()), T, ApplicationID)}:>TValue : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
    requires S <Int MAX_STACK_DEPTH
     andBool T <Int {getTxnField(getCurrentTxn(), GroupIndex)}:>Int
     andBool ({getGroupFieldByIdx(getTxnGroupID(getCurrentTxn()), T, TypeEnum)}:>Int) ==Int (@ appl)
  rule <k> gaid T => #panic(FUTURE_TXN) ... </k>
     requires T >=Int {getTxnField(getCurrentTxn(), GroupIndex)}:>Int
     orBool ({getGroupFieldByIdx(getTxnGroupID(getCurrentTxn()), T, TypeEnum)}:>Int) =/=Int (@ appl)
  rule <k> gaids => .K ... </k>
       <stack> T:Int : XS => {getGroupFieldByIdx( getTxnGroupID(getCurrentTxn()), T, ApplicationID)}:>TValue : XS </stack>
    requires T <Int {getTxnField(getCurrentTxn(), GroupIndex)}:>Int
     andBool ({getGroupFieldByIdx(getTxnGroupID(getCurrentTxn()), T, TypeEnum)}:>Int) ==Int (@ appl)
  rule <k> gaids => #panic(FUTURE_TXN) ... </k>
       <stack> T:Int : _ </stack>
     requires T >=Int {getTxnField(getCurrentTxn(), GroupIndex)}:>Int
     orBool ({getGroupFieldByIdx(getTxnGroupID(getCurrentTxn()), T, TypeEnum)}:>Int) =/=Int (@ appl)
  rule <k> gload TXN_IDX I => loadGroupScratch(TXN_IDX, I) ...</k>
  rule <k> gloads I => loadGroupScratch(TXN_IDX, I) ... </k>
       <stack> (TXN_IDX:Int : XS) => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> gloadss => loadGroupScratch(TXN_IDX, I) ... </k>
       <stack> (I:Int : TXN_IDX:Int : XS) => XS </stack>
       <stacksize> S => S -Int 2 </stacksize>
  syntax KItem  ::=
    "loadGroupScratch" "(" Int "," Int ")" [klabel(loadGroupScratch)]
  rule <k> loadGroupScratch(GROUP_IDX, I) => .K ...</k>
       <stack> XS => ({M[I]}:>TValue) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <groupID> GROUP_ID </groupID>
         ...
       </transaction>
       <transaction>
         <groupID> GROUP_ID </groupID>
         <groupIdx> GROUP_IDX </groupIdx>
         <txScratch> M </txScratch>
         ...
       </transaction>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool I in_keys(M)
     andBool S <Int MAX_STACK_DEPTH
     andBool GROUP_IDX <Int ({getTxnField(getCurrentTxn(), GroupIndex)}:>Int)
  rule <k> loadGroupScratch(GROUP_IDX, I) => .K ...</k>
       <stack> XS => ({M[I]}:>TValue) : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <groupIdx> GROUP_IDX </groupIdx>
         <txScratch> M </txScratch>
         ...
       </transaction>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool I in_keys(M)
     andBool S <Int MAX_STACK_DEPTH
     andBool GROUP_IDX <Int ({getTxnField(getCurrentTxn(), GroupIndex)}:>Int)
  rule <k> loadGroupScratch(GROUP_IDX, I) => .K ...</k>
       <stack> XS => 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <groupID> GROUP_ID </groupID>
         ...
       </transaction>
       <transaction>
         <groupID> GROUP_ID </groupID>
         <groupIdx> GROUP_IDX </groupIdx>
         <txScratch> M </txScratch>
         ...
       </transaction>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool notBool (I in_keys(M))
     andBool S <Int MAX_STACK_DEPTH
     andBool GROUP_IDX <Int ({getTxnField(getCurrentTxn(), GroupIndex)}:>Int)
  rule <k> loadGroupScratch(GROUP_IDX, I) => .K ...</k>
       <stack> XS => 0 : XS </stack>
       <stacksize> S => S +Int 1 </stacksize>
       <currentTx> TX_ID </currentTx>
       <transaction>
         <txID> TX_ID </txID>
         <groupIdx> GROUP_IDX </groupIdx>
         <txScratch> M </txScratch>
         ...
       </transaction>
    requires 0 <=Int I andBool I <Int MAX_SCRATCH_SIZE
     andBool notBool (I in_keys(M))
     andBool S <Int MAX_STACK_DEPTH
     andBool GROUP_IDX <Int ({getTxnField(getCurrentTxn(), GroupIndex)}:>Int)
  rule <k> loadGroupScratch(_, I) => #panic(INVALID_SCRATCH_LOC) ... </k>
    requires I <Int 0 orBool I >=Int MAX_SCRATCH_SIZE
  rule <k> loadGroupScratch(GROUP_IDX, _) => #panic(TXN_OUT_OF_BOUNDS) ... </k>
    requires GROUP_IDX <Int 0 orBool GROUP_IDX >=Int {getGlobalField(GroupSize)}:>Int
  rule <k> loadGroupScratch(GROUP_IDX, _) => #panic(FUTURE_TXN) ... </k>
    requires GROUP_IDX >=Int {getTxnField(getCurrentTxn(), GroupIndex)}:>Int
     andBool (GROUP_IDX >=Int 0 andBool GROUP_IDX <Int {getGlobalField(GroupSize)}:>Int)
  rule <k> loadGroupScratch(_, _) => #panic(STACK_OVERFLOW) ... </k>
       <stacksize> S </stacksize>
    requires S >=Int MAX_STACK_DEPTH
  rule <k> itxn_begin => .K ...</k>
       <innerTransactions>
         .List =>
         ListItem(<transaction>
           <txID> "" </txID>
           <txHeader>
             // TODO Fee is calculated dynamically
             <fee>         0                                         </fee>
             <sender>      getGlobalField(CurrentApplicationAddress) </sender>
             <firstValid>  getDefaultValue(FirstValid)  </firstValid>
             <lastValid>   getDefaultValue(LastValid)   </lastValid>
//           TODO: insert First/LastValid from parent TXN once we need them
//             <firstValid>  getTxnField(getCurrentTxn(), FirstValid)  </firstValid>
//             <lastValid>   getTxnField(getCurrentTxn(), LastValid)  </lastValid>
             <genesisHash> .Bytes                                    </genesisHash>
             <txType>       "unknown"                                </txType>
             <typeEnum>     0                                        </typeEnum>
             <groupID>      Int2String(GROUP_ID +Int 1)              </groupID>
             <groupIdx>     0                                        </groupIdx>
             <genesisID>    .Bytes                                   </genesisID>
             <lease>        .Bytes                                   </lease>
             <note>         .Bytes                                   </note>
             <rekeyTo>      PARAM_ZERO_ADDR                          </rekeyTo>
           </txHeader>
           <txnTypeSpecificFields>
             .Bag
           </txnTypeSpecificFields>
           ...
         </transaction>)
       </innerTransactions>
       <nextGroupID> GROUP_ID => GROUP_ID +Int 1 </nextGroupID>
  rule <k> (itxn_submit ~> #incrementPC() ~> #fetchOpcode()) => (#incrementPC() ~> #checkItxns(T) ~> #executeItxnGroup()) ...</k>
       <innerTransactions> T </innerTransactions>
       <lastTxnGroupID> _ => Int2String(GROUP_ID) </lastTxnGroupID>
       <nextGroupID> GROUP_ID </nextGroupID>
  rule <k> itxn_field FIELD => #setItxnField(FIELD, VAL) ...</k>
       <stack> VAL : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> itxn_next => .K ...</k>
       <innerTransactions>
         REST:List
         (.List =>
         ListItem(<transaction>
           <txID> "" </txID>
           <txHeader>
             // TODO Fee is calculated dynamically
             <fee>         0                                         </fee>
             <sender>      getGlobalField(CurrentApplicationAddress) </sender>
             <firstValid>  getTxnField(getCurrentTxn(), FirstValid)  </firstValid>
             <lastValid>   getTxnField(getCurrentTxn(), LastValid)   </lastValid>
             <genesisHash> .Bytes                                    </genesisHash>
             <txType>       "unknown"                                </txType>
             <typeEnum>     0                                        </typeEnum>
             <groupID>      Int2String(GROUP_ID)                     </groupID>
             <groupIdx>     size(REST)                               </groupIdx>
             <genesisID>    .Bytes                                   </genesisID>
             <lease>        .Bytes                                   </lease>
             <note>         .Bytes                                   </note>
             <rekeyTo>      PARAM_ZERO_ADDR                          </rekeyTo>
           </txHeader>
           <txnTypeSpecificFields>
             .Bag
           </txnTypeSpecificFields>
           ...
         </transaction>))
       </innerTransactions>
       <nextGroupID> GROUP_ID </nextGroupID>
    requires size(REST) >=Int 1
  rule <k> itxn FIELD => gitxn getLastItxnGroupIdx() FIELD ...</k>
  rule <k> itxna FIELD IDX => gitxna getLastItxnGroupIdx() FIELD IDX ...</k>
  rule <k> gitxn GROUP_IDX FIELD => #loadFromGroupInner(GROUP_IDX, FIELD) ...</k>
  rule <k> gitxna GROUP_IDX FIELD IDX => #loadFromGroupInner(GROUP_IDX, FIELD, IDX) ...</k>
  rule <k> itxnas FIELD => gitxna getLastItxnGroupIdx() FIELD IDX ...</k>
       <stack> IDX : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> gitxnas GROUP_IDX FIELD => gitxna GROUP_IDX FIELD IDX ...</k>
       <stack> IDX : XS => XS </stack>
       <stacksize> S => S -Int 1 </stacksize>
  rule <k> Op:OpCode => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (V2:TValue) : (V1:TValue) : _ </stack>
    requires (isBinaryArithOpCode(Op)         orBool
              isInequalityOpCode(Op)    orBool
              isBinaryLogicalOpCode(Op) orBool
              isBinaryBitOpCode(Op))
     andBool (isBytes(V2) orBool isBytes(V1))
  rule <k> Op:OpCode => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Bytes) : _ </stack>
    requires isUnaryLogicalOpCode(Op)
  rule <k> _:EqualityOpCode => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (V2:TValue) : (V1:TValue) : _ </stack>
    requires (isBytes(V1) andBool isInt(V2))
      orBool (isBytes(V2) andBool isInt(V1))
  rule <k> OP:OpCode => #panic(ILL_TYPED_STACK) ... </k>
       <stack> A : B : _ </stack>
    requires (isInt(A) orBool isInt(B))
     andBool (isArithmMathByteOpCode(OP)
     orBool   isRelationalMathByteOpCode(OP)
     orBool   isBinaryLogicalMathByteOpCode(OP))
  rule <k> OP:OpCode => #panic(ILL_TYPED_STACK) ... </k>
       <stack> _:Int : _ </stack>
    requires isUnaryLogicalMathByteOpCode(OP)
  rule <k> len => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Int) : _ </stack>
  rule <k> itob => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Bytes) : _ </stack>
  rule <k> btoi => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Int) : _ </stack>
  rule <k> concat => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (V2:TValue) : (V1:TValue) : _ </stack>
    requires isInt(V2) orBool isInt(V1)
  rule <k> substring _ _ => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Int) : _ </stack>
  rule <k> substring3 => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (V:TValue) : (START:TValue) : (END:TValue) : _ </stack>
    requires isInt(V) orBool isBytes(START) orBool isBytes(END)
  rule <k> Op:OpCode => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Bytes) : _ </stack>
    requires isCondBranchOpCode(Op) orBool isReturnOpCode(Op)
  rule <k> app_global_get => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Int) : _ </stack>
  rule <k> app_global_put => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:TValue) : (_:Int):_ </stack>
  rule <k> app_global_del => #panic(ILL_TYPED_STACK) ... </k>
       <stack> (_:Int) : _ </stack>
  rule <k> Op:OpCode => #panic(STACK_UNDERFLOW) ... </k>
       <stack> (_:TValue) : (_:TValue) : .TStack </stack>
       <stacksize> 2 </stacksize>
    requires isTernaryStateOpCode(Op)
      orBool isTernaryByteOpCode(Op)
      orBool isSigVerOpCode(Op)
      orBool isTernaryStackOpCode(Op)
  rule <k> Op:OpCode => #panic(STACK_UNDERFLOW) ... </k>
       <stack> (_:TValue) : .TStack </stack>
       <stacksize> 1 </stacksize>
    requires isBinaryArithOpCode(Op)
      orBool isBinaryBitOpCode(Op)
      orBool isRelationalOpCode(Op)
      orBool isBinaryLogicalOpCode(Op)
      orBool isBinaryByteOpCode(Op)
      orBool isTernaryByteOpCode(Op)
      orBool isBinaryStackOpCode(Op)
      orBool isSigVerOpCode(Op)
      orBool isBinaryStateOpCode(Op)
      orBool isTernaryStateOpCode(Op)
  rule <k> Op:OpCode => #panic(STACK_UNDERFLOW) ... </k>
       <stack> .TStack </stack>
       <stacksize> 0 </stacksize>
    requires isCryptoOpCode(Op)
      orBool isArithOpCode(Op)
      orBool isBitOpCode(Op)
      orBool isRelationalOpCode(Op)
      orBool isLogicalOpCode(Op)
      orBool isByteOpCode(Op)
      orBool isStoreOpCode(Op)
      orBool isCondBranchOpCode(Op)
      orBool isReturnOpCode(Op)
      orBool (isStackOpCode(Op) andBool notBool (isNullaryStackOpCode(Op)))
      orBool isStateOpCode(Op)
      orBool isSigVerOpCode(Op)
endmodule

module ALGOD-MODELS
  imports public JSON
  imports public ALGO-BLOCKCHAIN
  imports public AVM-CONFIGURATION
  imports public AVM-TXN-DEQUE
  imports public AVM-PANIC
  syntax KItem  ::=
    "#setupAccounts" "(" JSON ")" [klabel(#setupAccounts)]
  rule <k> #setupAccounts([ACCT_JSON, REST]) => #addAccountJSON(ACCT_JSON) ~> #setupAccounts([REST]) ... </k>
  rule <k> #setupAccounts([.JSONs]) => .K ... </k>
  syntax KItem  ::=
    "#setupOptInAssets" "(" Bytes "," JSONs ")" [klabel(#setupOptInAssets)]
  rule <k> #setupOptInAssets(ADDR:Bytes, (
                          {
                            "amount": AMOUNT:Int,
                            "asset-id": ASSET_ID:Int,
                            "is-frozen": FROZEN:Bool
                          }, REST:JSONs):JSONs)
            => #setupOptInAssets(ADDR, REST)
            ...
          </k>
          <account>
            <address> ADDR </address>
            <assetsOptedIn>
              (.Bag =>
              <optInAsset>
                <optInAssetID> ASSET_ID </optInAssetID>
                <optInAssetBalance> AMOUNT </optInAssetBalance>
                <optInAssetFrozen> bool2Int(FROZEN) </optInAssetFrozen>
              </optInAsset>)
              ...
            </assetsOptedIn>
            ...
          </account>
  rule <k> #setupOptInAssets(_:Bytes, .JSONs) => .K ... </k>
  syntax KItem  ::=
    "#addAccountJSON" "(" JSON ")" [klabel(#addAccountJSON)]
  rule <k> #addAccountJSON({"address": ADDR:String,
                              "amount": BALANCE:Int,
                              "amount-without-pending-rewards": _AMOUNT_WITHOUT_PENDING_REWARDS,
                              "apps-local-state": [LOCAL_STATE:JSONs],
                              "apps-total-schema": _APPS_TOTAL_SCHEMA,
                              "assets": [OPTIN_ASSETS:JSONs],
                              "auth-addr": AUTH_ADDR:String,
                              "created-apps": [APPS:JSONs],
                              "created-assets": [ASSETS:JSONs],
                              "participation": _PARTICIPATION,
                              "pending-rewards": _PENDING_REWARDS,
                              "reward-base": _REWARDS_BASE,
                              "rewards": _REWARDS,
                              "round": _ROUND,
                              "sig-type": _SIG_TYPE,
                              "status": _STATUS
                             })
            => #setupApplications([APPS])
            ~> #loadLocalState(DecodeAddressString(ADDR), [LOCAL_STATE])
            ~> #setupAssets([ASSETS])
            ~> #setupOptInAssets(DecodeAddressString(ADDR), OPTIN_ASSETS)
            ...
         </k>
         <accountsMap>
           (.Bag =>
           <account>
             <address> DecodeAddressString(ADDR) </address>
             <balance> BALANCE    </balance>
             <key> DecodeAddressString(AUTH_ADDR) </key>
             <appsCreated> .Bag </appsCreated>
             <appsOptedIn> .Bag </appsOptedIn>
             <assetsCreated> .Bag </assetsCreated>
             <assetsOptedIn> .Bag </assetsOptedIn>
             ...
           </account>)
           ...
         </accountsMap>
  rule <k> #addAccountJSON(_INPUT:JSON) => #panic(INVALID_JSON) ... </k>  [owise]
  syntax JSONs  ::=
    "#dumpAccounts" "(" AccountsMapCell ")" [function, klabel(#dumpAccounts)]
  | "#dumpAccountsImpl" "(" JSONs "," AccountsMapCell ")" [function, klabel(#dumpAccountsImpl)]
  rule #dumpAccounts(<accountsMap> ACCTS </accountsMap>)
      => #dumpAccountsImpl((.JSONs), <accountsMap> ACCTS </accountsMap>)
  rule #dumpAccountsImpl(
         (SERIALIZED:JSONs),
         <accountsMap>
           <account> ACCT </account>
           REST
         </accountsMap>)
      => #dumpAccountsImpl((#dumpAccountJSON(<account> ACCT </account>) , SERIALIZED) , <accountsMap> REST </accountsMap>)
  rule #dumpAccountsImpl(
         (SERIALIZED:JSONs),
         <accountsMap>
           .Bag
         </accountsMap>)
      => SERIALIZED
  syntax JSON  ::=
    "#dumpAccountJSON" "(" AccountCell ")" [function, klabel(#dumpAccountJSON)]
  rule #dumpAccountJSON(
             <account>
               <address> ADDR:Bytes </address>
               <balance> BALANCE:Int </balance>
               <appsCreated> APPS </appsCreated>
               <assetsCreated> ASSETS </assetsCreated>
               <assetsOptedIn> OPT_IN_ASSETS </assetsOptedIn>
               ...
             </account>)
          => {"address": EncodeAddressBytes(ADDR),
              "amount": BALANCE,
              "amount-without-pending-rewards": null,
              "apps-local-state": null,
              "apps-total-schema": null,
              "assets": [#dumpAssetsOptedIn(<assetsOptedIn> OPT_IN_ASSETS </assetsOptedIn>)],
              "created-apps": [#dumpApps(EncodeAddressBytes(ADDR),<appsCreated> APPS </appsCreated>)],
              "created-assets": [#dumpAssets(EncodeAddressBytes(ADDR),<assetsCreated> ASSETS </assetsCreated>)],
              "participation": null,
              "pending-rewards": null,
              "reward-base": null,
              "rewards": null,
              "round": null,
              "status": null,
              "sig-type": null,
              "auth-addr": null
             }
  syntax KItem  ::=
    "#setupAssets" "(" JSON ")" [klabel(#setupAssets)]
  rule <k> #setupAssets([ASSET_JSON, REST]) => #addAssetJSON(ASSET_JSON) ~> #setupAssets([REST]) ... </k>
  rule <k> #setupAssets([.JSONs]) => .K ... </k>
  syntax KItem  ::=
    "#addAssetJSON" "(" JSON ")" [klabel(#addAssetJSON)]
  rule <k> #addAssetJSON({
                             "index": INDEX:Int,
                             "params": {
                               "clawback": CLAWBACK_ADDR:String,
                               "creator": CREATOR_ADDR_STR:String,
                               "decimals": DECIMALS:Int,
                               "default-frozen": DEFAULT_FROZEN:Bool,
                               "freeze": FREEZE_ADDR:String,
                               "manager": MANAGER_ADDR:String,
                               "metadata-hash": METADATA_HASH:String,
                               "name": ASSET_NAME:String,
                               "reserve": RESERVE_ADDR:String,
                               "total": TOTAL:Int,
                               "unit-name": UNIT_NAME:String,
                               "url": URL:String
                             }
                           }) => .K ... </k>
         <account>
           <address> CREATOR_ADDR </address>
           <assetsCreated>
             .Bag =>
             <asset>
               <assetID> INDEX </assetID>
               <assetName> String2Bytes(ASSET_NAME) </assetName>
               <assetUnitName> String2Bytes(UNIT_NAME) </assetUnitName>
               <assetTotal> TOTAL </assetTotal>
               <assetDecimals> DECIMALS </assetDecimals>
               <assetDefaultFrozen> bool2Int(DEFAULT_FROZEN) </assetDefaultFrozen>
               <assetURL> String2Bytes(URL) </assetURL>
               <assetMetaDataHash> String2Bytes(METADATA_HASH) </assetMetaDataHash>
               <assetManagerAddr> DecodeAddressString(MANAGER_ADDR) </assetManagerAddr>
               <assetReserveAddr> DecodeAddressString(RESERVE_ADDR) </assetReserveAddr>
               <assetFreezeAddr> DecodeAddressString(FREEZE_ADDR) </assetFreezeAddr>
               <assetClawbackAddr> DecodeAddressString(CLAWBACK_ADDR) </assetClawbackAddr>
             </asset>
             ...
           </assetsCreated>
           ...
         </account>
         <assetCreator> (.Map => (INDEX |-> CREATOR_ADDR)) ... </assetCreator>
       requires DecodeAddressString(CREATOR_ADDR_STR) ==K CREATOR_ADDR
  syntax JSONs  ::=
    "#dumpAssets" "(" String "," AssetsCreatedCell ")" [function, klabel(#dumpAssets)]
  | "#dumpAssetsImpl" "(" String "," JSONs "," AssetsCreatedCell ")" [function, klabel(#dumpAssetsImpl)]
  rule #dumpAssets((CREATOR:String), <assetsCreated> ASSETS </assetsCreated>)
      => #dumpAssetsImpl((CREATOR:String), (.JSONs), <assetsCreated> ASSETS </assetsCreated>)
  rule #dumpAssetsImpl(
         (CREATOR:String),
         (SERIALIZED:JSONs),
         <assetsCreated>
           <asset> ASSET </asset>
           REST
         </assetsCreated>)
      => #dumpAssetsImpl((CREATOR:String), (#dumpAssetJSON((CREATOR:String), <asset> ASSET </asset>) , SERIALIZED) , <assetsCreated> REST </assetsCreated>)
  rule #dumpAssetsImpl(
         (_CREATOR:String),
         (SERIALIZED:JSONs),
         <assetsCreated>
           .Bag
         </assetsCreated>)
      => SERIALIZED
  syntax JSON  ::=
    "#dumpAssetJSON" "(" String "," AssetCell ")" [function, klabel(#dumpAssetJSON)]
  rule #dumpAssetJSON(
             (CREATOR:String),
             <asset>
               <assetID>            ASSET_ID:Int        </assetID>
               <assetName>          ASSET_NAME:Bytes    </assetName>
               <assetUnitName>      UNIT_NAME:Bytes     </assetUnitName>
               <assetTotal>         TOTAL:Int           </assetTotal>
               <assetDecimals>      DECIMALS:Int        </assetDecimals>
               <assetDefaultFrozen> DEFAULT_FROZEN:Int  </assetDefaultFrozen>
               <assetURL>           URL:Bytes           </assetURL>
               <assetMetaDataHash>  METADATA_HASH:Bytes </assetMetaDataHash>
               <assetManagerAddr>   MANAGER_ADDR:Bytes  </assetManagerAddr>
               <assetReserveAddr>   RESERVE_ADDR:Bytes  </assetReserveAddr>
               <assetFreezeAddr>    FREEZE_ADDR:Bytes   </assetFreezeAddr>
               <assetClawbackAddr>  CLAWBACK_ADDR:Bytes </assetClawbackAddr>
             </asset>)
          => { "index": ASSET_ID
             , "params": { "clawback"      : EncodeAddressBytes(CLAWBACK_ADDR)
                         , "creator"       : CREATOR
                         , "decimals"      : DECIMALS
                         , "default-frozen": int2Bool(DEFAULT_FROZEN)
                         , "freeze"        : EncodeAddressBytes(FREEZE_ADDR)
                         , "manager"       : EncodeAddressBytes(MANAGER_ADDR)
                         , "metadata-hash" : Bytes2String(METADATA_HASH)
                         , "name"          : Bytes2String(ASSET_NAME)
                         , "reserve"       : EncodeAddressBytes(RESERVE_ADDR)
                         , "total"         : TOTAL
                         , "unit-name"     : Bytes2String(UNIT_NAME)
                         , "url"           : Bytes2String(URL)
                         }
             }
  syntax JSONs  ::=
    "#dumpAssetsOptedIn" "(" AssetsOptedInCell ")" [function, klabel(#dumpAssetsOptedIn)]
  | "#dumpAssetsOptedInImpl" "(" JSONs "," AssetsOptedInCell ")" [function, klabel(#dumpAssetsOptedInImpl)]
  rule #dumpAssetsOptedIn(<assetsOptedIn> ASSETS </assetsOptedIn>)
      => #dumpAssetsOptedInImpl((.JSONs), <assetsOptedIn> ASSETS </assetsOptedIn>)
  rule #dumpAssetsOptedInImpl(
         (SERIALIZED:JSONs),
         <assetsOptedIn>
           <optInAsset>
             <optInAssetID>      ASSET_ID:Int      </optInAssetID>
             <optInAssetBalance> ASSET_BALANCE:Int </optInAssetBalance>
             <optInAssetFrozen>  FROZEN:Int        </optInAssetFrozen>
           </optInAsset>
           REST
         </assetsOptedIn>)
      => #dumpAssetsOptedInImpl( ({"amount": ASSET_BALANCE, "asset-id": ASSET_ID, "is-frozen": int2Bool(FROZEN)} , SERIALIZED)
                               , <assetsOptedIn> REST </assetsOptedIn>)
  rule #dumpAssetsOptedInImpl(
         (SERIALIZED:JSONs),
         <assetsOptedIn>
           .Bag
         </assetsOptedIn>)
      => SERIALIZED
  syntax KItem  ::=
    "#loadLocalState" "(" Bytes "," JSONs ")" [klabel(#loadLocalState)]
  | "#loadLocalState" "(" Int "," Bytes "," JSONs ")" [klabel(#loadLocalState)]
  rule <k> #loadLocalState(ADDR:Bytes,
                  [{
                     "id": APP_ID:Int,
                     "key-value": [LOCAL_STATE],
                     "schema": _:JSON
                   }, REST:JSONs] )
          => #loadLocalState(APP_ID, ADDR, [LOCAL_STATE]) ~> #loadLocalState(ADDR, [REST]) ... </k>
         <account>
           <address> ADDR </address>
           <appsOptedIn>
             (.Bag =>
             <optInApp>
               <optInAppID> APP_ID </optInAppID>
               <localInts> .Map </localInts>
               <localBytes> .Map </localBytes>
             </optInApp>)
             ...
           </appsOptedIn>
           ...
         </account>
  rule <k> #loadLocalState(_:Bytes, [ .JSONs ]) => .K ... </k>
  rule <k> #loadLocalState(APP_ID:Int, ADDR:Bytes,
                             [{"key": K:String, "value": {"bytes": V:String, "type": 1, "uint": _} }, REST:JSONs])
          => #loadLocalState(APP_ID, ADDR, [REST]) ... </k>
         <account>
           <address> ADDR </address>
           <appsOptedIn>
             <optInApp>
               <optInAppID> APP_ID </optInAppID>
               <localInts> _ </localInts>
               <localBytes> .Map => (Base64Decode(K) |-> Base64Decode(V)) ... </localBytes>
             </optInApp>
             ...
           </appsOptedIn>
           ...
         </account>
  rule <k> #loadLocalState(APP_ID:Int, ADDR:Bytes,
                             [{"key": K:String, "value": {"bytes": _, "type": 2, "uint": V:Int} }, REST:JSONs])
          => #loadLocalState(APP_ID, ADDR, [REST]) ... </k>
         <account>
           <address> ADDR </address>
           <appsOptedIn>
             <optInApp>
               <optInAppID> APP_ID </optInAppID>
               <localInts> .Map => (Base64Decode(K) |-> V) ... </localInts>
               <localBytes> _ </localBytes>
             </optInApp>
             ...
           </appsOptedIn>
           ...
         </account>
  rule <k> #loadLocalState(_:Int, _:Bytes, [.JSONs]) => .K ... </k>
  syntax KItem  ::=
    "#loadGlobalState" "(" Int "," JSONs ")" [klabel(#loadGlobalState)]
  rule <k> #loadGlobalState(APP_ID, [{"key": K:String, "value": {"bytes": V:String, "type": 1, "uint": _} }, REST:JSONs] )
          => #loadGlobalState(APP_ID, [REST]) ... </k>
         <app>
           <appID> APP_ID </appID>
           <globalState>
             <globalBytes> .Map => (Base64Decode(K) |-> Base64Decode(V)) ... </globalBytes>
             ...
           </globalState>
           ...
         </app>
  rule <k> #loadGlobalState(APP_ID, [{"key": K:String, "value": {"bytes": _, "type": 2, "uint": V:Int} }, REST:JSONs] )
          => #loadGlobalState(APP_ID, [REST]) ... </k>
         <app>
           <appID> APP_ID </appID>
           <globalState>
             <globalInts> .Map => (Base64Decode(K) |-> V) ... </globalInts>
             ...
           </globalState>
           ...
         </app>
  rule <k> #loadGlobalState(_, [.JSONs]) => .K ... </k>
  syntax KItem  ::=
    "#setupApplications" "(" JSON ")" [klabel(#setupApplications)]
  rule <k> #setupApplications([APP_JSON, REST]) => #addApplicationJSON(APP_JSON) ~> #setupApplications([REST]) ... </k>
  rule <k> #setupApplications([.JSONs])         => .K ... </k>
  rule <k> #setupApplications(null)             => .K ... </k>
  syntax KItem  ::=
    "#addApplicationJSON" "(" JSON ")" [klabel(#addApplicationJSON)]
  rule <k> #addApplicationJSON({ "id": APP_ID:Int
                                 , "params": { "approval-program"   : APPROVAL_NAME:String
                                             , "clear-state-program": CLEAR_STATE_NAME:String
                                             , "creator"            : CREATOR_ADDR_STR:String
                                             , "global-state"       : [GLOBAL_STATE:JSONs]
                                             , "global-state-schema": { "nbs": GLOBAL_NUM_BYTES:Int, "nui": GLOBAL_NUM_UINTS:Int }
                                             , "local-state-schema" : { "nbs": LOCAL_NUM_BYTES:Int, "nui": LOCAL_NUM_UINTS:Int }
                                             }
                                 }
             ) => #loadGlobalState(APP_ID, [GLOBAL_STATE]) ... </k>
           <account>
             <address> CREATOR_ADDR </address>
             <appsCreated>
             (.Bag => <app>
                        <appID>            APP_ID                                            </appID>
                        <approvalPgm>  APPROVAL_NAME                                     </approvalPgm>
                        <approvalPgmSrc>   {TEAL_PROGRAMS[ APPROVAL_NAME ]}:>TealInputPgm    </approvalPgmSrc>
                        <clearStatePgm> CLEAR_STATE_NAME                                 </clearStatePgm>
                        <clearStatePgmSrc> {TEAL_PROGRAMS[ CLEAR_STATE_NAME ]}:>TealInputPgm </clearStatePgmSrc>
                        <globalState>
                          <globalNumInts>   GLOBAL_NUM_UINTS      </globalNumInts>
                          <globalNumBytes>  GLOBAL_NUM_BYTES      </globalNumBytes>
                          ...
                        </globalState>
                        <localState>
                          <localNumInts>    LOCAL_NUM_UINTS       </localNumInts>
                          <localNumBytes>   LOCAL_NUM_BYTES       </localNumBytes>
                        </localState>
                          ...
                       </app>)
             ...
             </appsCreated>
             ...
           </account>
           <tealPrograms> TEAL_PROGRAMS </tealPrograms>
           <appCreator> (.Map => (APP_ID |-> DecodeAddressString(CREATOR_ADDR_STR))) ... </appCreator>
       requires DecodeAddressString(CREATOR_ADDR_STR) ==K CREATOR_ADDR
  rule <k> #addApplicationJSON(_INPUT:JSON) => #panic(INVALID_JSON) ... </k>  [owise]
  syntax JSONs  ::=
    "#dumpApps" "(" String "," AppsCreatedCell ")" [function, klabel(#dumpApps)]
  | "#dumpAppsImpl" "(" String "," JSONs "," AppsCreatedCell ")" [function, klabel(#dumpAppsImpl)]
  rule #dumpApps((CREATOR:String), <appsCreated> APPS </appsCreated>)
      => #dumpAppsImpl((CREATOR:String), (.JSONs), <appsCreated> APPS </appsCreated>)
  rule #dumpAppsImpl(
         (CREATOR:String),
         (SERIALIZED:JSONs),
         <appsCreated>
           <app> APP </app>
           REST
         </appsCreated>)
      => #dumpAppsImpl((CREATOR:String), (#dumpAppJSON((CREATOR:String), <app> APP </app>) , SERIALIZED) , <appsCreated> REST </appsCreated>)
  rule #dumpAppsImpl(
         (_CREATOR:String),
         (SERIALIZED:JSONs),
         <appsCreated>
           .Bag
         </appsCreated>)
      => SERIALIZED
  syntax JSON  ::=
    "#dumpAppJSON" "(" String "," AppCell ")" [function, klabel(#dumpAppJSON)]
  rule #dumpAppJSON(
             (CREATOR:String),
             <app>
               <appID>             APP_ID:Int              </appID>
               <approvalPgm>   APPROVAL_NAME:String           </approvalPgm>
               <clearStatePgm> CLEAR_STATE_NAME:String        </clearStatePgm>
               <globalState>
                 <globalNumInts>   GLOBAL_NUM_UINTS      </globalNumInts>
                 <globalNumBytes>  GLOBAL_NUM_BYTES      </globalNumBytes>
                 <globalBytes>     GLOBAL_UINTS:Map      </globalBytes>
                 <globalInts>      GLOBAL_BYTES:Map      </globalInts>
               </globalState>
               <localState>
                 <localNumInts>    LOCAL_NUM_UINTS       </localNumInts>
                 <localNumBytes>   LOCAL_NUM_BYTES       </localNumBytes>
               </localState>
               <extraPages>        _EXTRA_PAGES           </extraPages>
               ...
             </app>)
          => { "id": APP_ID
             , "params": { "creator"            : CREATOR
                         , "approval-program"   : APPROVAL_NAME
                         , "clear-state-program": CLEAR_STATE_NAME
                         , "local-state-schema" : { "nbs": maybeTUInt64(LOCAL_NUM_BYTES, 0)
                                                  , "nui": maybeTUInt64(LOCAL_NUM_UINTS, 0) }
                         , "global-state-schema": { "nbs": maybeTUInt64(GLOBAL_NUM_BYTES, 0)
                                                  , "nui": maybeTUInt64(GLOBAL_NUM_UINTS, 0) }
                         , "global-state"       : [ #dumpStateMap(GLOBAL_UINTS GLOBAL_BYTES) ]
                         }
             }
  syntax JSONs  ::=
    "#dumpStateMap" "(" Map ")" [function, klabel(#dumpStateMap)]
  rule #dumpStateMap((KEY:Bytes |-> VALUE:Bytes) REST)
      => {"key": Base64Encode(KEY):String, "value": {"bytes": Base64Encode(VALUE), "type": 1, "uint": 0 } }, #dumpStateMap(REST)
  rule #dumpStateMap((KEY:Bytes |-> VALUE:Int  ) REST)
      => {"key": Base64Encode(KEY):String, "value": {"bytes": "", "type": 2, "uint": VALUE} }, #dumpStateMap(REST)
  rule #dumpStateMap(.Map) => .JSONs
  syntax String  ::=
    "#getTxnJSONType" "(" JSON ")" [function, klabel(#getTxnJSONType)]
  rule #getTxnJSONType({ "type": TYPE:String,  _}) => TYPE
  rule #getTxnJSONType({ KEY: _, REST}) => #getTxnJSONType(REST)
      requires notBool (KEY ==String "type")
  rule #getTxnJSONType({ .JSONs }) => "undef"
  syntax KItem  ::=
    "#setupTransactions" "(" JSON ")" [klabel(#setupTransactions)]
  rule <k> #setupTransactions([TXN_JSON, REST]) => #addTxnJSON(TXN_JSON) ~> #setupTransactions([REST]) ... </k>
  rule <k> #setupTransactions([.JSONs]) => .K ... </k>
  syntax KItem  ::=
    "#addTxnJSON" "(" JSON ")" [klabel(#addTxnJSON)]
  syntax TValueList  ::=
    "JSONList2BytesList" "(" JSON ")" [function, klabel(JSONList2BytesList)]
  rule JSONList2BytesList([.JSONs]) => .TValueList
  rule JSONList2BytesList([ I:Int , REST ]) => prepend(Int2Bytes(I, BE, Unsigned), JSONList2BytesList( [ REST ] ))
  rule JSONList2BytesList([ S:String , REST ]) => prepend(Base64Decode(S), JSONList2BytesList( [ REST ] ))
  syntax TValueList  ::=
    "JSONIntList2TUint64List" "(" JSON ")" [function, klabel(JSONIntList2TUint64List)]
  rule JSONIntList2TUint64List([.JSONs]) => .TValueList
  rule JSONIntList2TUint64List([I:Int, REST]) => prepend(I, JSONIntList2TUint64List([REST]))
  syntax TValueList  ::=
    "JSONAccountsList2BytesList" "(" JSON ")" [function, klabel(JSONAccountsList2BytesList)]
  rule JSONAccountsList2BytesList([.JSONs]) => .TValueList
  rule JSONAccountsList2BytesList([S:String, REST]) => prepend(DecodeAddressString(S), JSONAccountsList2BytesList([REST]))
  syntax TValuePairList  ::=
    "JSONBoxRefsList2PairList" "(" JSONs ")" [function, klabel(JSONBoxRefsList2PairList)]
  rule JSONBoxRefsList2PairList([{ "i": I:Int, "n": NAME:String  }:JSON, REST:JSONs]) =>
    prepend((String2Bytes(NAME), I):TValuePair, JSONBoxRefsList2PairList([REST]))
  rule JSONBoxRefsList2PairList([{ "i": I:Int , "n": NAME:String }]) =>
    (String2Bytes(NAME), I):TValuePair
  rule JSONBoxRefsList2PairList([.JSONs]) => .TValuePairList
  rule <k> #addTxnJSON({ "amt": AMOUNT:Int,
                           "fee": _FEE:Int,
                           "fv": _FIRST_VALID:Int,
                           "gen": _GEN:String,
                           "gh": _,
                           "grp": GROUP_ID:String,
                           "lv": _LAST_VALID:Int,
                           "note": _NOTE:String,
                           "rcv": RECEIVER:String,
                           "rekey": REKEY_TO:String,
                           "snd": SENDER:String,
                           "type": "pay"
                         })
          => #pushTxnBack(<txID> Int2String(ID) </txID>) ...
        </k>
       <transactions>
         TXNS =>
         <transaction>
           <txID> Int2String(ID) </txID>
           <txHeader>
             <sender>      DecodeAddressString(SENDER)   </sender>
             <txType>      "pay"                                                    </txType>
             <typeEnum>    @ pay                                                    </typeEnum>
             <groupID>     GROUP_ID                                                 </groupID>
             <groupIdx>    groupSize(GROUP_ID, <transactions> TXNS </transactions>) </groupIdx>
             <rekeyTo>     DecodeAddressString(REKEY_TO)                            </rekeyTo>
             ...           // other fields will receive default values
           </txHeader>
           <payTxFields>
             <receiver>         DecodeAddressString(RECEIVER) </receiver>
             <amount>           AMOUNT </amount>
             <closeRemainderTo> PARAM_ZERO_ADDR </closeRemainderTo>
           </payTxFields>
           ...
         </transaction>
         TXNS
       </transactions>
       <nextTxnID> ID => ID +Int 1 </nextTxnID>
  rule <k> #addTxnJSON({
                           "aamt": AMOUNT:Int,
                           "aclose": CLOSE_TO:JSON,
                           "arcv": RECEIVER:String,
                           "asnd": _ASSET_ASENDER,
                           "fee": _FEE:Int,
                           "fv": _FIRST_VALID:Int,
                           "gen": _GEN:String,
                           "gh": _,
                           "grp": GROUP_ID:String,
                           "lv": _LAST_VALID:Int,
                           "note": _NOTE:String,
                           "rekey": REKEY_TO:String,
                           "snd": SENDER:String,
                           "type": "axfer",
                           "xaid": ASSET_ID:Int
                         })
          => #pushTxnBack(<txID> Int2String(ID) </txID>) ...
        </k>
       <transactions>
         TXNS =>
         <transaction>
           <txID> Int2String(ID) </txID>
           <txHeader>
             <sender>      DecodeAddressString(SENDER)                              </sender>
             <txType>      "axfer"                                                  </txType>
             <typeEnum>    @ axfer                                                  </typeEnum>
             <groupID>     GROUP_ID                                                 </groupID>
             <groupIdx>    groupSize(GROUP_ID, <transactions> TXNS </transactions>) </groupIdx>
             <rekeyTo>     DecodeAddressString(REKEY_TO)                            </rekeyTo>
             ...           // other fields will receive default values
           </txHeader>
           <assetTransferTxFields>
             <xferAsset> ASSET_ID </xferAsset>
             <assetAmount> AMOUNT </assetAmount>
             <assetReceiver> DecodeAddressString(RECEIVER) </assetReceiver>
             <assetASender> PARAM_ZERO_ADDR </assetASender>
             <assetCloseTo> #if isString(CLOSE_TO) #then DecodeAddressString({CLOSE_TO}:>String) #else PARAM_ZERO_ADDR #fi </assetCloseTo>
           </assetTransferTxFields>
           ...
         </transaction>
         TXNS
       </transactions>
       <nextTxnID> ID => ID +Int 1 </nextTxnID>
  rule <k> #addTxnJSON({
                           "afrz": FROZEN:Bool,
                           "fadd": FREEZE_ADDR:String,
                           "faid": ASSET_ID:Int,
                           "fee": _FEE:Int,
                           "fv": _FIRST_VALID:Int,
                           "gen": _GEN:String,
                           "gh": _,
                           "grp": GROUP_ID:String,
                           "lv": _LAST_VALID:Int,
                           "note": _NOTE:String,
                           "rekey": REKEY_TO:String,
                           "snd": SENDER:String,
                           "type": "afrz"
                         })
          => #pushTxnBack(<txID> Int2String(ID) </txID>) ...
        </k>
       <transactions>
         TXNS =>
         <transaction>
           <txID> Int2String(ID) </txID>
           <txHeader>
             <sender>      DecodeAddressString(SENDER)   </sender>
             <txType>      "afrz"                                                   </txType>
             <typeEnum>    @ afrz                                                   </typeEnum>
             <groupID>     GROUP_ID                                                 </groupID>
             <groupIdx>    groupSize(GROUP_ID, <transactions> TXNS </transactions>) </groupIdx>
             <rekeyTo>     DecodeAddressString(REKEY_TO)                            </rekeyTo>
             ...           // other fields will receive default values
           </txHeader>
           <assetFreezeTxFields>
             <freezeAccount> DecodeAddressString(FREEZE_ADDR) </freezeAccount>
             <freezeAsset> ASSET_ID </freezeAsset>
             <assetFrozen> bool2Int(FROZEN) </assetFrozen>
           </assetFreezeTxFields>
           ...
         </transaction>
         TXNS
       </transactions>
       <nextTxnID> ID => ID +Int 1 </nextTxnID>
  rule <k> #addTxnJSON({
                           "apaa": APPLICATION_ARGS:JSON,
                           "apan": ON_COMPLETION:Int,
                           "apap": APPROVAL_NAME:JSON,
                           "apas": FOREIGN_ASSETS:JSON,
                           "apat": ACCOUNTS:JSON,
                           "apbx": BOX_REFS:JSON,
                           "apep": EXTRA_PAGES:Int,
                           "apfa": FOREIGN_APPS:JSON,
                           "apgs": { "nbs": GLOBAL_NUM_BYTES:Int, "nui": GLOBAL_NUM_UINTS:Int },
                           "apid": APPLICATION_ID:Int,
                           "apls": { "nbs": LOCAL_NUM_BYTES:Int, "nui": LOCAL_NUM_UINTS:Int },
                           "apsu": CLEAR_STATE_NAME:JSON,
                           "fee": _FEE:Int,
                           "fv": _FIRST_VALID:Int,
                           "gen": _GEN:String,
                           "gh": _,
                           "grp": GROUP_ID:String,
                           "lv": _LAST_VALID:Int,
                           "note": _NOTE:String,
                           "rekey": REKEY_TO:String,
                           "snd":  SENDER:String,
                           "type": "appl"
                         })
          => #pushTxnBack(<txID> Int2String(ID) </txID>) ...
        </k>
        <transactions>
         (.Bag =>
         <transaction>
           <txID> Int2String(ID) </txID>
           <txHeader>
             <sender>      DecodeAddressString(SENDER)                              </sender>
             <txType>      "appl"                                                   </txType>
             <typeEnum>    @ appl                                                   </typeEnum>
             <groupID>     GROUP_ID                                                 </groupID>
             <groupIdx>    groupSize(GROUP_ID, <transactions> TXNS </transactions>) </groupIdx>
             <rekeyTo>     DecodeAddressString(REKEY_TO)                            </rekeyTo>
             ...           // other fields will receive default values
           </txHeader>
           <appCallTxFields>
             <applicationID> APPLICATION_ID </applicationID>
             <onCompletion> ON_COMPLETION </onCompletion>
             <approvalProgramSrc>
               #if isString(progamFromJSON(APPROVAL_NAME)) #then {TEAL_PROGRAMS[ APPROVAL_NAME ]}:>TealInputPgm #else err:TealInputPgm #fi
              </approvalProgramSrc>
             <clearStateProgramSrc>
               #if isString(progamFromJSON(CLEAR_STATE_NAME)) #then {TEAL_PROGRAMS[ CLEAR_STATE_NAME ]}:>TealInputPgm #else err:TealInputPgm #fi
             </clearStateProgramSrc>
             <approvalProgram>      progamFromJSON(APPROVAL_NAME)     </approvalProgram>
             <clearStateProgram>    progamFromJSON(CLEAR_STATE_NAME)  </clearStateProgram>
             <accounts> JSONAccountsList2BytesList(ACCOUNTS) </accounts>
             <applicationArgs> JSONList2BytesList(APPLICATION_ARGS) </applicationArgs>
             <foreignApps> JSONIntList2TUint64List(FOREIGN_APPS) </foreignApps>
             <foreignAssets> JSONIntList2TUint64List(FOREIGN_ASSETS) </foreignAssets>
             <boxReferences> JSONBoxRefsList2PairList(BOX_REFS) </boxReferences>
             <globalStateSchema>
               <globalNui> GLOBAL_NUM_UINTS </globalNui>
               <globalNbs> GLOBAL_NUM_BYTES </globalNbs>
             </globalStateSchema>
             <localStateSchema>
               <localNui> LOCAL_NUM_UINTS </localNui>
               <localNbs> LOCAL_NUM_BYTES </localNbs>
             </localStateSchema>
             <extraProgramPages> EXTRA_PAGES </extraProgramPages>
             ...
           </appCallTxFields>
           ...
         </transaction>)
         TXNS
       </transactions>
       <tealPrograms> TEAL_PROGRAMS </tealPrograms>
       <nextTxnID> ID => ID +Int 1 </nextTxnID>
  syntax MaybeTValue  ::=
    "progamFromJSON" "(" JSON ")" [function, klabel(progamFromJSON), total]
  rule progamFromJSON(PGM:String) => PGM
  rule progamFromJSON(_)          => NoTValue  [owise]
  rule <k> #addTxnJSON({
                           "apar": {
                             "am": METADATA_HASH:String,
                             "an": ASSET_NAME:String,
                             "au": URL:String,
                             "c": CLAWBACK_ADDR:String,
                             "dc": DECIMALS:Int,
                             "df": DEFAULT_FROZEN:Bool,
                             "f": FREEZE_ADDR:String,
                             "m": MANAGER_ADDR:String,
                             "r": RESERVE_ADDR:String,
                             "t": TOTAL:Int,
                             "un": UNIT_NAME:String

                           },
                           "caid": ASSET_ID:Int,
                           "fee": _FEE:Int,
                           "fv": _FIRST_VALID:Int,
                           "gen": _GEN:String,
                           "gh": _,
                           "grp": GROUP_ID:String,
                           "lv": _LAST_VALID:Int,
                           "note": _NOTE:String,
                           "rekey": REKEY_TO:String,
                           "snd":  SENDER:String,
                           "type": "acfg"
                         })
          => #pushTxnBack(<txID> Int2String(ID) </txID>) ...
        </k>
        <transactions>
         (.Bag =>
         <transaction>
           <txID> Int2String(ID) </txID>
           <txHeader>
             <sender>      DecodeAddressString(SENDER)                              </sender>
             <txType>      "acfg"                                                   </txType>
             <typeEnum>    @ acfg                                                   </typeEnum>
             <groupID>     GROUP_ID                                                 </groupID>
             <groupIdx>    groupSize(GROUP_ID, <transactions> TXNS </transactions>) </groupIdx>
             <rekeyTo>     DecodeAddressString(REKEY_TO)                            </rekeyTo>
             ...           // other fields will receive default values
           </txHeader>
           <assetConfigTxFields>
             <configAsset> ASSET_ID </configAsset>
             <assetParams>
               <configTotal> TOTAL </configTotal>
               <configDecimals> DECIMALS </configDecimals>
               <configDefaultFrozen> bool2Int(DEFAULT_FROZEN) </configDefaultFrozen>
               <configUnitName> String2Bytes(UNIT_NAME) </configUnitName>
               <configAssetName> String2Bytes(ASSET_NAME) </configAssetName>
               <configAssetURL> String2Bytes(URL) </configAssetURL>
               <configMetaDataHash> String2Bytes(METADATA_HASH) </configMetaDataHash>
               <configManagerAddr> DecodeAddressString(MANAGER_ADDR) </configManagerAddr>
               <configReserveAddr> DecodeAddressString(RESERVE_ADDR) </configReserveAddr>
               <configFreezeAddr> DecodeAddressString(FREEZE_ADDR) </configFreezeAddr>
               <configClawbackAddr> DecodeAddressString(CLAWBACK_ADDR) </configClawbackAddr>
             </assetParams>
           </assetConfigTxFields>
           ...
         </transaction>)
         TXNS
       </transactions>
       <tealPrograms> _TEAL_PROGRAMS </tealPrograms>
       <nextTxnID> ID => ID +Int 1 </nextTxnID>
  syntax JSONs  ::=
    "#dumpConfirmedTransactions" "(" TransactionsCell ")" [function, klabel(#dumpConfirmedTransactions)]
  | "#dumpConfirmedTransactionsImpl" "(" JSONs "," TransactionsCell ")" [function, klabel(#dumpConfirmedTransactionsImpl)]
  rule #dumpConfirmedTransactions(<transactions> TXNS </transactions>)
      => #dumpConfirmedTransactionsImpl((.JSONs), <transactions> TXNS </transactions>)
  rule #dumpConfirmedTransactionsImpl(
         (SERIALIZED:JSONs),
         <transactions>
           <transaction> TXN </transaction>
           REST
         </transactions>)
      => #dumpConfirmedTransactionsImpl((#dumpConfirmedTransactionJSON(<transaction> TXN </transaction>) , SERIALIZED) , <transactions> REST </transactions>)
  rule #dumpConfirmedTransactionsImpl(
         (SERIALIZED:JSONs),
         <transactions>
           .Bag
         </transactions>)
      => SERIALIZED
  syntax JSON  ::=
    "#dumpConfirmedTransactionJSON" "(" TransactionCell ")" [function, klabel(#dumpConfirmedTransactionJSON)]
  rule #dumpConfirmedTransactionJSON(
          <transaction>
            <txID> TX_ID:String </txID>
            <applyData>
              <txConfigAsset>   CREATED_ASSET_ID </txConfigAsset>
              <txApplicationID> CREATED_APP_ID   </txApplicationID>
              <log>
                <logData> LOG_DATA  </logData>
                <logSize> _LOG_SIZE </logSize>
              </log>
              ...
            </applyData>
            ...
          </transaction>)
          =>{ "id"     : TX_ID
            , "params" : { "asset-index": maybeTUInt64(CREATED_ASSET_ID, 0)
                       , "application-index": maybeTUInt64(CREATED_APP_ID, 0)
                       , "close-rewards": null
                       , "closing-amount": null
                       , "asset-closing-amount": null
                       , "confirmed-round": 1
                       , "receiver-rewards": null
                       , "sender-rewards": null
                       , "local-state-delta": null
                       , "global-state-delta": null
                       , "logs": BytesList2JSONList(LOG_DATA)
                       , "inner-txns": null
                       , "txn": null
                       }
            }
  syntax JSON  ::=
    "BytesList2JSONList" "(" TValueList ")" [function, klabel(BytesList2JSONList)]
  rule BytesList2JSONList(.TValueList)  => [.JSONs]
  rule BytesList2JSONList(B:Bytes)      => [Base64Encode(B)]
  rule BytesList2JSONList(B:Bytes REST) => [Base64Encode(B), BytesList2JSONList(REST)]
endmodule

module AVM-EXECUTION-SYNTAX
  imports public INT
  imports public LIST
  imports public BYTES
  imports public AVM-CONSTANTS
  imports public ALGO-BLOCKCHAIN
  imports public ALGO-TXN
  imports public ALGO-ITXN
  imports public TEAL-SYNTAX
  imports public TEAL-DRIVER
  imports public AVM-INITIALIZATION
  syntax AlgorandCommand
endmodule

module AVM-EXECUTION
  imports public AVM-EXECUTION-SYNTAX
  imports public AVM-TXN-DEQUE
  imports public ALGO-TXN
  rule <k> #evalTxGroup() => #initTxnIndexMap() ~> #evalFirstTx() ...</k>
  syntax AlgorandCommand  ::=
    "#evalFirstTx" "(" ")" [klabel(#evalFirstTx)]
  | "#evalNextTx" "(" ")" [klabel(#evalNextTx)]
  rule <k> #evalFirstTx() => #getNextTxn() ~> #startTx() ~> #evalTx() ~> #popTxnFront() ~> #endTx() ~> #evalNextTx() ... </k>
       <deque> TXN_DEQUE </deque>
    requires TXN_DEQUE =/=K .List
  rule <k> #evalNextTx() => #getNextTxn() ~> #startTx() ~> #evalTx() ~> #popTxnFront() ~> #endTx() ~> #evalNextTx() ... </k>
       <deque> TXN_DEQUE </deque>
    requires TXN_DEQUE =/=K .List andBool (getTxnGroupID(getNextTxnID()) ==K getTxnGroupID(getCurrentTxn()))
  rule <k> #evalNextTx() => #getNextTxn() ~> #startTx() ~> #evalTx() ~> #endTx() ... </k>
       <deque> TXN_DEQUE </deque>
    requires TXN_DEQUE =/=K .List andBool (getTxnGroupID(getNextTxnID()) =/=K getTxnGroupID(getCurrentTxn()))
  rule <k> #evalNextTx() => #checkSufficientBalance() ~> #endTx() ... </k>
       <returncode> _ => 0 </returncode>
       <deque> .List </deque>
  syntax AlgorandCommand  ::=
    "#startTx" "(" ")" [klabel(#startTx)]
  | "#endTx" "(" ")" [klabel(#endTx)]
  rule [starttx]: <k> #startTx() => .K ... </k>
  rule [endtx]: <k> #endTx()   => .K ... </k>
  syntax AlgorandCommand  ::=
    "#evalTx" "(" ")" [klabel(#evalTx)]
  rule <k> #evalTx()
        => #checkTxnSignature()
        ~> #executeTxn(TXN_TYPE)
        ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID> TXN_ID </txID>
         <typeEnum> TXN_TYPE </typeEnum>
         <sender> SENDER_ADDR </sender>
         ...
       </transaction>
       <touchedAccounts> TA => addToListNoDup(SENDER_ADDR, TA) </touchedAccounts>
   requires TXN_TYPE =/=K @appl
  rule <k> #evalTx()
        => #initContext()
        ~> #checkTxnSignature()
        ~> #executeTxn(TXN_TYPE)
        ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID> TXN_ID </txID>
         <typeEnum> TXN_TYPE </typeEnum>
         <resume> false => true </resume>
         <sender> SENDER_ADDR </sender>
         ...
       </transaction>
       <touchedAccounts> TA => addToListNoDup(SENDER_ADDR, TA) </touchedAccounts>
   requires TXN_TYPE ==K @appl
  rule <k> #evalTx()
         => #restoreContext()
         ~> #evalTeal()
         ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID> TXN_ID </txID>
         <typeEnum> TXN_TYPE </typeEnum>
         <resume> true </resume>
         <sender> SENDER_ADDR </sender>
         ...
       </transaction>
       <touchedAccounts> TA => addToListNoDup(SENDER_ADDR, TA) </touchedAccounts>
   requires TXN_TYPE ==K @appl
  syntax AlgorandCommand  ::=
    "#checkTxnSignature" "(" ")" [klabel(#checkTxnSignature)]
  rule <k> #checkTxnSignature() => .K ... </k>
  syntax AlgorandCommand  ::=
    "#clearState" "(" TValue "," TValue ")" [klabel(#clearState)]
  rule <k> #clearState(APP_ID, ADDR) => .K ...</k>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           (<optInApp>
             <optInAppID> APP_ID </optInAppID>
             ...
           </optInApp>) => .Bag
           ...
         </appsOptedIn>
         <appsCreated>
           <appID> APP_ID </appID>
           <localNumInts>     LOCAL_INTS      </localNumInts>
           <localNumBytes>    LOCAL_BYTES     </localNumBytes>
           ...
         </appsCreated>
         <minBalance> MIN_BALANCE => MIN_BALANCE
                                -Int (PARAM_APP_OPTIN_FLAT
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_UINT_MIN_BALANCE)
                                  *Int LOCAL_INTS)
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_BYTES_MIN_BALANCE)
                                  *Int LOCAL_BYTES))
         </minBalance>
         ...
       </account>
  rule <k> #clearState(APP_ID, ADDR) => .K ...</k>
       <account>
         <address> ADDR </address>
         <appsOptedIn>
           (<optInApp>
             <optInAppID> APP_ID </optInAppID>
             ...
           </optInApp>) => .Bag
           ...
         </appsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE
                                -Int (PARAM_APP_OPTIN_FLAT
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_UINT_MIN_BALANCE)
                                  *Int LOCAL_INTS)
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_BYTES_MIN_BALANCE)
                                  *Int LOCAL_BYTES))
         </minBalance>
         ...
       </account>
       <appsCreated>
         <appID> APP_ID </appID>
         <localNumInts>     LOCAL_INTS      </localNumInts>
         <localNumBytes>    LOCAL_BYTES     </localNumBytes>
         ...
       </appsCreated>
  syntax AlgorandCommand  ::=
    "#updatePrograms" "(" TValue "," KItem "," KItem ")" [klabel(#updatePrograms)]
  rule <k> #updatePrograms(APP_ID, APPROVAL_PGM, CLEAR_STATE_PGM) => .K ...</k>
       <app>
         <appID> APP_ID </appID>
         <approvalPgmSrc> _ => APPROVAL_PGM </approvalPgmSrc>
         <clearStatePgmSrc> _ => CLEAR_STATE_PGM </clearStatePgmSrc>
         ...
       </app>
  syntax AlgorandCommand  ::=
    "#deleteApplication" "(" TValue ")" [klabel(#deleteApplication)]
  rule <k> #deleteApplication(APP_ID) => .K ...</k>
       <account>
         <appsCreated>
           ((<app>
             <appID> APP_ID </appID>
             <globalNumInts>    GLOBAL_INTS     </globalNumInts>
             <globalNumBytes>   GLOBAL_BYTES    </globalNumBytes>
             <extraPages>    EXTRA_PAGES     </extraPages>
             ...
           </app>) => .Bag) ...
         </appsCreated>
         <minBalance> MIN_BALANCE => MIN_BALANCE
                                -Int (((1 +Int EXTRA_PAGES) *Int PARAM_APP_PAGE_FLAT)
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_UINT_MIN_BALANCE)
                                  *Int GLOBAL_INTS)
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_BYTES_MIN_BALANCE)
                                  *Int GLOBAL_BYTES))
         </minBalance>
         ...
       </account>
       <appCreator> (APP_ID |-> _) => .Map ... </appCreator>
  syntax AlgorandCommand  ::=
    "#closeTo" "(" TValue "," TValue "," TValue ")" [klabel(#closeTo)]
  rule <k> #closeTo(ASSET_ID, FROM, CLOSE_TO) => .K ...</k>
       <account>
         <address> FROM </address>
         <assetsOptedIn>
           (<optInAsset>
             <optInAssetID>      ASSET_ID </optInAssetID>
             <optInAssetBalance> BALANCE  </optInAssetBalance>
             <optInAssetFrozen>  _        </optInAssetFrozen>
           </optInAsset> => .Bag)
           ...
         </assetsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE -Int PARAM_MIN_BALANCE </minBalance>
         ...
       </account>
       <account>
         <address> CLOSE_TO </address>
         <optInAsset>
           <optInAssetID> ASSET_ID </optInAssetID>
           <optInAssetBalance> PREV_BALANCE => PREV_BALANCE +Int BALANCE </optInAssetBalance>
           ...
         </optInAsset>
           ...
       </account>
  syntax AlgorandCommand  ::=
    "#giveAlgos" "(" TValue "," TValue ")" [klabel(#giveAlgos)]
  rule <k> #giveAlgos(ACCOUNT, AMOUNT) => .K ...</k>
       <account>
         <address> ACCOUNT </address>
         <balance> BALANCE => BALANCE +Int AMOUNT </balance>
         ...
       </account>
       requires (BALANCE +Int AMOUNT) >=Int 0
  rule <k> #giveAlgos(ACCOUNT, AMOUNT) => #panic(INSUFFICIENT_FUNDS) ...</k>
       <account>
         <address> ACCOUNT </address>
         <balance> BALANCE </balance>
         ...
       </account>
       requires (BALANCE +Int AMOUNT) <Int 0
  syntax AlgorandCommand  ::=
    "#giveAsset" "(" TValue "," TValue "," TValue ")" [klabel(#giveAsset)]
  rule <k> #giveAsset(ASSET_ID, ACCOUNT, AMOUNT) => .K ...</k>
       <account>
         <address> ACCOUNT </address>
         <optInAsset>
           <optInAssetID> ASSET_ID </optInAssetID>
           <optInAssetBalance> BALANCE => BALANCE +Int AMOUNT </optInAssetBalance>
           <optInAssetFrozen> 0 </optInAssetFrozen>
         </optInAsset>
         ...
       </account>
       requires (BALANCE +Int AMOUNT) >=Int 0
  rule <k> #giveAsset(ASSET_ID, ACCOUNT, AMOUNT) => #panic(INSUFFICIENT_ASSET_BALANCE) ...</k>
       <account>
         <address> ACCOUNT </address>
         <optInAsset>
           <optInAssetID> ASSET_ID </optInAssetID>
           <optInAssetBalance> BALANCE </optInAssetBalance>
           <optInAssetFrozen> 0 </optInAssetFrozen>
         </optInAsset>
         ...
       </account>
       requires (BALANCE +Int AMOUNT) <Int 0
  syntax AlgorandCommand  ::=
    "#checkSufficientBalance" "(" ")" [klabel(#checkSufficientBalance)]
  rule <k> #checkSufficientBalance() => (#checkSufficientBalance(ADDR) ~> #checkSufficientBalance()) ...</k>
       <touchedAccounts> (ListItem(ADDR) => .List) ...</touchedAccounts>
  rule <k> #checkSufficientBalance() => .K ...</k>
       <touchedAccounts> .List </touchedAccounts>
  syntax AlgorandCommand  ::=
    "#checkSufficientBalance" "(" Bytes ")" [klabel(#checkSufficientBalance)]
  rule <k> #checkSufficientBalance(ADDR) => .K ...</k>
       <account>
         <address> ADDR </address>
         <balance> BALANCE </balance>
         <minBalance> MIN_BALANCE </minBalance>
         ...
       </account>
    requires BALANCE >=Int MIN_BALANCE
  rule <k> #checkSufficientBalance(ADDR) => #panic(MIN_BALANCE_VIOLATION) ...</k>
       <account>
         <address> ADDR </address>
         <balance> BALANCE </balance>
         <minBalance> MIN_BALANCE </minBalance>
         ...
       </account>
    requires BALANCE <Int MIN_BALANCE
  syntax AlgorandCommand  ::=
    "#evalTeal" "(" ")" [klabel(#evalTeal)]
  rule <k> #evalTeal() => #startExecution() ... </k>
  syntax AlgorandCommand  ::=
    "#executeTxn" "(" TValue ")" [klabel(#executeTxn)]
  rule <k> #executeTxn(@pay) => #giveAlgos(SENDER, 0 -Int AMOUNT) ~> #giveAlgos(RECEIVER, AMOUNT) ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>     TXN_ID   </txID>
         <sender>   SENDER   </sender>
         <receiver> RECEIVER </receiver>
         <amount>   AMOUNT   </amount>
         <rekeyTo>  REKEY_TO </rekeyTo>
         ...
       </transaction>
       <account>
         <address> SENDER </address>
         <key>     KEY => (#if REKEY_TO ==K getGlobalField(ZeroAddress) #then KEY #else REKEY_TO #fi) </key>
         ...
       </account>
       <touchedAccounts> TA => addToListNoDup(RECEIVER, TA) </touchedAccounts>
  syntax List  ::=
    "addToListNoDup" "(" Bytes "," List ")" [function, klabel(addToListNoDup), total]
  rule addToListNoDup(X, L) => ListItem(X) L requires notBool(X in L)
  rule addToListNoDup(X, L) => L requires X in L
  rule <k> #executeTxn(@pay) => #panic(INSUFFICIENT_FUNDS) ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>     TXN_ID   </txID>
         <sender>   SENDER   </sender>
         <amount>   AMOUNT   </amount>
         ...
       </transaction>
       <account>
         <address> SENDER </address>
         <balance> SENDER_BALANCE </balance>
         ...
       </account>
    requires SENDER_BALANCE -Int AMOUNT <Int 0
  rule <k> #executeTxn(@pay) => #panic(UNKNOWN_ADDRESS) ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>     TXN_ID   </txID>
         <sender>   SENDER   </sender>
         <amount>   _AMOUNT   </amount>
         <receiver> RECEIVER </receiver>
         ...
       </transaction>
       <accountsMap>
         AMAP
       </accountsMap>
    requires notBool ( SENDER in_accounts (<accountsMap> AMAP </accountsMap>) )
      orBool notBool ( RECEIVER in_accounts (<accountsMap> AMAP </accountsMap>) )
  rule <k> #executeTxn(@keyreg) => #panic(UNSUPPORTED_TXN_TYPE) ... </k>
  rule <k> #executeTxn(@acfg) => .K ...</k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                TXN_ID         </txID>
         <sender>              SENDER         </sender>
         <configAsset>         0              </configAsset>
         <configTotal>         TOTAL          </configTotal>
         <configDecimals>      DECIMALS       </configDecimals>
         <configDefaultFrozen> DEFAULT_FROZEN </configDefaultFrozen>
         <configUnitName>      UNIT_NAME      </configUnitName>
         <configAssetName>     NAME           </configAssetName>
         <configAssetURL>      ASSET_URL      </configAssetURL>
         <configMetaDataHash>  METADATA_HASH  </configMetaDataHash>
         <configManagerAddr>   MANAGER_ADDR   </configManagerAddr>
         <configReserveAddr>   RESERVE_ADDR   </configReserveAddr>
         <configFreezeAddr>    FREEZE_ADDR    </configFreezeAddr>
         <configClawbackAddr>  CLAWB_ADDR     </configClawbackAddr>
         <txConfigAsset>       _ => ASSET_ID  </txConfigAsset>
         ...
       </transaction>

       <nextAssetID> ASSET_ID => ASSET_ID +Int 1 </nextAssetID>
       <account>
         <address> SENDER </address>
         <assetsCreated>
           ASSETS =>
           (<asset>
             <assetID>            ASSET_ID       </assetID>
             <assetName>          NAME           </assetName>
             <assetUnitName>      UNIT_NAME      </assetUnitName>
             <assetTotal>         TOTAL          </assetTotal>
             <assetDecimals>      DECIMALS       </assetDecimals>
             <assetDefaultFrozen> DEFAULT_FROZEN </assetDefaultFrozen>
             <assetURL>           ASSET_URL      </assetURL>
             <assetMetaDataHash>  METADATA_HASH  </assetMetaDataHash>
             <assetManagerAddr>   MANAGER_ADDR   </assetManagerAddr>
             <assetReserveAddr>   RESERVE_ADDR   </assetReserveAddr>
             <assetFreezeAddr>    FREEZE_ADDR    </assetFreezeAddr>
             <assetClawbackAddr>  CLAWB_ADDR     </assetClawbackAddr>
           </asset>
           ASSETS)
         </assetsCreated>
         <assetsOptedIn>
           ASSETS_OPTED_IN =>
           <optInAsset>
             <optInAssetID>      ASSET_ID       </optInAssetID>
             <optInAssetBalance> TOTAL          </optInAssetBalance>
             <optInAssetFrozen>  DEFAULT_FROZEN </optInAssetFrozen>
           </optInAsset>
           ASSETS_OPTED_IN
         </assetsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE +Int PARAM_MIN_BALANCE </minBalance>
         ...
       </account>
       <assetCreator> .Map => (ASSET_ID |-> SENDER) ...</assetCreator>
  rule <k> #executeTxn(@acfg) => .K ...</k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                TXN_ID          </txID>
         <sender>              SENDER          </sender>
         <configAsset>         ASSET_ID:TValue </configAsset>
         <configManagerAddr>   MANAGER_ADDR    </configManagerAddr>
         <configReserveAddr>   RESERVE_ADDR    </configReserveAddr>
         <configFreezeAddr>    FREEZE_ADDR     </configFreezeAddr>
         <configClawbackAddr>  CLAWB_ADDR      </configClawbackAddr>
         ...
       </transaction>
       <asset>
         <assetID>            ASSET_ID               </assetID>
         <assetManagerAddr>   SENDER => MANAGER_ADDR </assetManagerAddr>
         <assetReserveAddr>   _ => RESERVE_ADDR      </assetReserveAddr>
         <assetFreezeAddr>    _ => FREEZE_ADDR       </assetFreezeAddr>
         <assetClawbackAddr>  _ => CLAWB_ADDR        </assetClawbackAddr>
         ...
       </asset>
    requires MANAGER_ADDR =/=K getGlobalField(ZeroAddress)
      orBool RESERVE_ADDR =/=K getGlobalField(ZeroAddress)
      orBool FREEZE_ADDR  =/=K getGlobalField(ZeroAddress)
      orBool CLAWB_ADDR   =/=K getGlobalField(ZeroAddress)
  rule <k> #executeTxn(@acfg) => .K ...</k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                TXN_ID          </txID>
         <sender>              SENDER          </sender>
         <configAsset>         ASSET_ID:TValue </configAsset>
         <configManagerAddr>   MANAGER_ADDR    </configManagerAddr>
         <configReserveAddr>   RESERVE_ADDR    </configReserveAddr>
         <configFreezeAddr>    FREEZE_ADDR     </configFreezeAddr>
         <configClawbackAddr>  CLAWB_ADDR      </configClawbackAddr>
         ...
       </transaction>
       <account>
         <address> CREATOR </address>
         <assetsCreated>
           (<asset>
             <assetID>            ASSET_ID </assetID>
             <assetManagerAddr>   SENDER   </assetManagerAddr>
             <assetTotal>         BALANCE  </assetTotal>
             ...
           </asset>) => .Bag
           ...
         </assetsCreated>
         <assetsOptedIn>
           (<optInAsset>
             <optInAssetID>      ASSET_ID </optInAssetID>
             <optInAssetBalance> BALANCE  </optInAssetBalance>
             ...
           </optInAsset>) => .Bag
           ...
         </assetsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE -Int PARAM_MIN_BALANCE </minBalance>
         ...
       </account>
       <assetCreator> (ASSET_ID |-> CREATOR) => .Map ...</assetCreator>
    requires MANAGER_ADDR ==K getGlobalField(ZeroAddress)
     andBool RESERVE_ADDR ==K getGlobalField(ZeroAddress)
     andBool FREEZE_ADDR  ==K getGlobalField(ZeroAddress)
     andBool CLAWB_ADDR   ==K getGlobalField(ZeroAddress)
  rule <k> #executeTxn(@acfg) => #panic(ASSET_NO_PERMISSION) ...</k>  [owise]
  rule <k> #executeTxn(@axfer) =>
                #giveAsset(ASSET_ID, SENDER, 0 -Int AMOUNT)
             ~> #giveAsset(ASSET_ID, RECEIVER, AMOUNT)
           ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID   </txID>
         <sender>        SENDER   </sender>
         <xferAsset>     ASSET_ID </xferAsset>
         <assetReceiver> RECEIVER </assetReceiver>
         <assetAmount>   AMOUNT   </assetAmount>
         <assetCloseTo>  CLOSE_TO </assetCloseTo>
         ...
       </transaction>
    requires assetCreated(ASSET_ID)
     andBool hasOptedInAsset(ASSET_ID, SENDER)
     andBool hasOptedInAsset(ASSET_ID, RECEIVER)
     andBool CLOSE_TO ==K getGlobalField(ZeroAddress)
     andBool (getOptInAssetField(AssetFrozen, RECEIVER, ASSET_ID) ==K 0)
     andBool (getOptInAssetField(AssetFrozen, SENDER,   ASSET_ID) ==K 0)
  rule <k> #executeTxn(@axfer) => #panic(ASSET_NOT_OPT_IN) ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID   </txID>
         <sender>        SENDER   </sender>
         <xferAsset>     ASSET_ID </xferAsset>
         <assetReceiver> RECEIVER </assetReceiver>
         <assetCloseTo>  CLOSE_TO </assetCloseTo>
         <assetAmount>   AMOUNT   </assetAmount>
         ...
       </transaction>
       <account>
         <address> SENDER </address>
         ...
       </account>
       <account>
         <address> RECEIVER </address>
         ...
       </account>
    requires assetCreated(ASSET_ID)
     andBool SENDER =/=K RECEIVER
     andBool CLOSE_TO ==K getGlobalField(ZeroAddress)
     andBool AMOUNT >Int 0
     andBool (notBool hasOptedInAsset(ASSET_ID, SENDER)
      orBool notBool hasOptedInAsset(ASSET_ID, RECEIVER))
  rule <k> #executeTxn(@axfer) => #panic(ASSET_NOT_FOUND) ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID   </txID>
         <xferAsset>     ASSET_ID </xferAsset>
         ...
       </transaction>
    requires notBool(assetCreated(ASSET_ID))
  rule <k> #executeTxn(@axfer) => #panic(ASSET_FROZEN) ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID   </txID>
         <sender>        SENDER   </sender>
         <assetReceiver> RECEIVER </assetReceiver>
         <xferAsset>     ASSET_ID </xferAsset>
         <assetAmount>   AMOUNT   </assetAmount>
         ...
       </transaction>
    requires assetCreated(ASSET_ID)
     andBool ((AMOUNT >Int 0
     andBool (hasOptedInAsset(ASSET_ID, SENDER)
              andBool hasOptedInAsset(ASSET_ID, RECEIVER)))
     andThenBool
            ((getOptInAssetField(AssetFrozen, SENDER, ASSET_ID) ==K 1)
     orBool  (getOptInAssetField(AssetFrozen, RECEIVER, ASSET_ID) ==K 1)))
  rule <k> #executeTxn(@axfer) => .K ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID   </txID>
         <sender>        SENDER   </sender>
         <xferAsset>     ASSET_ID </xferAsset>
         <assetReceiver> SENDER   </assetReceiver>
         <assetAmount>   0        </assetAmount>
         <assetCloseTo>  CLOSE_TO </assetCloseTo>
         ...
       </transaction>
       <account>
         <address> SENDER </address>
         <assetsOptedIn>
           ASSETS_OPTED_IN =>
           <optInAsset>
             <optInAssetID>      ASSET_ID </optInAssetID>
             <optInAssetBalance> 0 </optInAssetBalance>
             <optInAssetFrozen>
               getAssetParamsField(AssetDefaultFrozen, ASSET_ID)
             </optInAssetFrozen>
           </optInAsset>
           ASSETS_OPTED_IN
         </assetsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE +Int PARAM_MIN_BALANCE </minBalance>
         ...
       </account>
    requires assetCreated(ASSET_ID)
     andBool CLOSE_TO ==K getGlobalField(ZeroAddress)
     andBool notBool hasOptedInAsset(ASSET_ID, SENDER)
  rule <k> #executeTxn(@axfer) =>
                #giveAsset(ASSET_ID, SENDER, 0 -Int AMOUNT)
             ~> #giveAsset(ASSET_ID, RECEIVER, AMOUNT)
             ~> #closeTo(ASSET_ID, SENDER, CLOSE_TO)
           ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID          </txID>
         <sender>        SENDER          </sender>
         <xferAsset>     ASSET_ID        </xferAsset>
         <assetReceiver> RECEIVER        </assetReceiver>
         <assetAmount>   AMOUNT          </assetAmount>
         <assetCloseTo>  CLOSE_TO        </assetCloseTo>
         ...
       </transaction>
    requires assetCreated(ASSET_ID)
     andBool CLOSE_TO =/=K getGlobalField(ZeroAddress)
  rule <k> #executeTxn(@afrz) => .K ... </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                 TXN_ID              </txID>
         <sender>               SENDER              </sender>
         <freezeAccount>        FREEZE_ACCOUNT      </freezeAccount>
         <freezeAsset>          ASSET_ID            </freezeAsset>
         <assetFrozen>          FREEZE              </assetFrozen>
         ...
       </transaction>
       <account>
         <address> FREEZE_ACCOUNT </address>
         <optInAsset>
           <optInAssetID>      ASSET_ID       </optInAssetID>
           <optInAssetFrozen>  _ => FREEZE    </optInAssetFrozen>
           ...
         </optInAsset>
         ...
       </account>
    requires getAssetParamsField(AssetFreeze, ASSET_ID) ==K SENDER
  rule <k> #executeTxn(@appl) => #executeAppl(APP_ID) ...</k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                 TXN_ID              </txID>
         <sender>               SENDER              </sender>
         <applicationID>        0                   </applicationID>
         <approvalProgramSrc>   APPROVAL_PGM_SRC    </approvalProgramSrc>
         <clearStateProgramSrc> CLEAR_STATE_PGM_SRC </clearStateProgramSrc>
         <approvalProgram>      APPROVAL_PGM        </approvalProgram>
         <clearStateProgram>    CLEAR_STATE_PGM     </clearStateProgram>
         <globalNui>            GLOBAL_INTS         </globalNui>
         <globalNbs>            GLOBAL_BYTES        </globalNbs>
         <localNui>             LOCAL_INTS          </localNui>
         <localNbs>             LOCAL_BYTES         </localNbs>
         <extraProgramPages>    EXTRA_PAGES         </extraProgramPages>
         <txApplicationID>      _ => APP_ID         </txApplicationID>
         ...
       </transaction>
       <accountsMap>
         <account>
           <address> SENDER </address>
           <minBalance> MIN_BALANCE => MIN_BALANCE
                                  +Int ((1 +Int EXTRA_PAGES) *Int PARAM_APP_PAGE_FLAT)
                                  +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_UINT_MIN_BALANCE)
                                    *Int GLOBAL_INTS)
                                  +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_BYTES_MIN_BALANCE)
                                    *Int GLOBAL_BYTES)
           </minBalance>
           <appsCreated>
             APPS =>
             <app>
               <appID>            APP_ID              </appID>
               <approvalPgmSrc>   APPROVAL_PGM_SRC    </approvalPgmSrc>
               <clearStatePgmSrc> CLEAR_STATE_PGM_SRC </clearStatePgmSrc>
               <approvalPgm>      APPROVAL_PGM        </approvalPgm>
               <clearStatePgm>    CLEAR_STATE_PGM     </clearStatePgm>
               <globalNumInts>       GLOBAL_INTS         </globalNumInts>
               <globalNumBytes>      GLOBAL_BYTES        </globalNumBytes>
               <localNumInts>        LOCAL_INTS          </localNumInts>
               <localNumBytes>       LOCAL_BYTES         </localNumBytes>
               <extraPages>       EXTRA_PAGES         </extraPages>
               ...
             </app>
             APPS
           </appsCreated>
           ...
         </account>
         (.Bag =>
         (<account>
           <address> getAppAddressBytes(APP_ID) </address>
           ...
         </account>))
         ...
       </accountsMap>
       <appCreator> (.Map => (APP_ID |-> SENDER)) ... </appCreator>
       <nextAppID> APP_ID => APP_ID +Int 1 </nextAppID>
    requires notBool(APP_ID in_apps(<appsCreated> APPS </appsCreated>))
     andBool GLOBAL_INTS +Int GLOBAL_BYTES <=Int PARAM_MAX_GLOBAL_KEYS
     andBool LOCAL_INTS  +Int LOCAL_BYTES  <=Int PARAM_MAX_LOCAL_KEYS
  rule <k> #executeTxn(@appl) => #executeAppl(APP_ID) ...</k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                 TXN_ID              </txID>
         <applicationID>        APP_ID:TValue       </applicationID>
         ...
       </transaction>
  requires APP_ID =/=K 0
  syntax AlgorandCommand  ::=
    "#executeAppl" "(" TValue ")" [klabel(#executeAppl)]
  rule <k> #executeAppl(APP_ID) =>
               #initApp(APP_ID)
            ~> #loadInputPgm(APPROVAL_PGM)
            ~> #evalTeal()
            ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID        </txID>
         <onCompletion>  @ NoOp        </onCompletion>
         ...
       </transaction>
       <app>
         <appID>          APP_ID       </appID>
         <approvalPgmSrc> APPROVAL_PGM </approvalPgmSrc>
         ...
       </app>
  rule <k> #executeAppl(APP_ID) =>
               #initApp(APP_ID)
            ~> #loadInputPgm(APPROVAL_PGM)
            ~> #evalTeal()
            ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID  </txID>
         <sender>        SENDER  </sender>
         <onCompletion>  @ OptIn </onCompletion>
         ...
       </transaction>
       <account>
         <address> SENDER </address>
         <appsOptedIn>
           OPTED_IN_APPS =>
           <optInApp>
             <optInAppID>   APP_ID </optInAppID>
             <localInts> .Map   </localInts>
             <localBytes> .Map   </localBytes>
           </optInApp>
           OPTED_IN_APPS
         </appsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE
                                +Int PARAM_APP_OPTIN_FLAT
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_UINT_MIN_BALANCE)
                                      *Int LOCAL_INTS)
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_BYTES_MIN_BALANCE)
                                      *Int LOCAL_BYTES)
         </minBalance>
         ...
       </account>
       <app>
         <appID>          APP_ID       </appID>
         <approvalPgmSrc> APPROVAL_PGM </approvalPgmSrc>
         <localNumInts>      LOCAL_INTS   </localNumInts>
         <localNumBytes>     LOCAL_BYTES  </localNumBytes>
         ...
       </app>
     requires notBool hasOptedInApp(APP_ID, SENDER)
  rule <k> #executeAppl(APP_ID) =>
               #initApp(APP_ID)
            ~> #loadInputPgm(APPROVAL_PGM)
            ~> #evalTeal()
            ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID  </txID>
         <sender>        SENDER  </sender>
         <onCompletion>  @ OptIn </onCompletion>
         ...
       </transaction>
       <account>
         <address> SENDER </address>
         <appsCreated>
           <app>
             <appID>          APP_ID       </appID>
             <approvalPgmSrc> APPROVAL_PGM </approvalPgmSrc>
             <localNumInts>      LOCAL_INTS   </localNumInts>
             <localNumBytes>     LOCAL_BYTES  </localNumBytes>
             ...
           </app>
           ...
         </appsCreated>
         <appsOptedIn>
           OPTED_IN_APPS =>
           <optInApp>
             <optInAppID>   APP_ID </optInAppID>
             <localInts> .Map        </localInts>
             <localBytes> .Map        </localBytes>
           </optInApp>
           OPTED_IN_APPS
         </appsOptedIn>
         <minBalance> MIN_BALANCE => MIN_BALANCE
                                +Int PARAM_APP_OPTIN_FLAT
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_UINT_MIN_BALANCE)
                                  *Int LOCAL_INTS)
                                +Int ((PARAM_MIN_BALANCE_PER_ENTRY +Int PARAM_BYTES_MIN_BALANCE)
                                  *Int LOCAL_BYTES)
         </minBalance>
         ...
       </account>
     requires notBool hasOptedInApp(APP_ID, SENDER)
  rule <k>
         #executeAppl(APP_ID) =>
              #initApp(APP_ID)
           ~> #loadInputPgm(APPROVAL_PGM)
           ~> #evalTeal()
           ~> #clearState(APP_ID, SENDER)
         ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID        </txID>
         <sender>        SENDER        </sender>
         <onCompletion>  @ CloseOut    </onCompletion>
         ...
       </transaction>
       <app>
         <appID>          APP_ID       </appID>
         <approvalPgmSrc> APPROVAL_PGM </approvalPgmSrc>
         ...
       </app>
  rule <k>
         #executeAppl(APP_ID) =>
              #initApp(APP_ID)
           ~> #loadInputPgm(CLEAR_STATE_PGM)
           ~> #evalTeal()
           ~> #clearState(APP_ID, SENDER)
         ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID        </txID>
         <sender>        SENDER        </sender>
         <onCompletion> @ ClearState   </onCompletion>
         ...
       </transaction>
       <app>
         <appID>            APP_ID          </appID>
         <clearStatePgmSrc> CLEAR_STATE_PGM </clearStatePgmSrc>
         ...
       </app>
  rule <k>
         #executeAppl(APP_ID) =>
              #initApp(APP_ID)
           ~> #loadInputPgm(APPROVAL_PGM)
           ~> #evalTeal()
           ~> #updatePrograms(APP_ID, NEW_APPROVAL_PGM, NEW_CLEAR_STATE_PGM)
         ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>                 TXN_ID              </txID>
         <onCompletion>         @ UpdateApplication </onCompletion>
         <approvalProgramSrc>   NEW_APPROVAL_PGM    </approvalProgramSrc>
         <clearStateProgramSrc> NEW_CLEAR_STATE_PGM </clearStateProgramSrc>
         ...
       </transaction>
       <app>
         <appID>          APP_ID       </appID>
         <approvalPgmSrc> APPROVAL_PGM </approvalPgmSrc>
         ...
       </app>
  rule <k>
         #executeAppl(APP_ID) =>
              #initApp(APP_ID)
           ~> #loadInputPgm(APPROVAL_PGM)
           ~> #evalTeal()
           ~> #deleteApplication(APP_ID)
         ...
       </k>
       <currentTx> TXN_ID </currentTx>
       <transaction>
         <txID>          TXN_ID              </txID>
         <onCompletion>  @ DeleteApplication </onCompletion>
         ...
       </transaction>
       <app>
         <appID>          APP_ID       </appID>
         <approvalPgmSrc> APPROVAL_PGM </approvalPgmSrc>
         ...
       </app>
  rule <k> #executeTxn(@ccfg) => #panic(UNSUPPORTED_TXN_TYPE) ... </k>
  rule <k> #executeTxn(@ccall) => #panic(UNSUPPORTED_TXN_TYPE) ... </k>
  rule <k> #executeTxn(@cfx) => #panic(UNSUPPORTED_TXN_TYPE) ... </k>
endmodule

module AVM-TESTING-SYNTAX
  imports public TEAL-PARSER-SYNTAX
  imports public STRING
  imports public JSON
endmodule

module AVM-TESTING
  imports public INT
  imports public LIST
  imports public BYTES
  imports public ALGO-BLOCKCHAIN
  imports public ALGO-TXN
  imports public TEAL-CONSTANTS
  imports public AVM-CONFIGURATION
  imports public ALGOD-MODELS
  imports public AVM-EXECUTION
  imports public K-IO
  configuration <avm-testing>
      <kavm/>
      <state-dumps> .List </state-dumps>
    </avm-testing>
  syntax Bool  ::=
    "isValidScenario" "(" JSON ")" [function, klabel(isValidScenario)]
  rule isValidScenario({ "stages": [ STAGES ]}) => setupStageIsUniqueAndComesFirst(STAGES)
  syntax Bool  ::=
    "setupStageIsUniqueAndComesFirst" "(" JSONs ")" [function, klabel(setupStageIsUniqueAndComesFirst)]
  rule setupStageIsUniqueAndComesFirst(.JSONs) => false
  rule setupStageIsUniqueAndComesFirst(FIRST, OTHERS:JSONs)
       => assertStageTypes("setup-network", FIRST) andBool
          assertStageTypes("submit-transactions", OTHERS)
  syntax Bool  ::=
    "assertStageTypes" "(" String "," JSONs ")" [function, klabel(assertStageTypes)]
  rule assertStageTypes(EXPECTED_TYPE, { "data" : _, "stage-type": STAGE_TYPE }
                                       , OTHER_STAGES:JSONs
                                       )
       => STAGE_TYPE ==String EXPECTED_TYPE andBool assertStageTypes(EXPECTED_TYPE, OTHER_STAGES)
  rule assertStageTypes(EXPECTED_TYPE, { "data": _, "expected-returncode": _, "stage-type": STAGE_TYPE }
                                       , OTHER_STAGES:JSONs
                                       )
       => STAGE_TYPE ==String EXPECTED_TYPE andBool assertStageTypes(EXPECTED_TYPE, OTHER_STAGES)
  rule assertStageTypes(_EXPECTED_TYPE, .JSONs) => true
  rule <k> INPUT:JSON => #readScenario(INPUT) ... </k>
    requires isValidScenario(INPUT)
  rule <k> _INPUT:JSON => #panic(INVALID_JSON) ... </k>  [owise]
  syntax TestingCommand  ::=
    "#readScenario" "(" JSON ")" [klabel(#readScenario)]
  rule <k> #readScenario({ "stages": [ SETUP_STAGE, EXECUTION_STAGES:JSONs ]})
        => #readSetupStage(SETUP_STAGE)
        ~> #readExecutionStages([EXECUTION_STAGES]) ...
       </k>
  syntax TestingCommand  ::=
    "#readSetupStage" "(" JSON ")" [klabel(#readSetupStage)]
  rule <k> #readSetupStage({ "data": {"accounts": ACCTS:JSON}
                           , "stage-type": "setup-network"
                           })
        => #setupAccounts(ACCTS) ~> #setupCounters() ...
       </k>
  syntax TestingCommand  ::=
    "#setupCounters" "(" ")" [klabel(#setupCounters)]
  rule <k> #setupCounters() => .K ... </k>
       <assetCreator> ASSET_CREATOR_MAP </assetCreator>
       <appCreator>   APP_CREATOR_MAP   </appCreator>
       <nextAssetID> _ => maxInList(keys_list(ASSET_CREATOR_MAP)) +Int 1 </nextAssetID>
       <nextAppID>   _ => maxInList(keys_list(APP_CREATOR_MAP)) +Int 1   </nextAppID>
  syntax Int  ::=
    "maxInList" "(" List ")" [function, klabel(maxInList), total]
  | "maxInListImpl" "(" List "," Int ")" [function, klabel(maxInListImpl), total]
  rule maxInList(XS) => maxInListImpl(XS, 0)
  rule maxInListImpl(.List, ACC) => ACC
  rule maxInListImpl(ListItem(X) XS, ACC) => maxInListImpl(XS, X)
    requires X >Int ACC
  rule maxInListImpl(ListItem(X) XS, ACC) => maxInListImpl(XS, ACC)
    requires X <=Int ACC
  syntax TestingCommand  ::=
    "#readExecutionStages" "(" JSONs ")" [klabel(#readExecutionStages)]
  rule <k> #readExecutionStages([.JSONs]) => .K ... </k>
  rule <k> #readExecutionStages([STAGE, .JSONs])
        => #readExecutionStage(STAGE) ...
       </k>
  syntax TestingCommand  ::=
    "#readExecutionStage" "(" JSON ")" [klabel(#readExecutionStage)]
  rule <k> #readExecutionStage({ "data": {"transactions": TXNS:JSON}
                               , "expected-returncode": EXPECTED_RETURN_CODE
                               , "stage-type": "submit-transactions"
                               })
        => #setupTransactions(TXNS) ~> #initGlobals() ~> #evalTxGroup()
        ~> #checkExecutionResults(EXPECTED_RETURN_CODE) ...
       </k>
  syntax TestingCommand  ::=
    "#checkExecutionResults" "(" Int ")" [klabel(#checkExecutionResults)]
  rule <k> #checkExecutionResults(EXPECTED_RETURN_CODE)
        => #dumpFinalState() ...
       </k>
       <returncode> RETURN_CODE => 0 </returncode>
   requires RETURN_CODE ==Int EXPECTED_RETURN_CODE
  rule <k> #checkExecutionResults(EXPECTED_RETURN_CODE)
        => .K ...
       </k>
       <returncode> RETURN_CODE => 1 </returncode>
   requires notBool (RETURN_CODE ==Int EXPECTED_RETURN_CODE)
  syntax TestingCommand  ::=
    "#dumpFinalState" "(" ")" [klabel(#dumpFinalState)]
  rule <k> #dumpFinalState()
        => #log(JSON2String({ "accounts": [ #dumpAccounts(<accountsMap> ACCS </accountsMap>)]
                            , "transactions": [ #dumpConfirmedTransactions(<transactions> TXNS </transactions>)]}))
        ...
       </k>
       <accountsMap>  ACCS </accountsMap>
       <transactions> TXNS </transactions>
       <state-dumps>
         ...
         ( .List
        => ListItem({ "accounts"     : [ #dumpAccounts(<accountsMap> ACCS </accountsMap>)                ]
                    , "transactions" : [ #dumpConfirmedTransactions(<transactions> TXNS </transactions>) ]
                    , .JSONs
                   })
         )
       </state-dumps>
endmodule
