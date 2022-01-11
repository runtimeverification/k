module IELE-SYNTAX
  imports IELE-COMMON
  syntax IeleNameToken  ::=
    r"(?<![A-Za-z0-9\\_\\.\\-\\$])[a-zA-Z\\.\\_\\$][0-9a-zA-Z\\.\\_\\-\\$]*" [notInRules, prec(3), token]
  syntax Keyword  ::=
    "load" [token]
  | "store" [token]
  | "sload" [token]
  | "sstore" [token]
  | "iszero" [token]
  | "not" [token]
  | "add" [token]
  | "mul" [token]
  | "sub" [token]
  | "div" [token]
  | "exp" [token]
  | "mod" [token]
  | "addmod" [token]
  | "mulmod" [token]
  | "expmod" [token]
  | "byte" [token]
  | "sext" [token]
  | "twos" [token]
  | "and" [token]
  | "or" [token]
  | "xor" [token]
  | "shift" [token]
  | "lt" [token]
  | "le" [token]
  | "gt" [token]
  | "ge" [token]
  | "eq" [token]
  | "ne" [token]
  | "cmp" [token]
  | "sha3" [token]
  syntax Keyword  ::=
    "br" [token]
  | "call" [token]
  | "staticcall" [token]
  | "at" [token]
  | "send" [token]
  | "gaslimit" [token]
  | "ret" [token]
  | "void" [token]
  | "revert" [token]
  | "log" [token]
  | "create" [token]
  | "copycreate" [token]
  | "selfdestruct" [token]
  | "contract" [token]
  | "external" [token]
  | "define" [token]
  | "public" [token]
  | "log2" [token]
  | "bswap" [token]
  | "calladdress" [token]
  syntax IeleNameToken  ::=
    Keyword [token]
  syntax NumericIeleName  ::=
    r"[0-9]+" [token, prec(2)]
  syntax StringIeleName  ::=
    r"\\\"(([^\\\"\\\\])|(\\\\[0-9a-fA-F]{2}))*\\\"" [token]
endmodule

module IELE-COMMON
  imports DOMAINS-SYNTAX
  imports INT-SYNTAX
  syntax KResult
  syntax NumericIeleName  ::=
    Int
  syntax StringIeleName [token]
  syntax IeleName  ::=
    NumericIeleName
  syntax IeleNameToken [token]
  syntax IeleName  ::=
    IeleNameToken
  syntax IeleName  ::=
    StringIeleName [avoid, function, klabel(StringIeleName), symbol]
  syntax GlobalName  ::=
    "@" IeleName
  syntax LocalName  ::=
    "%" IeleName
  syntax LocalNames  ::=
    List{LocalName,","} [klabel(localNameList)]
  syntax Constant  ::=
    IntConstant
  | GlobalName
  syntax IntConstant  ::=
    Int
  | Bool
  | HexConstant
  syntax HexConstant  ::=
    r"0x[0-9a-fA-F]+" [token]
  syntax LValue  ::=
    LocalName
  syntax LValues  ::=
    NeList{LValue,","} [klabel(lvalueList)]
  syntax Operand  ::=
    LValue
  | Constant
  syntax Operands  ::=
    List{Operand,","} [klabel(operandList)]
  syntax NonEmptyOperands  ::=
    NeList{Operand,","} [klabel(operandList)]
  syntax Ints  ::=
    List{Int,","} [klabel(operandList)]
  syntax Operands  ::=
    Ints
  syntax Operands  ::=
    NonEmptyOperands
  syntax Ints  ::=
    NonEmptyInts
  syntax NonEmptyOperands  ::=
    NonEmptyInts
  syntax NonEmptyInts  ::=
    NeList{Int,","} [klabel(operandList)]
  syntax AssignInst  ::=
    LValue "=" Operand
  syntax LoadInst  ::=
    LValue "=" "load" Operand [hybrid, strict(2)]
  syntax LoadInst  ::=
    LValue "=" "load" Operand "," Operand "," Operand [hybrid, seqstrict(2,3,4)]
  syntax StoreInst  ::=
    "store" Operand "," Operand [hybrid, seqstrict(1,2)]
  syntax StoreInst  ::=
    "store" Operand "," Operand "," Operand "," Operand [hybrid, seqstrict(1,2,3,4)]
  syntax SLoadInst  ::=
    LValue "=" "sload" Operand [hybrid, strict(2)]
  syntax SStoreInst  ::=
    "sstore" Operand "," Operand [hybrid, seqstrict(1,2)]
  syntax IsZeroInst  ::=
    LValue "=" "iszero" Operand [hybrid, strict(2)]
  syntax NotInst  ::=
    LValue "=" "not" Operand [hybrid, strict(2)]
  syntax AddInst  ::=
    LValue "=" "add" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax MulInst  ::=
    LValue "=" "mul" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax SubInst  ::=
    LValue "=" "sub" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax DivInst  ::=
    LValue "=" "div" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax ExpInst  ::=
    LValue "=" "exp" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax ModInst  ::=
    LValue "=" "mod" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax AddModInst  ::=
    LValue "=" "addmod" Operand "," Operand "," Operand [hybrid, seqstrict(2,3,4)]
  syntax MulModInst  ::=
    LValue "=" "mulmod" Operand "," Operand "," Operand [hybrid, seqstrict(2,3,4)]
  syntax ExpModInst  ::=
    LValue "=" "expmod" Operand "," Operand "," Operand [hybrid, seqstrict(2,3,4)]
  syntax LogInst  ::=
    LValue "=" "log2" Operand [hybrid, strict(2)]
  syntax ByteInst  ::=
    LValue "=" "byte" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax SExtInst  ::=
    LValue "=" "sext" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax TwosInst  ::=
    LValue "=" "twos" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax BswapInst  ::=
    LValue "=" "bswap" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax AndInst  ::=
    LValue "=" "and" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax OrInst  ::=
    LValue "=" "or" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax XorInst  ::=
    LValue "=" "xor" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax ShiftInst  ::=
    LValue "=" "shift" Operand "," Operand [hybrid, seqstrict(2,3)]
  syntax Predicate  ::=
    "lt"
  | "le"
  | "gt"
  | "ge"
  | "eq"
  | "ne"
  syntax CmpInst  ::=
    LValue "=" "cmp" Predicate Operand "," Operand [hybrid, seqstrict(3,4)]
  syntax SHA3Inst  ::=
    LValue "=" "sha3" Operand [hybrid, strict(2)]
  syntax JumpInst  ::=
    "br" IeleName
  syntax CondJumpInst  ::=
    "br" Operand "," IeleName [hybrid, strict(1)]
  syntax LocalCallInst  ::=
    "call" Operand "(" Operands ")"
  | LValues "=" "call" Operand "(" Operands ")" [hybrid, strict(2,3)]
  syntax AccountCallInst  ::=
    LValues "=" "call" Operand "at" Operand "(" Operands ")" "send" Operand "," "gaslimit" Operand [hybrid, seqstrict(2,3,4,5,6)]
  syntax AccountCallInst  ::=
    LValues "=" "staticcall" Operand "at" Operand "(" Operands ")" "gaslimit" Operand [hybrid, seqstrict(2,3,4,5)]
  syntax CallAddressInst  ::=
    LValue "=" "calladdress" GlobalName "at" Operand [hybrid, strict(3)]
  syntax ReturnInst  ::=
    "ret" NonEmptyOperands [hybrid, strict(1)]
  | "ret" "void"
  syntax RevertInst  ::=
    "revert" Operand [hybrid, strict(1)]
  syntax LogInst  ::=
    "log" Operand [hybrid, strict(1)]
  | "log" Operand "," NonEmptyOperands [hybrid, seqstrict(1,2)]
  syntax CreateInst  ::=
    LValue "," LValue "=" "create" IeleName "(" Operands ")" "send" Operand [hybrid, seqstrict(4,5)]
  syntax CreateInst  ::=
    LValue "," LValue "=" "copycreate" Operand "(" Operands ")" "send" Operand [hybrid, seqstrict(3,4,5)]
  syntax SelfdestructInst  ::=
    "selfdestruct" Operand [hybrid, strict(1)]
  syntax IeleNameToken  ::=
    "iele.invalid" [token]
  syntax IeleNameToken  ::=
    "iele.gas" [token]
  syntax IeleNameToken  ::=
    "iele.gasprice" [token]
  syntax IeleNameToken  ::=
    "iele.gaslimit" [token]
  syntax IeleNameToken  ::=
    "iele.beneficiary" [token]
  syntax IeleNameToken  ::=
    "iele.timestamp" [token]
  syntax IeleNameToken  ::=
    "iele.number" [token]
  syntax IeleNameToken  ::=
    "iele.difficulty" [token]
  syntax IeleNameToken  ::=
    "iele.address" [token]
  syntax IeleNameToken  ::=
    "iele.origin" [token]
  syntax IeleNameToken  ::=
    "iele.caller" [token]
  syntax IeleNameToken  ::=
    "iele.callvalue" [token]
  syntax IeleNameToken  ::=
    "iele.msize" [token]
  syntax IeleNameToken  ::=
    "iele.codesize" [token]
  syntax IeleNameToken  ::=
    "iele.blockhash" [token]
  syntax IeleNameToken  ::=
    "iele.balance" [token]
  syntax IeleNameToken  ::=
    "iele.extcodesize" [token]
  syntax IeleNameToken  ::=
    "iele.ecrec" [token]
  syntax IeleNameToken  ::=
    "iele.sha256" [token]
  syntax IeleNameToken  ::=
    "iele.rip160" [token]
  syntax IeleNameToken  ::=
    "iele.id" [token]
  syntax IeleNameToken  ::=
    "iele.ecadd" [token]
  syntax IeleNameToken  ::=
    "iele.ecmul" [token]
  syntax IeleNameToken  ::=
    "iele.ecpairing" [token]
  syntax Instruction  ::=
    AssignInst
  | LoadInst
  | StoreInst
  | SLoadInst
  | SStoreInst
  | IsZeroInst
  | NotInst
  | AddInst
  | MulInst
  | SubInst
  | DivInst
  | ExpInst
  | ModInst
  | AddModInst
  | MulModInst
  | ExpModInst
  | ByteInst
  | SExtInst
  | TwosInst
  | BswapInst
  | AndInst
  | OrInst
  | XorInst
  | ShiftInst
  | CmpInst
  | SHA3Inst
  | JumpInst
  | CondJumpInst
  | LocalCallInst
  | AccountCallInst
  | CallAddressInst
  | ReturnInst
  | RevertInst
  | LogInst
  | CreateInst
  | SelfdestructInst
  syntax Instructions  ::=
    List{Instruction,""} [format(%1%2%n%3), klabel(instructionList)]
  syntax TopLevelDefinition  ::=
    FunctionDefinition
  | GlobalDefinition
  | ContractDeclaration
  syntax TopLevelDefinitions  ::=
    List{TopLevelDefinition,""} [format(%1%2%n%3), klabel(topLevelDefinitionList)]
  syntax ContractDefinition  ::=
    "contract" IeleName "{" TopLevelDefinitions "}" [format(%1 %2 %3%n%i%4%d%n%5)]
  syntax Contract  ::=
    List{ContractDefinition,""} [klabel(contractDefinitionList)]
  syntax ContractDeclaration  ::=
    "external" "contract" IeleName
  syntax GlobalDefinition  ::=
    GlobalName "=" IntConstant [klabel(globalDefinition)]
  syntax FunctionSignature  ::=
    GlobalName "(" FunctionParameters ")"
  syntax FunctionParameters  ::=
    LocalNames
  syntax FunctionDefinition  ::=
    "define" FunctionSignature "{" Blocks "}" [format(%1 %2 %3%i%n%4%d%n%5%n)]
  | "define" "public" FunctionSignature "{" Blocks "}" [format(%1 %2 %3 %4%i%n%5%d%n%6%n)]
  syntax LabeledBlock  ::=
    IeleName ":" Instructions
  syntax LabeledBlocks  ::=
    List{LabeledBlock,""} [klabel(labeledBlockList)]
  syntax UnlabeledBlock  ::=
    Instructions
  syntax Blocks [flatPredicate]
  syntax Blocks  ::=
    UnlabeledBlock LabeledBlocks [avoid]
  | LabeledBlocks
  syntax IeleNameToken  ::=
    "deposit" [token]
  syntax IeleNameToken  ::=
    "init" [token]
  rule call NAME ( ARGS ) => .LValues = call NAME ( ARGS )  [alias]
  rule ret void => ret .NonEmptyOperands  [alias]
endmodule

module IELE
  imports IELE-COMMON
  imports BOOL
endmodule
