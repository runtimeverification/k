// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "io/io.k"
require "io-aux.k"

/********************************/
module AST-SYNTAX

syntax Type ::=
  "Bool" // "boolean" requires "is" for getters
| "String" // "String" requires quoting and string escape
| "Name" // "String" no quoting, but perhaps Id escape
| "Any" // "String" no quoting or escaping
> Id // A regular type name

syntax Program ::= List{Syntax, ""}

// TODO: syn -> syntax
// TODO: "code" Id "{" Code "}" (w/o quotes)
syntax Syntax ::= "syn" Id "::=" SyntaxBody
| "code" Id Code // "{{{" Code2 "}}}"
| "doc" Id Doc
| "doc" Id Id Doc
  //| "code" Id "{" Code "}" // | "enum"
syntax SyntaxBody ::= List{Prod, "|"}

syntax Prod ::= ProdBody ProdAttrs
syntax ProdBody ::= List{Field, ""}
syntax ProdAttrs ::= "[" ProdAttrsBody "]"
syntax ProdAttrsBody ::= List{ProdAttr, ","}
syntax ProdAttr ::= "final" | "abstract" | "non-generated" | "implements" "=" Id > Id

syntax Field ::= "attrs" | String | Type FieldAttrs
syntax FieldAttrs ::= "[" FieldAttrsBody "]"
syntax FieldAttrsBody ::= List{FieldAttr, ","}
syntax FieldAttr ::=
  "private" | "protected" | "package"
| "list" "=" String /*separator*/ | "non-list"
| "mutable" | "immutable"
| "required" | "optional" "=" String/*default value*/ | "omitted" "=" String/*initial value*/
| "shown" | "hidden"
> Id

//syntax Code ::= Lexer{("}"? "}"? ~[\}])*}
//syntax Code ::= "%" Lexer{((~[\%])? ("\n")?) *} "%"
//syntax Code ::= "%" Lexer{(~[\%])*} "%"
//syntax Code ::= Token{"%" (~[\%])* "%"}
//syntax Code ::= "%" Code2 "%"
//syntax Code3 ::= List{Code2, "\\n"}
syntax Code ::= Token{ "{{{" ("}"?"}"?~[\}])* "}}}" } [onlyLabel]
//syntax Doc ::= Token{ "%%" (~[\%])* "%%" } [onlyLabel]
//syntax Doc ::= Token{ "/**" ("/"* "*"* (~[\*\/])+)* "/"* "*"* "*/" } [onlyLabel] // This regex is odd b/c K doesn't support "|" in regex
//syntax Doc ::= Token{ "/**" ("/"* "*"* (~[\*\/])+)* "*/" } [onlyLabel] // This regex is odd b/c K doesn't support "|" in regex
syntax Doc ::= Code
//syntax Code2 ::= Token{ "%" (~[\%])* "%" } [onlyLabel]

syntax String ::= Code2String(Code) [function] | Doc2String(Doc) [function]
rule Code2String(C) => substrString(#tokenToString(C), 3, lengthString(#tokenToString(C)) -Int 3)
//rule Doc2String(D) => #tokenToString(D)
rule Doc2String(D) => "/**" +String Code2String(D) +String "*/" //#tokenToString(D)

syntax Program ::= appendPrograms(Program, Program) [function]
rule appendPrograms(.Program, P) => P
rule appendPrograms((S::Syntax) P1, P2) => appendPrograms(P1, S P2)

//syntax Code -/- ~[\}]
//syntax Code -/- [\}].~[\}]
//syntax Code -/- [\}].[\}].~[\}]
//syntax Code ::= "{" Code "}" | Token{~[\{\}]+}
//syntax Code ::= Token{
//List{String, ""}

/*
public enum Assoc {
  left("Left"), right("Right");

  private final String print;
  private Assoc(String print) { this.print = print; }
  @Override public String toString() { return print; }
}
*/

endmodule

/********************************/
module UTIL

//syntax ConcatStrings ::= List{String, ""}

syntax String ::= String "~" String [left, function] > String "~~" String [left, function] > String "~~~" String [left, function]
rule S1 ~ S2 => S1 +String S2
rule S1 ~~ S2 => S1 +String " " +String S2
rule S1 ~~~ S2 => S1 +String "\n" +String S2

syntax Strings ::= List{String, ""}
syntax String ::= concatString(Strings) [function] | vconcatString(Strings) [function]
rule concatString(.Strings) => ""
rule concatString(S SS) => (S +String " ") +String concatString(SS)

rule vconcatString(.Strings) => ""
rule vconcatString(S SS) => (S +String "\n") +String vconcatString(SS)

endmodule

/********************************/
module IR /* Intermediate representation */

imports AST-SYNTAX

syntax Class ::= class(Id/*name*/, ClassMode, String/*extends*/, Implements, Fields)
syntax ClassMode ::= "default" | "abstract" | "final" | "non-generated"
syntax Implements ::= List{Id, ","}

syntax Fields ::= List{Field, ""}
syntax Field ::= "attrs" | str(String) | field(Id/*name*/, Protection, Type/*type*/, IsList, IsMutable, IsArg, IsShown)
syntax Protection ::= "package" | "protected" | "private"
syntax IsList ::= list(String/*separator*/) | "non-list"
syntax IsMutable ::= "mutable" | "immutable"
syntax IsArg ::= "required" | optional(String/*default*/) | omitted(String/*initial*/)
syntax IsShown ::= "shown" | "hidden"

syntax Class ::= applyProdAttrs(Class, ProdAttrs) [function]
rule applyProdAttrs(Class, [.ProdAttrsBody]) => Class // TODO: there is a bug somewhere
rule applyProdAttrs(class(_,(_=>final),_,_,_), [final, A => A])
rule applyProdAttrs(class(_,(_=>abstract),_,_,_), [abstract, A => A])
rule applyProdAttrs(class(_,(_=>non-generated),_,_,_), [non-generated, A => A])
rule applyProdAttrs(class(_,_,_,(I => Interface, I),_), [(implements = Interface), A => A])

syntax Fields ::= generateFields(ProdBody) [function]
syntax Field ::= fieldAttr(FieldAttrs, Field) [function]
rule generateFields(.ProdBody) => .
rule generateFields(attrs Fs) => attrs generateFields(Fs)
rule generateFields(S:String Fs) => str(S) generateFields(Fs)
rule generateFields((T:Type ([F::Id,A::FieldAttrsBody]::FieldAttrs))::Field (Fs::ProdBody)) => fieldAttr([A], field(F, private, T, non-list, mutable, required, shown)) generateFields(Fs)

// Need a debugger to explain why particular rules don't fire
// TODO: (protected => .), _
rule fieldAttr([.FieldAttrsBody], F) => F
rule fieldAttr([private, A => A], field(_,(_ => private),_,_,_,_,_))
rule fieldAttr([protected, A => A], field(_,(_ => protected),_,_,_,_,_))
rule fieldAttr([package, A => A], field(_,(_ => package),_,_,_,_,_))
rule fieldAttr([list = Sep, A => A], field(_,_,_,(_ => list(Sep)),_,_,_))
rule fieldAttr([non-list, A => A], field(_,_,_,(_ => non-list),_,_,_))
rule fieldAttr([mutable, A => A], field(_,_,_,_,(_ => mutable),_,_))
rule fieldAttr([immutable, A => A], field(_,_,_,_,(_ => immutable),_,_))
rule fieldAttr([required, A => A], field(_,_,_,_,_,(_ => required),_))
rule fieldAttr([optional = S, A => A], field(_,_,_,_,_,(_ => optional(S)),_))
rule fieldAttr([omitted = S, A => A], field(_,_,_,_,_,(_ => omitted(S)),_))
rule fieldAttr([omitted = S, A => A], field(_,_,_,_,_,(_ => omitted(S)),_))
rule fieldAttr([shown, A => A], field(_,_,_,_,_,_,(_ => shown)))
rule fieldAttr([hidden, A => A], field(_,_,_,_,_,_,(_ => hidden)))

endmodule

/********************************/
module OUTPUT

imports UTIL
imports IR

//syntax Files ::= List{File, ";"}
//syntax File ::= file(String,String)

//context file(HOLE,_)
//context file(_,HOLE)

// TODO: associative operators? (to avoid ambig parse)

// TODO: should shalow copy copy list contents?

syntax String ::= classToString(Class,Program) [function]
rule classToString(class(Class,non-generated,Extends,Implements,Fields),Cache) => ""
rule classToString(class(Class,Mode,Extends,Implements,Fields),Cache) =>
  "+++++ "~Id2String(Class)~" +++++" ~~~
  "/* DO NOT EDIT THIS FILE. IT IS GENERATED BY AST.K */" ~~~
  "package org.kframework.kil;" ~~~
  "" ~~~
  "import org.kframework.visitors.Transformer;" ~~~
  "import org.kframework.visitors.Visitor;" ~~~
  "import org.kframework.visitors.exceptions.TransformerException;" ~~~
  "" ~~~
  doc(Class, Cache) ~~~
  "public" ~~ mode(Mode) ~~ Id2String(Class) ~~ "extends" ~~ Extends ~~ implements(Implements) ~~ "{" ~~~
     fieldDeclarations(Fields, Class, Cache) ~~~
  "" ~~~
     constructors(Id2String(Class),Fields) ~~~
  "  public" ~~ Id2String(Class) ~ "(" ~ Id2String(Class) ~~ "that" ~ ")" ~~ "{" ~~~
  "    super(that);" ~~~
       copyFields(Fields) ~~~
  "  }" ~~~
  "" ~~~
  "  @Override public void accept(Visitor visitor) { visitor.visit(this); }" ~~~
  "" ~~~
  "  @Override public ASTNode accept(Transformer transformer)" ~~~
  "      throws TransformerException {" ~~~
  "    return transformer.transform(this);" ~~~
  "  }" ~~~
  "" ~~~
     fieldMethods(Fields) ~~~
  "" ~~~
  "  @Override public boolean equals(Object obj) {" ~~~
  "    if (obj == null) return false;" ~~~
  "    if (obj == that) return true;" ~~~
  "    if (!(obj instanceof" ~~ Id2String(Class) ~ ")) return false;" ~~~
  "    " ~ Id2String(Class) ~~ "that = (" ~ Id2String(Class) ~ ")obj;" ~~~
       equalFields(Fields) ~
  "    return true;" ~~~
  "  }" ~~~
  "" ~~~
  "  @Override public" ~~ Id2String(Class) ~~ "shallowCopy() { return new" ~~ Id2String(Class) ~ "(this); }" ~~~
  "  @Override public String toString() {" ~~~
  "    StringBuilder sb = new StringBuilder();" ~~~
       toStrings(Fields) ~~~
  "    return sb.toString();" ~~~
  "  }" ~~~
  "" ~~~
  "  @Override public int hashCode() {" ~~~
  "    int hash = 1;" ~~~
       hashCodes(Fields) ~~~
  "    return hash;" ~~~
  "  }" ~~~
  "" ~~~
//  "  public enum Type {" ~~~
//  "    " ~ getTypes(...) ~~~
//  "  }"
//  "" ~~~
  "  @Override public" ~~ Extends ~ ".Type getType() {" ~~~
  "    return" ~~ Extends ~ ".Type." ~ Id2String(Class) ~ ";" ~~~
  "  }" ~~~
  code(Class, Cache) ~~~
  "}\n\n"
//TODO: when Mode =/= non-generated

// Class Mode
syntax String ::= mode(ClassMode) [function]
rule mode(abstract) => "abstract"
rule mode(final) => "final"
rule mode(default) => "/*default*/"

// Class Implementation List
syntax String ::= implements(Implements) [function]
rule implements(.) => ""
rule implements(I:Id, Rest) => "implements" ~~ implementsAux(I, Rest)
syntax String ::= implementsAux(Implements) [function]
rule implementsAux(Nam, .K) => Id2String(Nam)
rule implementsAux(Nam, Nam2, Rest) => Id2String(Nam) ~ "," ~~ implementsAux(Nam2, Rest)

// Field Declarations
syntax String ::= fieldDeclarations(Fields, Id, Program) [function] | fieldDeclaration(Field, Id, Program) [function] | protection(Protection) [function] | final(IsMutable) [function] | list(IsList, String) [function] | type(Type) [function]
rule fieldDeclarations(., _, _) => ""
rule fieldDeclarations(attrs Fs, Class, Cache) => fieldDeclarations(Fs, Class, Cache)
rule fieldDeclarations(str(_) Fs, Class, Cache) => fieldDeclarations(Fs, Class, Cache)
rule fieldDeclarations((F::Field) Fs, Class, Cache) => fieldDeclaration(F, Class, Cache) ~~~ fieldDeclarations(Fs, Class, Cache)
rule fieldDeclaration(field(Nam, Protection, Type, IsList, IsMutable, CtorArg, _), Class, Cache) =>
  doc(Class, Nam, Cache) ~
  "  " ~ protection(Protection) ~~ final(IsMutable) ~~ list(IsList, type(Type)) ~~ Id2String(Nam) ~ ";"

rule protection(protected) => "protected"
rule protection(private) => "private"
rule protection(package) => ""
rule final(mutable) => "/*mutable*/"
rule final(immutable) => "final"
rule list(list(_), T) => "List<" ~T ~">"
rule list(non-list, T) => T
rule type(Bool) => "boolean"
rule type(String) => "String"
rule type(Name) => "String"
rule type(Any) => "String"
rule type(I:Id) => Id2String(I)

// Constructors
syntax String ::= constructors(String, Fields) [function] | constructors0(String, Fields, Fields, Fields) [function] | constructors1(String, Fields, Fields, Fields) [function] | constructor(String, Fields, Fields, Fields) [function] | ctorArgs(Fields) [function] | assignArgs(Fields) [function] | assignNonArgs(Fields) [function]
rule constructors(Nam, Fs) => constructors0(Nam, noStr(Fs), .Fields, .Fields)

// TODO: need warning if misspelled "function"

//syntax Program ::= String
//rule <k>_ => .</k><out>_ => constructors0 ( "DefinitionItem" , field ( "predefined" , protected , Bool , non-list , mutable , required ), .Fields , .Fields )</out>

syntax Fields ::= noStr(Fields) [function]
rule noStr(.K) => .Fields
rule noStr(attrs Fs) => noStr(Fs)
rule noStr(str(_) Fs) => noStr(Fs)
rule noStr(field(N,P,T,L,M,O,S) Fs) => field(N,P,T,L,M,O,S) noStr(Fs)

// TODO: is list matching not associative?
//rule constructors0(Nam, field(_,_,_,_,_,_) Fs1, Fs2, Omit) => "FOOO"

//syntax Fields ::= reverseFields(Fields) [function]
//rule reverseFields(F:Field (Fs:Fields)) => (reverseFields(Fs:Fields) (F:Field))

// TODO: Note we are reversing the order of Fs and Omit

// Fs2 and Omit are reversed
rule constructors0(Nam, .Fields, Fs, Omit) => constructor(Nam, Fs, .Fields, Omit) ~~~ constructors1(Nam, Fs, .Fields, Omit)
rule constructors0(Nam, field(F,P,T,L,M,required,S) Fs1, Fs2, Omit) =>
     constructors0(Nam, Fs1, field(F,P,T,L,M,required,S) Fs2, Omit)
rule constructors0(Nam, field(F,P,T,L,M,optional(O),S) Fs1, Fs2, Omit) =>
     constructors0(Nam, Fs1, field(F,P,T,L,M,optional(O),S) Fs2, Omit)
rule constructors0(Nam, field(F,P,T,L,M,omitted(O),S) Fs1, Fs2, Omit) =>
     constructors0(Nam, Fs1, Fs2, field(F,P,T,L,M,omitted(O),S) Omit)

// Fs and Omit are reversed, Req is forward
rule constructors1(Nam, .Fields, Req, Omit) => ""
rule constructors1(Nam, field(F,P,T,L,M,required,S) Fs, Req, Omit) =>
     constructors1(Nam, Fs, field(F,P,T,L,M,required,S) Req, Omit)
rule constructors1(Nam, field(F,P,T,L,M,optional(O),S) Fs, Req, Omit) =>
     constructor(Nam, Fs, Req, field(F,P,T,L,M,optional(O),S) Omit) ~~~
     constructors1(Nam, Fs, Req, field(F,P,T,L,M,optional(O),S) Omit)

// Fs and Omit are reversed, Req is forward
rule constructor(Nam, Fs, Req, Omit) =>
  "  public" ~~ Nam ~ "(" ~ ctorArgs(appendFields(Fs, Req)) ~ ")" ~~ "{" ~~~
  "    super();" ~~~
       assignArgs(appendFields(Fs, Req)) ~~~
       assignNonArgs(Omit) ~~~
  "  }"

// TODO: is "." always ".K"?
// Fs1 is reversed, Fs2 is forward
syntax Fields ::= appendFields(Fields, Fields) [function]
rule appendFields(.Fields,Fs) => Fs
rule appendFields((F::Field) Fs1, Fs2) => appendFields(Fs1, F Fs2)

// TODO: local (in .k but not .lambda) syntax

// TODO: Note we have to unreverse the args
rule ctorArgs(.Fields) => ""
//rule ctorArgs(. Fs) => ctorArgs(Fs)
//rule ctorArgs(((.Fields) :: Fields) Fs) => ctorArgs(Fs)
rule ctorArgs(field(Nam,_,T,L,_,_,_)) => list(L,type(T)) ~~ Id2String(Nam)
rule ctorArgs(field(Nam,_,T,L,_,_,_) Fs) => list(L,type(T)) ~~ Id2String(Nam) ~ "," ~~ ctorArgs(Fs)
rule assignArgs(.Fields) => ""
rule assignArgs(field(Nam,_,_,_,_,_,_) Fs) => "    this." ~ Id2String(Nam) ~~ "=" ~~ Id2String(Nam) ~ ";" ~~~ assignArgs(Fs)
rule assignNonArgs(.Fields) => ""
rule assignNonArgs(field(Nam,_,_,_,_,optional(S),_) Fs) => "    this." ~ Id2String(Nam) ~~ "=" ~~ S ~";" ~~~ assignNonArgs(Fs)
rule assignNonArgs(field(Nam,_,_,_,_,omitted(S),_) Fs) => "    this." ~ Id2String(Nam) ~~ "=" ~~ S ~ ";" ~~~ assignNonArgs(Fs)

// TODO: +String should work regardless of association

// Copy Constructor
syntax String ::= copyFields(Fields) [function]
rule copyFields(.) => ""
rule copyFields(attrs Fs) => copyFields(Fs)
rule copyFields(str(_) Fs) => copyFields(Fs)
rule copyFields(field(Nam,_,_,_,_,_,_) Fields) =>
  "    this." ~ Id2String(Nam) ~~ "=" ~~ "that." ~ Id2String(Nam) ~ ";" ~~~ copyFields(Fields)

// Field Accessors
syntax String ::= fieldMethods(Fields) [function] | fieldMethod(Field) [function] | getMethod(String,Type,IsList) [function] | setMethod(String,Type,IsList,IsMutable) [function] | isOrGet(Type, IsList) [function]
rule fieldMethods(.) => ""
rule fieldMethods((F::Field) Fs) => fieldMethod(F) ~~~ fieldMethods(Fs)
rule fieldMethod(attrs) => ""
rule fieldMethod(str(_)) => ""
rule fieldMethod(field(Nam,_,T,L,M,_,_)) => getMethod(Id2String(Nam),T,L) ~~~ setMethod(Id2String(Nam),T,L,M)
rule getMethod(Nam,T,L) => "  " ~ list(L, type(T)) ~~ isOrGet(T,L)~upcase(Nam)~"() { return" ~~ Nam~"; } "
rule setMethod(Nam,T,L,immutable) => ""
rule setMethod(Nam,T,L,mutable) =>
  "  void" ~~ "set"~upcase(Nam)~"(" ~ list(L,type(T)) ~~ Nam ~ ") {" ~~ "this."~Nam ~~ "=" ~~ Nam ~ ";" ~~ "}"
//rule fieldMethdod // is$FIELD, append$FIELD
rule isOrGet(Bool, non-list) => "is"
rule isOrGet(T,L) => "get" when /* (T, L) =/=KItem (Bool, non-list) */ T =/=K Bool orBool L =/=K (non-list) // TODO: maude error if we do non-list:IsList

syntax String ::= upcase(String) [function]
rule upcase(S) => chrChar(ordChar(substrString(S, 0, 1)) -Int 32) +String substrString(S, 1, lengthString(S)) when ordChar(substrString(S, 0, 1)) >=Int 97

// Equality Operator
syntax String ::= equalFields(Fields) [function] | equalField(Field) [function]
rule equalFields(.) => ""
rule equalFields(attrs Fields) => equalFields(Fields)
rule equalFields(str(_) Fields) => equalFields(Fields)
rule equalFields(F:Field Fields) => equalField(F) ~~~ equalFields(Fields)
rule equalField(field(Field,_,_,_,_,_,_)) =>
  "    if (this."~Id2String(Field)~~"== null ^ that."~Id2String(Field)~~"== null) return false;" ~~~
  "    if (this."~Id2String(Field)~~"!= null && this."~Id2String(Field)~".equals(that."~Id2String(Field)~")) return false;"

//syntax K ::= map(KLabel,List)
//rule map(_,.) => ""
//rule map(L,(X, Xs)) => L(X) map(L, Xs)

// toString Method
syntax String ::= toStrings(Fields) [function] | toStringsAux(Type, String) [function] | encodeString(String) [function]
rule toStrings(.) => ""
rule toStrings(attrs Fs) => "    sb.append(attributes);" ~~~ toStrings(Fs)
rule toStrings(str(S) Fs) => "    sb.append(\""~encodeString(S)~"\");" ~~~ toStrings(Fs)
rule toStrings(field(Nam,_,_,_,_,_,hidden) Fs) => toStrings(Fs)
rule toStrings(field(Nam,_,T,non-list,_,_,shown) Fs) => "    "~toStringsAux(T,Id2String(Nam)) ~~~ toStrings(Fs)
rule toStrings(field(Nam,_,T,list(Sep),_,_,shown) Fs) =>
  "    if ("~Id2String(Nam)~" == null) { sb.append(\"null\"); }" ~~~
  "    else {" ~~~
  "      for ("~type(T)~~"item :"~~Id2String(Nam)~") {" ~~~
  "        "~toStringsAux(T,"item")~~"sb.append(\""~encodeString(Sep)~"\");" ~~~
  "      }" ~~~
  "      if ("~Id2String(Nam)~".size() != 0) { sb.setLength(sb.length() - \""~encodeString(Sep)~"\".length()); }" ~~~
  "    }"

rule toStringsAux(String, Nam) => "sb.append(org.kframework.utils.StringUtil.escapeK("~Nam~"));"
rule toStringsAux(T, Nam) => "sb.append("~Nam~");" when T =/=K String

rule encodeString(S) => replaceAll(replaceAll(S, "\\", "\\\\"), "\n", "\\n")

// HashCode Method
syntax String ::= hashCodes(Fields) [function] | hashCode(Field) [function]
rule hashCodes(.) => ""
rule hashCodes(attrs Fs) => hashCodes(Fs)
rule hashCodes(str(_) Fs) => hashCodes(Fs)
rule hashCodes(F:Field Fs) => hashCode(F) ~~~ hashCodes(Fs)
rule hashCode(field(Nam,_,_,_,_,_,_)) => "    hash = hash * 17 + ("~Id2String(Nam)~" == null ? 0 : "~Id2String(Nam)~".hashCode());"

//rule Code2String(% #token(_,C) %) => C

// TODO: way to filter from list
syntax String ::= code(Id, Program) [function]
rule code(Class, .Program) => ""
rule code(Class, code Class (C::Code) P) => Code2String(C) ~~~ code(Class, P)
rule code(Class, code Class2 C P) => code(Class, P) when Class =/=K Class2
rule code(Class, (doc _ _) P) => code(Class, P)
rule code(Class, (doc _ _ _) P) => code(Class, P)
rule code(Class, (syn _ ::= _) P) => code(Class, P)

syntax String ::= doc(Id, Program) [function] | doc(Id, Id, Program) [function]
rule doc(Class, .Program) => ""
rule doc(Class, doc Class (D::Doc) P) => Doc2String(D) ~~~ doc(Class, P)
rule doc(Class, doc Class2 (D::Doc) P) => doc(Class, P) when Class =/=K Class2
rule doc(Class, (doc _ _ _) P) => doc(Class, P)
rule doc(Class, (code _ _) P) => doc(Class, P)
rule doc(Class, (syn _ ::= _) P) => doc(Class, P)

rule doc(Class, Field, .Program) => ""
rule doc(Class, Field, (doc Class Field D) P) => "  " ~ Doc2String(D) ~~~ doc(Class, Field, P)
rule doc(Class, Field, (doc Class2 Field2 D) P) => doc(Class, Field, P) when Class =/=K Class2 orBool Field =/=K Field2
rule doc(Class, Field, (doc _ _) P) => doc(Class, Field, P)
rule doc(Class, Field, (code _ _) P) => doc(Class, Field, P)
rule doc(Class, Field, (syn _ ::= _) P) => doc(Class, Field, P)

endmodule

/********************************/
module AST

imports AST-SYNTAX
imports UTIL
imports IR
imports OUTPUT
imports URIS
imports TCP-HOOKS
imports IO-AUX
// TODO: allow inline list declarations
// TODO: handle argument permutations
// Priorities between rules?
// "@" patterns
// Auto-sorted functions
// What is ListItem?
// Tree based priorities
// Why doesn't "(X => .) | _" work?
// Local let bindings for rules

//rule <k>code Class { C } S => S</k>
//     <code>R:Map => R:Map (Class |-> (_ => C))</code>

rule <k>P</k><cache>.Program => P</cache>
rule <k>code Class C S => S</k>
rule <k>(doc Class D) S => S</k>
rule <k>(doc Class Field D) S => S</k>
//rule <k>.Program</k><cache>_ => .Program</cache>

//configuration <T><k>$PGM:Program</k><out>.Strings</out></T>
configuration <T><k>$PGM:Program</k><cache>.Program</cache><out stream="stdout">.List</out></T>
//<out stream="stdout">.List</out>
//<out>... . => ListItem(classToString(...))</out>

// Initial rule to kick off one clause
rule <k>syn Extends ::= .SyntaxBody S => S</k>
     //<k>(syn Extends ::= _) => . ...</k>
//rule <k>(syn Extends ::= (Body [Class::Id, Attrs] | B => B)) S</k>
//     <cache>P</cache>
//     <out>... . => ListItem(classToString(applyProdAttrs(class(Class, default, Id2String(Extends), ., generateFields(Body)), [Attrs]), appendPrograms(P, S)))</out>
// P was appendPrograms(P, S)
rule <k>(. => writeNonEmptyToFile(Id2String(Class)~".javax", classToString(applyProdAttrs(class(Class, default, Id2String(Extends), ., generateFields(Body)), [Attrs]), P))) ~>
        (syn Extends ::= (Body [Class::Id, Attrs] | B => B)) S</k>
     <cache>P</cache>
//     <out>... . => ListItem(classToString(applyProdAttrs(class(Class, default, Id2String(Extends), ., generateFields(Body)), [Attrs]), appendPrograms(P, S)))</out>

syntax KItem ::= writeNonEmptyToFile(String, String)
rule writeNonEmptyToFile(File, "") => .
rule writeNonEmptyToFile(File, Str) => writeToFile(File, Str) when Str =/=String ""

//syntax KItem ::= writeToFile(String, String) | checkOpen(String, K) | writeToFileNum(String, Int, String) | checkWrite(String, Int, String, K)
//rule writeToFile(Filename, Content) => writeToFileNum(Filename, checkOpen(Filename, #open(Filename, "w")), Content)
//rule checkOpen(_, X:Int) => X
//rule <k>checkOpen(Filename, X:TCPError) => X </k><out>... . => ListItem("Error opening " ~ Filename ~": " ~ K2String(X))</out>
//
//rule writeToFileNum(Filename, Num, Content) => checkWrite(Filename, Num, Content, #write(Num, Content)) ~> #close(Num)
//rule checkWrite(_, _, _, X:Int) => X
//rule <k>checkWrite(Filename, _, _, X:TCPError) => X </k><out>... . => ListItem("Error writing to " ~ Filename ~": " ~ K2String(X))</out>

//rule <filenum>.K => open("test.javax", "w")</filenum>
//     (write(x, "test") ~> close(x))

endmodule
