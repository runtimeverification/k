package ro.uaic.fmse.kplugin;

import com.intellij.lexer.FlexLexer;
import com.intellij.psi.tree.IElementType;
import ro.uaic.fmse.kplugin.psi.KTypes;
import com.intellij.psi.TokenType;

%%

%public
%class KLexer
%implements FlexLexer
%unicode
%function advance
%type IElementType
%eof{  //return;
%eof}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\r\n]
WhiteSpace     = ({LineTerminator} | [ \t\f])+

/* comments */
Comment = {TraditionalComment} | {EndOfLineComment} | {DocumentationComment}

TraditionalComment   = "/*" [^*] ~"*/" | "/*" "*"+ "/"
EndOfLineComment     = "//" {InputCharacter}* {LineTerminator}
DocumentationComment = "/**" {CommentContent} "*"+ "/"
CommentContent       = ( [^*] | \*+ [^/*] )*

Identifier = [:jletter:] [:jletterdigit:]*
Label = "'" [:jletter:] ([:jletterdigit:] | "_" | `. )*

DecIntegerLiteral = 0 | [1-9][0-9]*

String = \"([^\n\r\"\\] | \\t | \\n | \\r | \\\" | \\)*\"

%%


<YYINITIAL> {
/* keywords */
  "require"        { return KTypes.KEYWORD; }
  "module"         { return KTypes.KEYWORD; }
  "endmodule"      { return KTypes.KEYWORD; }
  "imports"        { return KTypes.KEYWORD; }
  "configuration"  { return KTypes.KEYWORD; }
  "syntax"         { return KTypes.KEYWORD; }
  "rule"           { return KTypes.KEYWORD; }
  "when"           { return KTypes.KEYWORD; }
  "context"        { return KTypes.KEYWORD; }

  /* reusable builtins */
    "store"
  | "select"
  | "keys"
  | "values"
  | "in"           { return KTypes.BUILTIN_FUNC; }

  /* operators */
  // Array
    "store"
  | "const-array"
  | "select"
  | "size-of-array"

  // Bag
  | ".Bag"
  | "in"
  | "size"

  // Bool
  | "true"
  | "false"
  | "notBool"
  | "andBool"
  | "andThenBool"
  | "xorBool"
  | "orBool"
  | "orElseBool"
  | "impliesBool"
  | "==Bool"
  | "=/=Bool"

  // Float
  | "-Float"
  | "^Float"
  | "*Float"
  | "/Float"
  | "%Float"
  | "+Float"
  | "<=Float"
  | "<Float"
  | ">=Float"
  | ">Float"
  | "==Float"
  | "=/=Float"
  | "Int2Float"
  | "Float2Int"

  // Id
  | "Id2String"
  | "String2Id"

  // Int
  | "~Int"
  | "^Int"
  | "*Int"
  | "/Int"
  | "%Int"
  | "+Int"
  | "-Int"
  | ">>Int"
  | "<<Int"
  | "&Int"
  | "xorInt"
  | "|Int"
  | "minInt"
  | "maxInt"
  | "absInt"
  | "<=Int"
  | "<Int"
  | ">=Int"
  | ">Int"
  | "==Int"
  | "=/=Int"
  | "=Int"
  | "dividesInt"

  | "==K"
  | "=/=K"
  | "#if"
  | "#then"
  | "#else"
  | "#fi"
  | "<=Set"
  | "==Set"
  | "=/=Set"
  | "<=Map"
  | "==Map"
  | "=/=Map"
  | "==KList"
  | "=/=KList"
  | "==KLabel"
  | "=/=KLabel"
  | "==List"
  | "=/=List"

  // List
  | ".List"

  // Map
  | ".Map"
  | "|->"
  | "["
  | "]"
  | "<-"
  | "undef"
  | "keys"
  | "values"

  // Set
  | ".Set"

  // String
  | "+String"
  | "==String"
  | "lengthString"
  | "chrChar"
  | "ordChar"
  | "substrString"
  | "findString"
  | "rfindString"
  | "findChar"
  | "rfindChar"
  | "Float2String"
  | "String2Float"
  | "String2Int"
  | "Int2String"
  | "KLabel2String"
  | "String2KLabel"
  | "replaceAll"
  | "replace"
  | "replaceFirst"
  | "countAllOccurences"
  | "trim"
  | "ltrim"
  | "rtrim"
  | "=/=String"
  | "<String"
  | "<=String"
  | ">String"
  | ">=String"
  | "categoryChar"
  | "directionalityChar"

  // KList
  | ".KList"

  // KResult

  | ".K"
  | "~>"

  | "=>"
  | "..."
  | "::="
  | "HOLE"
  { return KTypes.OPERATOR; }

  "Array" | "Bag" | "Bool" | "Float" | "Id" | "Int"
  | "List" | "Map" | "Set" | "String" | "Char" | "KList" | "KResult"
  | "BagItem" | "ListItem" | "SetItem" { return KTypes.BUILTIN_ID; }

  "("                       {return KTypes.LEFT_PAREN;}
  ")"                       {return KTypes.RIGHT_PAREN;}
  "{" | "}"                 {return KTypes.BRACE;}
  "|"                     {return KTypes.VERTICAL_BAR;}
  "<" | ">" | "</" | "/>" {return KTypes.TAG_BORDER;}

  ",,"                    {return KTypes.DOUBLE_COMMA;}
  ","                     {return KTypes.COMMA;}
  "_"                     {return KTypes.UNDERSCORE;}

  {Label}                        { return KTypes.LABEL_TOK; }

  /* identifiers */
  {Identifier}                   { return KTypes.USER_ID; }

  /* literals */
  {DecIntegerLiteral}            { return KTypes.INTEGER_LITERAL; }

  /* comments */
  {Comment}                      { return KTypes.COMMENT; }

  /* whitespace */
  {WhiteSpace}                   { return TokenType.WHITE_SPACE; }

  {String}                       { return KTypes.STRING; }
}

//Instead of error, this should be valid content of rules and syntax that was not matched by other categories.
/* error fallback */
.                             { return KTypes.OTHER; }
