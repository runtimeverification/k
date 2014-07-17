// Copyright (c) 2013-2014 K Team. All Rights Reserved.
// TODO: inner LiterateDefinitionComment.Type

// Is there any reason to separate imports from module definitions?
syntax ModuleItem ::=
  "imports" NAME[name] [Import]
| "/*" LiterateCommentType[lcType] Any[value] "*/"
  [LiterateModuleComment, implements = LiterateComment]
| Name[type] "[" Name[label] "]:" ANY[content] [StringSentence]
| "syntax" "priorities" PriorityBlockExtended[priorityBlocks, list = ">"] [PriorityExtend]
| "syntax" Assoc[assoc] KLabelConstant[tags, list = " "] [PriorityExtendedAssoc] // rename tags to KLabels
| "syntax" "restrictions" Sort[sort] Terminal[terminal]) "-/-" STRING[pattern] [Restrictions]
| "syntax" Sort[sort] attrs ::= PriorityBlock[priorityBlocks, list=">"] [Syntax]

//  ("[" NAME[label,default = "\"\""] "]:")? Term[body] ("requires" Term[requires, default = null])? ("ensures" Term[ensures, default = null])? [class = Sentence] // omit for now

enum Assoc ::= left[Left] | right | non-assoc

/*
syntax Sentence ::=
  Configuration.java
  Context.java
  Rule.java // why does this have builtinLookups in it?
*/

code {
    public Restrictions(String sort, String terminal, String pattern) {
        if (sort != null && terminal != null)
            System.out.println("A restriction can have only one of sort or terminal!");
        if (sort != null)
            this.sort = new Sort(sort);
        else
            this.terminal = new Terminal(terminal);
        this.pattern = pattern;
    }
}

syntax ASTNode ::=
  Assoc[assoc] KLabelConstant[productions, list=" "] [PriorityBlockExtended, final]
| Assoc[assoc] ": " Production[productions, list = "\n| "] [PriorityBlock]
| ProductionItem[items, list = " "]
  String[sort, hidden] String[ownerModuleName, hidden] [Production]
| "ProductionItem" [ProductionItem, abstract]

enum ListType ::= "*"[List] | "+"[NeList]

----------


syntax DataStructureSort.java ::= // What is this?
  STRING(name) STRING(type) STRING(constr) STRING(element) STRING(unit) ImmutableMap<String, String> operatorLabels;



Subclasses of TERM

CollectionBuiltin.java
CollectionItem.java
Collection.java
Constant.java
DataStructureBuiltin.java
Empty.java
FloatBuiltin.java
FreezerHole.java
Freezer.java
FreezerLabel.java
GenericToken.java
Hole.java
IntBuiltin.java
KApp.java
KInjectedLabel.java
KLabelConstant.java
KLabel.java
KList.java
KSequence.java
ListBuiltin.java
ListItem.java
List.java
ListLookup.java
ListTerminator.java
ListUpdate.java
MapBuiltin.java
MapItem.java
Map.java
MapLookup.java
MapUpdate.java
Rewrite.java
SetBuiltin.java
SetItem.java
Set.java
SetLookup.java
SetUpdate.java
StringBuiltin.java
TermComment.java
TermCons.java
Token.java
Variable.java
