// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*
ASTNode.java
Term.java
Attribute.java
Attributes.java
ConfigurationNotFound.java
ConfigurationNotUnique.java
ParseError.java // What is this?
interface LiterateComment.java
Location.java extends Attribute
enum KSort.java // missing KResult?
string constants KSorts.java // should just be toString of KSort
*/

// TODO: Enum and 'getType'
// TODO: does Production need equality to take account of klabel attribute?
// TODO: ListType as enum in UserList
// TODO: SortName and SortRef should be different
// TODO: Assoc as enum in PriorityExtendedAssoc

syn ASTNode ::=
  "Definition" [Definition, non-generated]
| "DefinitionItem " Bool[predefined, omitted = "false"] [DefinitionItem, abstract]
| "ModuleItem" [ModuleItem, abstract]

doc DefinitionItem predefined {{{ Set iff the item was read from a file in the standard libraries }}}

syn DefinitionItem ::=
  "require " String[value] "\n" [Require]
  // Should be: Import* Sentence*
| "module " Name[name] "\n" ModuleItem[items,list="\n"] "\nendmodule\n" [Module]
| "/*" LiterateCommentType[type, immutable] Any[value] "*/\n"
  [LiterateDefinitionComment, implements = LiterateComment]

doc Require {{{ A Require directive }}}
doc Require value {{{ The string argument to {@code require}, as written in the input file. }}}
doc Module {{{ A module. }}}

syn ModuleItem ::=
  "  imports " Name[name] [Import]
| "  /*" LiterateCommentType[type, immutable] Any[value] "*/"
  [LiterateModuleComment, implements = LiterateComment]
| Name[type] "[" Name[label] "]:" Any[content] [StringSentence]
| "  syntax priorities " PriorityBlockExtended[priorityBlocks, list = "\n> "] [PriorityExtended]
| "  syntax " Assoc[assoc] KLabelConstant[tags, list = " "] [PriorityExtendedAssoc] // rename tags to KLabels
| "  syntax restrictions " Sort[sort] Terminal[terminal] " -/- " Any[pattern] [Restrictions]
| "  syntax " Sort[sort] attrs " ::= " PriorityBlock[priorityBlocks, list="\n> ", optional="new ArrayList<PriorityBlock>()"] [Syntax]

doc Import {{{ An import directive }}}
doc StringSentence {{{ Used as a container for unparsed sentences like rule, context and configuration. }}}
doc PriorityExtended {{{ A priority declaration, {@code syntax priorities} <em>labels</em> {@code >} ... {@code >} <em>labels</em>.
 * @see PriorityBlockExtended
}}}
doc PriorityExtended priorityBlocks {{{ Highest priority block comes first }}}
doc PriorityExtendedAssoc {{{ An associativity declaration, one of {@code syntax left}, {@code syntax right}, or {@ code syntax non-assoc}. }}}
doc PriorityExtendedAssoc assoc {{{ "left", "right", "non-assoc" }}}
doc PriorityExtendedAssoc tags {{{ The labels getting an associativity. }}}
doc Syntax {{{ A syntax declaration.
 * Contains {@link Production}s, grouped into a list {@link PriorityBlock}
 * according to precedence marked by {@code >} in the declaration.
 }}}
doc Syntax sort {{{ The sort being declared. }}}

syn ASTNode ::=
  Assoc[assoc, optional="\"\""] ": " KLabelConstant[productions, list=" ", optional="new ArrayList<KLabelConstant>()"] [PriorityBlockExtended]
| Assoc[assoc, optional="\"\""] ": " Production[productions, list = "\n| ", optional="new ArrayList<Production>()"] [PriorityBlock]
| Name[sort, hidden] ProductionItem[items, list = " "]
  String[ownerModuleName, hidden, optional = "null"] [Production]
| "ProductionItem" [ProductionItem, abstract]

doc PriorityBlockExtended {{{ A group within a {@code syntax priorities} declaration. {@link #assoc} is currently unused.
 * @see PriorityExtended
 }}}
doc PriorityBlock {{{
 * A block of productions at the same priority within a syntax declaration.
 * @see Syntax
 }}}
doc PriorityBlock assoc {{{ "left", "right", or "non-assoc" if this group of productions had
 * an explicitly declared associativity, "" otherwise }}}
doc Production {{{ A production. Any explicit attributes on the production are stored in {@link ASTNode#attributes}. }}}

syn ProductionItem ::=
  String[terminal] [Terminal]
| Name[name] [Sort]
| ListType[listType, optional="*"] "{" String[sort] ",\" " String[separator] "}" [UserList]
| "Lexical" "{" String[lexicalRule] "}" String[follow, hidden] [Lexical]

doc Terminal {{{ A terminal in a {@link Production}. }}}
doc Sort {{{ A nonterminal in a {@link Production}. Also abused in some places as a sort identifier }}}
doc UserList {{{ A production item for a cons-list with separator, like List{UserSort,";"}. Must be the only item in a {@link Production}. }}}
doc Lexical {{{ A terminal in a {@link Production}. }}}

/*******************************
**** TERMS                  ****
*******************************/

syn ASTNode ::=
  "Term" String[sort] [Term, abstract]

syn Term ::=
  // BackendTerm.java:public class BackendTerm extends Term {
  // Bracket.java:public class Bracket extends Term {
  Cast
  // Cell.java:public class Cell extends Term {
  // FreezerHole.java:public class FreezerHole extends Term {
  // Freezer.java:public class Freezer extends Term {
| "HOLE" [Hole]
| Term[label] "(" Term[child] ")" [KApp]
  // KInjectedLabel.java:public class KInjectedLabel extends Term {
  KLabel
  ListTerminator
| "(" Term[left] "=>" Term[right] ")" [Rewrite]
  TermComment.java
  // TermCons.java:public class TermCons extends Term {
  Terminal
  Variable

  // BuiltinLookup.java:public abstract class BuiltinLookup extends Term {
  // CollectionItem.java:public abstract class CollectionItem extends Term {
  // Collection.java:public abstract class Collection extends Term {
  // DataStructureBuiltin.java:public abstract class DataStructureBuiltin extends Term {
  // ListUpdate.java:public class ListUpdate extends Term {
  // MapUpdate.java:public class MapUpdate extends Term {
  // SetUpdate.java:public class SetUpdate extends Term {

/*******************************
**** EXTRA CODE FOR CLASSES ****
*******************************/
code ModuleItem {{{
  public java.util.List<String> getLabels() { return null; }
// Comment
  public java.util.List<String> getKLabels() { return null; }
  public java.util.List<String> getAllSorts() { return null; }
}}}

//code Module {{{
//  public void appendModuleItem(ModuleItem item) {
//    this.items.add(item);
//  }
//    public List<String> getModuleKLabels() {
//        List<String> mkl = new LinkedList<String>();
//
//        for (ModuleItem mi : items) {
//            List<String> list = mi.getKLabels();
//            if (list != null)
//                mkl.addAll(list);
//        }
//
//        return mkl;
//    }
//
//    public java.util.Set<String> getAllSorts() {
//        java.util.Set<String> sorts = new HashSet<String>();
//
//        for (ModuleItem mi : items) {
//            List<String> list = mi.getAllSorts();
//            if (list != null)
//                sorts.addAll(list);
//        }
//
//        // Andrei S: bad, bad practice ...
//        // ... but it is 11:55pm and I do not see another way to get them
//        sorts.add("#Bool");
//        sorts.add('#Int');
//        sorts.add('#Float');
//        sorts.add('#String');
//        sorts.add('#Id');
//
//        return sorts;
//    }
//    public Module addModuleItems(List<ModuleItem> rules) {
//        Module result = new Module(this);
//        List<ModuleItem> items = new ArrayList<ModuleItem>(this.items);
//        items.addAll(rules);
//        result.setItems(items);
//        return result;
//    }
//
//    public void addSubsort(String sort, String subsort, Context context) {
//        this.addProduction(sort, new Sort(subsort));
//        context.addSubsort(sort, subsort);
//    }
//
//    public void addConstant(String ctSort, String ctName) {
//        this.addProduction(ctSort, new Terminal(ctName));
//    }
//
//    public void addConstant(Constant ct) {
//        this.addProduction(ct.getSort(), new Terminal(ct.getValue()));
//    }
//
//    public void addConstant(KLabelConstant kLabelConstant) {
//        this.addProduction(kLabelConstant.getSort(), new Terminal(kLabelConstant.getLabel()));
//    }
//
//    public void addProduction(String sort, ProductionItem prodItem) {
//        List<ProductionItem> prodItems = new LinkedList<ProductionItem>();
//        prodItems.add(prodItem);
//        this.addProduction(sort, new Production(new Sort(sort), prodItems));
//    }
//
//    public void addProduction(String sort, Production prod) {
//        List<PriorityBlock> pbs = new LinkedList<PriorityBlock>();
//        PriorityBlock pb = new PriorityBlock();
//        pbs.add(pb);
//
//        List<Production> prods = new LinkedList<Production>();
//        pb.setProductions(prods);
//
//        prods.add(prod);
//
//        this.items.add(new Syntax(new Sort(sort), pbs));
//    }
//
//    public List<Rule> getRules() {
//        List<Rule> list = new LinkedList<Rule>();
//        for (ModuleItem moduleItem : items) {
//            if (moduleItem instanceof Rule) {
//                list.add((Rule) moduleItem);
//            }
//        }
//
//        return list;
//    }
//
//    /**
//     * Returns a {@code Collection} of {@link Production} instances associated with the given sort.
//     */
//    public Collection<Production> getProductionsOf(String sort) {
//        Collection<Production> productions = new ArrayList<Production>();
//        for (ModuleItem item : items) {
//            if (!(item instanceof Syntax)) {
//                continue;
//            }
//            Syntax syntax = (Syntax) item;
//            if (!syntax.getSort().getName().equals(sort)) {
//                continue;
//            }
//            for (PriorityBlock priorityBlock : syntax.getPriorityBlocks()) {
//                productions.addAll(priorityBlock.getProductions());
//            }
//        }
//        return productions;
//    }
//}}}
//
//code LiterateModuleComment {{{
//    public LiterateModuleComment(LiterateDefinitionComment ldc) {
//        setFilename(ldc.getFilename());
//        setLocation(ldc.getLocation());
//        value = ldc.getValue();
//        type = ldc.getType();
//    }
//}}}
//
//code Syntax {{{
//
//    @Override
//    public List<String> getLabels() {
//        List<String> lbls = new LinkedList<String>();
//        for (PriorityBlock pb : priorityBlocks) {
//            for (Production prod : pb.getProductions()) {
//                lbls.add(prod.getLabel());
//            }
//        }
//        return lbls;
//    }
//
//    @Override
//    public List<String> getKLabels() {
//        List<String> lbls = new LinkedList<String>();
//        if (priorityBlocks == null)
//            return lbls;
//        for (PriorityBlock pb : priorityBlocks) {
//            for (Production prod : pb.getProductions()) {
//                if (MetaK.isComputationSort(prod.getSort()) || prod.getSort().equals(KSorts.KLABEL) && prod.isConstant())
//                    lbls.add(prod.getKLabel());
//            }
//        }
//        return lbls;
//    }
//
//    @Override
//    public List<String> getAllSorts() {
//        List<String> sorts = new ArrayList<String>();
//        sorts.add(sort.toString());
//        return sorts;
//    }
//}}}
//
//code Production {{{
//    /*
//     * Andrei S: It appears that the cons attribute is mandatory for all new production added during compilation, otherwise a null pointer exception can be thrown in one of the later compilation
//     * steps.
//     */
//
//    public static Production makeFunction(String funSort, String funName, String argSort, org.kframework.kil.loader.Context context) {
//        List<ProductionItem> prodItems = new ArrayList<ProductionItem>();
//        prodItems.add(new Terminal(funName));
//        prodItems.add(new Terminal("("));
//        prodItems.add(new Sort(argSort));
//        prodItems.add(new Terminal(")"));
//
//        Production funProd = new Production(new Sort(funSort), prodItems);
//        funProd.addAttribute(new Attribute("prefixlabel", funName));
//        if (MetaK.isComputationSort(funSort)) {
//            funProd.addAttribute(new Attribute("klabel", funName));
//            String consAttr = funSort + "1" + funName + "Syn";
//            funProd.addAttribute(new Attribute("cons", consAttr));
//            context.conses.put(consAttr, funProd);
//            context.putLabel(funProd, consAttr);
//        }
//
//        return funProd;
//    }
//
//    public boolean isListDecl() {
//        return items.size() == 1 && items.get(0).getType() == ProductionType.USERLIST;
//    }
//
//    public boolean isSubsort() {
//        return items.size() == 1 && items.get(0).getType() == ProductionType.SORT;
//    }
//
//    public boolean isLexical() {
//        return items.size() == 1 && items.get(0).getType() == ProductionType.LEXICAL;
//    }
//
//    public boolean isConstant() {
//        return items.size() == 1 && items.get(0).getType() == ProductionType.TERMINAL && (sort.startsWith("#") || sort.equals(KSorts.KLABEL));
//    }
//
//    public String getCons() {
//        return attributes.get("cons");
//    }
//
//    public String getLabel() {
//        String label = attributes.get("prefixlabel");
//        if (label == null) {
//            label = getPrefixLabel();
//            attributes.set("prefixlabel", label);
//        }
//        return label.replace(" ", "");
//    }
//
//    public String getKLabel() {
//        /*
//        assert MetaK.isComputationSort(sort) || sort.equals(KSorts.KLABEL) && isConstant():
//                sort + " ::= " + this + " -> " + getPrefixLabel();
//        */
//
//        String klabel = attributes.get("klabel");
//        if (klabel == null) {
//            if (sort.toString().equals(KSorts.KLABEL))
//                klabel = getPrefixLabel();
//            else
//                klabel = "'" + getPrefixLabel();
//            attributes.set("klabel", klabel);
//        }
//        return klabel.replace(" ", "");
//    }
//
//    private String getPrefixLabel() {
//        String label = "";
//        for (ProductionItem pi : items) {
//            switch (pi.getType()) {
//            case SORT:
//                label += "_";
//                break;
//            case TERMINAL:
//                label += ((Terminal) pi).getTerminal();
//                break;
//            case USERLIST:
//                label += "_" + ((UserList) pi).separator + "_";
//                break;
//            }
//        }
//        return label;
//    }
//
//    public java.util.List<ProductionItem> getItems() {
//        return items;
//    }
//
//    public void setItems(java.util.List<ProductionItem> items) {
//        this.items = items;
//    }
//
//    public int getArity() {
//        int arity = 0;
//        for (ProductionItem i : items) {
//            if (i.getType() == ProductionType.USERLIST)
//                arity += 2;
//            if (i.getType() == ProductionType.SORT)
//                arity++;
//        }
//        return arity;
//    }
//
//    public String getChildSort(int idx) {
//        int arity = -1;
//        if (items.get(0).getType() == ProductionType.USERLIST) {
//            if (idx == 0) {
//                return ((UserList) items.get(0)).getSort();
//            } else {
//                return this.getSort();
//            }
//        }
//        for (ProductionItem i : items) {
//            if (i.getType() != ProductionType.TERMINAL)
//                arity++;
//            if (arity == idx) {
//                return ((Sort) i).getName();
//            }
//        }
//        return null;
//    }
//
//    public boolean hasTerminalToRight(int idx) {
//        int arity = 0;
//        for (int i = 0; i < items.size(); i++) {
//            ProductionItem item = items.get(i);
//            if (item.getType() == ProductionType.USERLIST) {
//                if (idx == arity)
//                    return !((UserList) item).getSeparator().equals("");
//                if (idx == arity + 1)
//                    return false;
//                arity += 2;
//            } else if (item.getType() == ProductionType.SORT) {
//                if (idx == arity)
//                    return i != items.size() - 1 && items.get(i + 1).getType() == ProductionType.TERMINAL;
//                arity++;
//            }
//        }
//        throw new IllegalArgumentException("Index not found in production");
//    }
//
//    public boolean hasTerminalToLeft(int idx) {
//        int arity = 0;
//        for (int i = 0; i < items.size(); i++) {
//            ProductionItem item = items.get(i);
//            if (item.getType() == ProductionType.USERLIST) {
//                if (idx == arity)
//                    return false;
//                if (idx == arity + 1)
//                    return !((UserList) item).getSeparator().equals("");
//                arity += 2;
//            } else if (item.getType() == ProductionType.SORT) {
//                if (idx == arity)
//                    return i != 0 && items.get(i - 1).getType() == ProductionType.TERMINAL;
//                arity++;
//            }
//        }
//        throw new IllegalArgumentException("Index not found in production");
//    }
//
//}}}
//
//code ProductionItem {{{
//    public enum ProductionType {
//        TERMINAL, SORT, USERLIST, LEXICAL
//    }
//
//    public abstract ProductionType getType();
//}}}
//
//code Sort {{{
//
//    public static final String BOOL = "Bool";
//
//    private String name;
//    private static Set<String> baseSorts = new HashSet<String>();
//    static {
//        baseSorts.add("K");
//        baseSorts.add("KResult");
//        baseSorts.add(KSorts.KITEM);
//        baseSorts.add(KSorts.KLIST);
//        baseSorts.add("Map");
//        baseSorts.add("MapItem");
//        baseSorts.add("List");
//        baseSorts.add("ListItem");
//        baseSorts.add("Set");
//        baseSorts.add("SetItem");
//        baseSorts.add("Bag");
//        baseSorts.add("BagItem");
//        baseSorts.add(KSorts.KLABEL);
//        baseSorts.add("CellLabel");
//    }
//
//    public static boolean isBasesort(String sort) {
//        return baseSorts.contains(sort);
//    }
//
//    public static Set<String> getBaseSorts() {
//        return new HashSet<String>(baseSorts);
//    }
//
//    public boolean isBaseSort() {
//        return Sort.isBasesort(getName());
//    }
//
// // TODO: what is this?
//    public String getName() {
//        if (MetaK.isCellSort(name))
//            return KSort.Bag.name();
//        return name;
//    }
//
//    public String getRealName() {
//        return name;
//    }
//
//}}}
