package org.kframework.backend.maude;

import org.kframework.backend.BackendFilter;
import org.kframework.compile.transformers.AddPredicates;
import org.kframework.compile.utils.ConfigurationStructure;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Collection;
import org.kframework.kil.loader.Context;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import com.google.common.collect.ImmutableSet;

import java.util.*;
import java.util.Map;
import java.util.Set;

public class MaudeFilter extends BackendFilter {
    private boolean firstAttribute;
    ConfigurationStructureMap cfgStr;
    private Set<String> unusedTransitions;

    public MaudeFilter(Context context) {
        super(context);
        unusedTransitions = new HashSet<>(options.transition.size());
        this.cfgStr = context.getConfigurationStructureMap();
    }

    @Override
    public void visit(Definition definition) {
        unusedTransitions.addAll(options.transition);
        if (unusedTransitions.contains(KompileOptions.DEFAULT_TRANSITION)) {
            unusedTransitions.remove(KompileOptions.DEFAULT_TRANSITION);
        }
        // TODO: remove hack for token membership predicates

        for (DefinitionItem di : definition.getItems()) {
            di.accept(this);
            result.append(" \n");
        }
        if (!(unusedTransitions.isEmpty())) {
            GlobalSettings.kem
                    .register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER,
                            "These specified transition tags were not used (mispelled?):\n\t\t" + unusedTransitions,
                            "command line arguments", "--transition"));
        }
    }

    @Override
    public void visit(Import imp) {
        result.append("including ");
        String name = imp.getName();
        final String iface = "-INTERFACE";
        if (name.startsWith("#") && name.endsWith(iface)) {
            name = name.substring(0, name.length() - iface.length());
        }
        result.append(name);
        result.append(" .");
    }

    @Override
    public void visit(Module mod) {
          result.append("mod ");
          result.append(mod.getName());
          result.append(" is\n");

          // TODO(AndreiS): move declaration of #token in a .maude file
          result.append("op #token : #String #String -> KLabel .\n");

          for (ModuleItem mi : mod.getItems()) {
            mi.accept(this);
            result.append("\n");
          }

          // TODO(AndreiS): move this in a more approprite place
          for (String sort : context.getTokenSorts()) {
            String tokenKItem = "_`(_`)(#token(\"" + sort + "\", V:" + StringBuiltin.SORT_NAME
              + "), .KList)";
            String sortKItem = "_`(_`)(#_(\"" + sort + "\")" + ", .KList)";
            String valueKItem = "_`(_`)(#_(V:" + StringBuiltin.SORT_NAME + ")" + ", .KList)";
            result.append("eq _`(_`)(" + AddPredicates.syntaxPredicate(sort) + ", "
                          + tokenKItem + ") = _`(_`)(#_(true), .KList) .\n");
            result.append("eq _`(_`)(#parseToken, _`,`,_(" + sortKItem + ", " + valueKItem
                          + ")) = " + tokenKItem + " .\n");
            result.append("eq _`(_`)(#tokenToString, " + tokenKItem + ") = " + valueKItem
                          + " .\n");
          }

          for (Map.Entry<String, DataStructureSort> entry : context.getDataStructureSorts().entrySet()) {
            String lhs = "_`(_`)(" + AddPredicates.syntaxPredicate(entry.getKey()) + ", "
              + "_`(_`)(" + entry.getValue().type() + "2KLabel_(V:"
              + entry.getValue().type() + "), .KList))";
            result.append("eq " + lhs + "  = _`(_`)(#_(true), .KList) .\n");
          }

          result.append("\nendm");
    }

    @Override
    public void visit(PriorityExtended syn) {
    }

    @Override
    public void visit(Syntax syn) {
        for (PriorityBlock pb : syn.getPriorityBlocks()) {
            for (Production p : pb.getProductions()) {
                if (p.getItems().size() == 1 && (p.getItems().get(0) instanceof Sort)) {
                    // sub-sort case
                    ProductionItem item = p.getItems().get(0);
                    if (item instanceof Sort) {
                        if (!MaudeHelper.declaredSorts.contains(p.getItems().get(0).toString()) && !MaudeHelper.basicSorts.contains(p.getItems().get(0).toString())) {
                            result.append("sort ");
                            result.append(p.getItems().get(0));
                            result.append(" .\n");
                            MaudeHelper.declaredSorts.add(p.getItems().get(0).toString());
                        }
                        result.append("subsort ");
                        result.append(p.getItems().get(0));
                        result.append(" < ");
                        result.append(syn.getSort());
                        result.append(" .\n");
                    }
                } else if (p.getItems().size() == 1 && (p.getItems().get(0) instanceof Terminal)) {
                    String operation = p.toString();
                    if (operation.startsWith("\"")) {
                        operation = operation.substring(1, operation.length() - 2);
                    }
                    if (operation.equals("") && !p.containsAttribute("onlyLabel")) {
                        String msg = "Cannot declare empty terminals in the definition.\n";
                        msg += "            Use attribute 'onlyLabel' paired with 'klabel(...)' to limit the use to programs.";
                        GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, p.getFilename(), p.getLocation()));
                    }
                    if (!MaudeHelper.constantSorts.contains(syn.getSort()) || !syn.getSort().toString().equals(KSorts.KLABEL) || !syn.getSort().toString().equals("CellLabel")) {
                        result.append("op ");
                        result.append(StringUtil.escapeMaude(operation));
                        result.append(" : -> ");
                        result.append(syn.getSort());
                        if (!isEmptyAttributes(p.getAttributes())) {
                            result.append(" [metadata \"");
                            p.getAttributes().accept(this);
                            result.append("\"]");
                        }
                        result.append(" .\n");
                    }
                    // ignore K constants declarations
                } else if (p.getItems().size() == 1 && (p.getItems().get(0) instanceof UserList)) {
                    // user declared lists case
                    UserList list = (UserList) p.getItems().get(0);
                    if (!MaudeHelper.separators.contains(list.getSeparator())) {
                        result.append("op _");
                        result.append(StringUtil.escapeMaude(list.getSeparator()));
                        result.append("_ : K K -> K [prec 120 metadata \"");
                        p.getAttributes().accept(this);
                        result.append(" hybrid=()");
                        result.append("\"] .\n");
                        result.append("op .List`{\"");
                        result.append(list.getSeparator());
                        result.append("\"`} : -> K .\n");
                        MaudeHelper.separators.add(list.getSeparator());
                    }
                } else {
                    String maudelabel = p.getLabel();
                    if (maudelabel.equals("")) {
                        String msg = "Empty production. Please use `prefixlabel` attribute.";
                        GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER, msg, p.getFilename(), p.getLocation()));
                        continue;
                    }

                    if (!p.containsAttribute("bracket")) {
                        result.append("op ");
                        result.append(StringUtil.escapeMaude(maudelabel));
                        result.append(" : ");
                        p.accept(this);
                        result.append(" -> ");
                        result.append(syn.getSort());
                        // if (!isEmptyAttributes(p.getCellAttributes())) {
                        result.append(" [metadata \"");
                        p.getAttributes().accept(this);
                        result.append("\"]");
                        // }
                        result.append(" .\n");
                    }
                }
            }
        }
    }

    @Override
    public void visit(PriorityExtendedAssoc priorityBlock) {
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {
        result.append("production");
    }

    @Override
    public void visit(Production prod) {
        boolean first = true;
        for (ProductionItem pi : prod.getItems()) {
            if (!first) {
                result.append(" ");
            } else {
                first = false;
            }
            if (pi instanceof Sort) {
                pi.accept(this);
            }
        }
    }

    @Override
    public void visit(Sort sort) {
        result.append(sort.getName());
    }

    @Override
    public void visit(Terminal terminal) {
        // do nothing
    }

    @Override
    public void visit(StringSentence stringSentence) {
        result.append("StringSentence should not be maudifiable");
    }

    @Override
    public void visit(UserList userList) {
        // do nothing
    }

    @Override
    public void visit(KList listOfK) {
        this.visit((Collection) listOfK);
        // throw new RuntimeException("don't know how to maudify KList");
    }

    @Override
    public void visit(Attributes attributes) {
        firstAttribute = true;
        for (Attribute entry : attributes.getContents()) {
            if (!entry.getKey().equals("klabel")) {
                entry.accept(this);
            }
        }
    }

    private boolean isEmptyAttributes(Attributes attributes) {
        for (Attribute entry : attributes.getContents()) {
            if (!entry.getKey().equals("klabel") && !entry.getKey().equals("location") && !entry.getKey().equals("filename")) {
                if (!isEmptyAttribute(entry)) {
                    return false;
                }
            }
        }
        return true;
    }

    private boolean isEmptyAttribute(Attribute entry) {
        java.util.List<String> reject = new LinkedList<String>();
        reject.add("cons");
        reject.add("kgeneratedlabel");
        reject.add("latex");
        reject.add("prefixlabel");

        if (!reject.contains(entry.getKey())) {
            return false;
        }
        return true;
    }

    @Override
    public void visit(Attribute attribute) {
        java.util.List<String> reject = new LinkedList<String>();
        reject.add("cons");
        reject.add("kgeneratedlabel");
        reject.add("latex");
        reject.add("prefixlabel");

        if (!reject.contains(attribute.getKey())) {
            if (!firstAttribute) {
                result.append(" ");
            } else {
                firstAttribute = false;
            }
            result.append(attribute.getKey());
            result.append("=(");
            result.append(attribute.getValue().replaceAll("[()]", ""));
            result.append(")");
        }
    }

    /**
     * Pretty printing configuration-related stuff to Maude.
     *
     * This visitor is abused here for declaring the operations corresponding
     * to each sorted cell as concrete operations.
     *
     * @param configuration
     */
    @Override
    public void visit(Configuration configuration) {
        if (cfgStr == null) return;
        for (ConfigurationStructure cellStr : cfgStr.values()) {
            String id = cellStr.id;
            if (id == MetaK.Constants.generatedCfgAbsTopCellLabel) continue;
            String cellSort = MetaK.cellSort(id);
            String cellFragment = MetaK.cellFragment(id);
            String cellUnit = MetaK.cellUnit(id);
            if (!cellStr.id.equals("k")) {
                result.append("  sort " + cellSort +  " .\n");
            }
            result.append("  sort " + cellFragment + " .\n");
            result.append("  subsort " + cellSort + " < " + cellFragment + " .\n");
            result.append("  op " + cellUnit + " : -> " + cellFragment + " .\n");
            if (cellStr.isStarOrPlus()) {
                result.append(" op __ : " + cellFragment + " " + cellFragment + " -> " + cellFragment + " " +
                        "[assoc comm id: " + cellUnit + "] .\n");
            }
            result.append("  op " + cellFragment + "2KLabel_ : " + cellFragment + " -> KLabel .\n");
            result.append("  op " + cellSort + "2KLabel_ : " + cellFragment + " -> KLabel .\n");

            String placeHolders = "";
            String sorts = "";
            String fragSorts = "";
            String format = "";
            Cell cell = cellStr.cell;
            if (cellStr.sons.isEmpty()) {
                if (!cellStr.id.equals("k")) {
                    placeHolders="_";
                    format = "ni ";
                    sorts = KSort.getKSort(cell.getContents().getSort()).mainSort()
                            .toString();
                    declareCell(id,placeHolders, sorts, cellSort, format);
                }
                continue;
            }

            java.util.List<Term> cfgCells = cell.getCellTerms();
            for (Term cCell : cfgCells) {
                if (cCell instanceof TermComment) continue;
                placeHolders += "_";
                format += "ni ";
                // Decided to declare all sorts as Bags to allow using
                // cells instead of tuples for tupling purposes.

                String cellName = ((Cell) cCell).getId();
                switch(((Cell) cCell).getMultiplicity()) {
                    case ONE:
                        sorts += MetaK.cellSort(cellName);
                        break;
                    default:
                        sorts += MetaK.cellFragment(cellName);
                }
                fragSorts += MetaK.cellFragment(cellName) + " ";
                sorts += " ";
            }
            declareCell(id, placeHolders, sorts, cellSort, format);
            declareCell(id+"-fragment",placeHolders,fragSorts, cellFragment, format);
        }

        // result.append("mb configuration ");
        // this.visit((Sentence)configuration);
    }

    private void declareCell(String id, String placeHolders, String sorts, String resultSort, String format) {
        result.append(
                "  op " +
                        "<" + id + ">" +
                        placeHolders +
                        "</" + id + ">" +
                        " : " +
                        sorts +
                        " -> " +
                        resultSort +
                        "[format(b o++" + format + "--nib o)]" +
                        "." +
                        "\n");
    }

    /**
     * Pretty printing a cell to Maude
     *
     * The code was changed for pretty printing sorted cells which are now
     * operations on their own.
     * @param cell
     */
    @Override
    public void visit(Cell cell) {
        String id = cell.getId();
        result.append("<_>_</_>(" + id + ", ");
        if (cell.getContents() != null) {
            cell.getContents().accept(this);
        } else {
            result.append("null");
        }
        result.append(", " + id + ")");
    }

    @Override
    public void visit(Variable variable) {
        if (MetaK.isBuiltinSort(variable.getSort())
                || context.getDataStructureSorts().containsKey(variable.getSort())) {
            result.append("_`(_`)(");
            if (context.getDataStructureSorts().containsKey(variable.getSort())) {
                  String sort = context.dataStructureSortOf(variable.getSort()).type();
                  sort = sort.equals("K") ? "KList" : sort;
                result.append(sort + "2KLabel_(");
            } else {
                result.append("#_(");
            }
        }

        if (variable.getName().equals(MetaK.Constants.anyVarSymbol)) {
            result.append("?");
        } else {
            result.append(variable.getName());
        }
        result.append(":");
        if (context.getDataStructureSorts().containsKey(variable.getSort())) {
            result.append(context.dataStructureSortOf(variable.getSort()).type());
        } else {
            result.append(variable.getSort());
        }

        if (MetaK.isBuiltinSort(variable.getSort())
                || context.getDataStructureSorts().containsKey(variable.getSort())) {
            result.append(")");
            result.append(", ");
            result.append(".KList");
            result.append(") ");
        }
    }

    @Override
    public void visit(ListTerminator empty) {
        String sort = empty.getSort();
        if (MaudeHelper.basicSorts.contains(sort) || MetaK.isCellFragment(sort)) {
            result.append(".");
            result.append(sort);
        } else {
            Production prd = context.listConses.get(sort);
            UserList ul = (UserList) prd.getItems().get(0);
            result.append(".List`{\"");
            result.append(ul.getSeparator());
            result.append("\"`}");
        }
    }

    @Override
    public void visit(Rule rule) {
        boolean isTransition = false;
        for (Attribute a : rule.getAttributes().getContents()) {
            if (options.transition.contains(a.getKey())) {
                isTransition = true;
                unusedTransitions.remove(a.getKey());
                break;
            }
        }
        if (rule.getAttributes().containsKey("heat-choice")) {
            isTransition = true;
        }
        if (!(rule.getBody() instanceof Rewrite)) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "This rule should have a rewrite at top by now.", getName(), rule.getFilename(), rule
                    .getLocation()));
        }
        Rewrite body = (Rewrite) rule.getBody();
        assert rule.getEnsures() == null : "Maude does not support conditions on the right hand side";
        final Term condition = rule.getRequires();
        if (null != condition) {
            result.append("c");
        }
        if (isTransition) {
            result.append("rl ");
        } else {
            result.append("eq ");
        }
        body.getLeft().accept(this);
        if (isTransition) {
            result.append(" => ");
        } else {
            result.append(" = ");
        }
        body.getRight().accept(this);

        if (null != condition) {
            result.append(" if ");
            condition.accept(this);
            result.append(" = _`(_`)(# true, .KList)");
        }
        if (null != rule.getAttributes()) {
            result.append(" [");
            if (!isTransition && rule.getAttributes().containsKey("owise"))
                result.append("owise ");
            if (rule.getLabel() != null && !rule.getLabel().equals("")) {
                result.append("label " + rule.getLabel() + " metadata");
            } else {
                result.append("metadata");
            }
            result.append(" \"");
            rule.getAttributes().accept(this);
            result.append("\"] .\n");
        }
    }

    @Override
    public void visit(KApp kapp) {
        result.append("_`(_`)(");
        kapp.getLabel().accept(this);
        result.append(", ");
        kapp.getChild().accept(this);
        result.append(")");
    }

    @Override
    public void visit(KSequence ksequence) {
        this.visit((Collection) ksequence);
        // throw new RuntimeException("don't know how to maudify KSequence");
    }

    @Override
    public void visit(TermCons termCons) {
        Production pr = context.conses.get(termCons.getCons());
        String cons = StringUtil.escapeMaude(pr.getLabel());

        if (pr.containsAttribute("maudeop")) {
            cons = pr.getAttribute("maudeop").replaceAll("\"", "").replaceAll(" ", "`");
        }

        result.append(cons);
        if (termCons.getContents().size() > 0) {
            result.append("(");
        }
        boolean first = true;
        for (Term term : termCons.getContents()) {
            if (!first) {
                result.append(",");
            } else {
                first = false;
            }
            if (term != null) {
                term.accept(this);
            } else {
                result.append("null");
            }
        }
        if (termCons.getContents().size() > 0) {
            result.append(")");
        }
    }

    @Override
    public void visit(Sentence sentence) {
        sentence.getBody().accept(this);
        result.append(" ");
        if (sentence.getRequires() != null) {
            result.append("when ");
            sentence.getRequires().accept(this);
        }
        assert sentence.getEnsures() == null : "Maude does not support conditions on the right hand side";

        result.append(" : KSentence [");
        if (sentence instanceof Rule) {
            Rule rule = (Rule) sentence;
            if (rule.getLabel() != null && !rule.getLabel().equals("")) {
                result.append("label " + rule.getLabel() + " metadata");
            } else {
                result.append("metadata");
            }
        } else {
            result.append("metadata");
        }
        result.append(" \"");
        sentence.getAttributes().accept(this);
        result.append("\"] .");
    }

    @Override
    public void visit(Rewrite rewrite) {
        result.append("_=>_(");
        if (rewrite.getLeft() == null) {
            result.append("null");
        } else {
            rewrite.getLeft().accept(this);
        }
        result.append(",");
        if (rewrite.getRight() == null) {
            result.append("null");
        } else {
            rewrite.getRight().accept(this);
        }
        result.append(")");

    }

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        result.append(StringUtil.escapeMaude(kLabelConstant.getLabel()));
    }

    private java.util.Set<String> maudeBuiltinTokenSorts =
        ImmutableSet.of("#Float", "#LtlFormula");

    @Override
    public void visit(GenericToken token) {
        if (maudeBuiltinTokenSorts.contains(token.tokenSort())) {
            result.append("#_(" + token.value() + ")");
        } else {
            result.append(token);
        }
    }

    @Override
    public void visit(StringBuiltin token) {
        result.append("#_(\"" + StringUtil.escape(token.stringValue()) + "\")");
    }

    @Override
    public void visit(Token token) {
        result.append("#_(" + token.value() + ")");
    }

    @Override
    public void visit(Collection collection) {
        if (collection.getContents().size() == 0) {
            new ListTerminator(collection.getSort(), null).accept(this);
        } else if (collection.getContents().size() == 1) {
            collection.getContents().get(0).accept(this);
        } else {
            String constructor = getMaudeConstructor(collection.getSort());
            result.append(constructor);
            result.append("(");

            boolean first = true;
            for (Term term : collection.getContents()) {
                if (!first) {
                    result.append(", ");
                } else {
                    first = false;
                }
                if (term == null) {
                    GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.INTERNAL, "NULL Term encountered when MaudeFilter ran on collection " + collection.getContents()
                            + ".", collection.getFilename(), collection.getLocation()));
                }
                term.accept(this);
            }

            result.append(")");
        }
    }

    @Override
    public void visit(CollectionItem collectionItem) {
        throw new RuntimeException("don't know how to maudify CollectionItem");
    }

    @Override
    public void visit(BagItem bagItem) {
        result.append("BagItem(");
        bagItem.getItem().accept(this);
        result.append(")");
    }

    @Override
    public void visit(ListItem listItem) {
        result.append("ListItem(");
        listItem.getItem().accept(this);
        result.append(")");
    }

    @Override
    public void visit(SetItem setItem) {
        result.append("SetItem(");
        setItem.getItem().accept(this);
        result.append(")");
    }

    @Override
    public void visit(MapItem mapItem) {
        result.append("_|->_(");
        mapItem.getKey().accept(this);
        result.append(",");
        mapItem.getValue().accept(this);
        result.append(")");
    }

    @Override
    public void visit(DataStructureBuiltin dataStructure) {
        result.append("_`(_`)(" + dataStructure.sort().type() + "2KLabel_(");

        if (!dataStructure.isEmpty()) {
            result.append(DataStructureSort.LABELS.get(dataStructure.sort().type()).get(
                    DataStructureSort.Label.CONSTRUCTOR));
            result.append("(");

            result.append(DataStructureSort.LABELS.get(dataStructure.sort().type()).get(
                    DataStructureSort.Label.UNIT));
            if (dataStructure instanceof ListBuiltin) {
                visitListBuiltinElements((ListBuiltin) dataStructure);
            } else if (dataStructure instanceof CollectionBuiltin) {
                visitCollectionElements((CollectionBuiltin) dataStructure);
            } else {
                assert dataStructure instanceof MapBuiltin;

                visitMapElements((MapBuiltin) dataStructure);
            }

            if (dataStructure.isLHSView() && dataStructure.hasViewBase() && !(dataStructure instanceof ListBuiltin)) {
                result.append(", ");
                Variable variable = new Variable(
                        dataStructure.viewBase().getName(),
                        dataStructure.sort().type());
                variable.accept(this);
            }

            result.append(")");
        } else {
            result.append(DataStructureSort.LABELS.get(dataStructure.sort().type()).get(
                    DataStructureSort.Label.UNIT));
        }

        result.append("), .KList)");
    }

    private void visitCollectionElements(CollectionBuiltin collection) {
        for (Term term : collection.elements()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(collection.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            term.accept(this);
            result.append(")");
        }
    }

    public void visitListBuiltinElements(ListBuiltin listBuiltin) {
        // append lhs elements
        for (Term term : listBuiltin.elementsLeft()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(listBuiltin.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            term.accept(this);
            result.append(")");
        }

        // append base elements
        for (Term term : listBuiltin.baseTerms()) {
            result.append(", ");
            if (term instanceof  Variable) {
                Variable variable = new Variable(
                        listBuiltin.viewBase().getName(),
                        listBuiltin.sort().type());
                variable.accept(this);
            } else {
                result.append(DataStructureSort.LABELS.get(listBuiltin.sort().type()).get(
                        DataStructureSort.Label.ELEMENT));
                result.append("(");
                    term.accept(this);
                    result.append(")");
            }
        }

        // append rhs elements
        for (Term term : listBuiltin.elementsRight()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(listBuiltin.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            term.accept(this);
            result.append(")");
        }
    }

    private void visitMapElements(MapBuiltin map) {
        for (Map.Entry<Term, Term> entry : map.elements().entrySet()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(map.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            entry.getKey().accept(this);
            result.append(", ");
            entry.getValue().accept(this);
            result.append(")");
        }
    }

    @Override
    public void visit(CollectionBuiltin collection) {
        visit((DataStructureBuiltin) collection);
    }

    @Override
    public void visit(MapBuiltin map) {
        visit((DataStructureBuiltin) map);
    }


    @Override
    public void visit(Hole hole) {
        result.append("HOLE");
    }

    @Override
    public void visit(FreezerHole hole) {
        result.append("HOLE");
    }

    @Override
    public void visit(KInjectedLabel kInjectedLabel) {
        Term term = kInjectedLabel.getTerm();
        String sort = term.getSort().equals("K") ? "KList" : term.getSort();
        if (MetaK.isKSort(sort)) {
            //result.append(StringUtil.escapeMaude(kInjectedLabel.getInjectedSort(term.getSort())));
            result.append(kInjectedLabel.getInjectedSort(sort));
            result.append("2KLabel_(");
        } else if (MetaK.isCellSort(sort)){
            result.append(sort + "2KLabel_(");

        } else {
            result.append("#_(");
        }
        term.accept(this);
        result.append(")");
    }

    @Override
    public void visit(FreezerLabel freezerLabel) {
        Term term = freezerLabel.getTerm();
        result.append("#freezer_(");
        term.accept(this);
        result.append(")");
    }

    @Override
    public void visit(Freezer freezer) {
        freezer.getTerm().accept(this);
    }

    @Override
    public void visit(KLabel kLabel) {
        throw new RuntimeException("don't know how to maudify KLabel of type" + kLabel.getClass());
    }

    @Override
    public void visit(TermComment termComment) {
        result.append(" .Bag ");
    }

    @Override
    public void visit(org.kframework.kil.List list) {
        this.visit((Collection) list);
        // throw new RuntimeException("don't know how to maudify List");
    }

    @Override
    public void visit(org.kframework.kil.Map map) {
        this.visit((Collection) map);
        // throw new RuntimeException("don't know how to maudify Map");
    }

    /**
     * Pretty printing a Bag to Maude.
     *
     * The code is slightly altered to also work with printing cell contents
     * when cells are sorted
     * @param bag
     */
    @Override
    public void visit(Bag bag) {
        if (bag.getContents().isEmpty()) {
            new ListTerminator(KSorts.BAG, null).accept(this);
            return;
        }
        for (Term item: bag.getContents()) {
            if (item instanceof TermComment) continue;
            result.append("(");
            item.accept(this);
            result.append(")");
            result.append(" ");
        }
//        this.visit((Collection) bag);
        // throw new RuntimeException("don't know how to maudify Bag");
    }

    @Override
    public void visit(org.kframework.kil.Set set) {
        this.visit((Collection) set);
        // throw new RuntimeException("don't know how to maudify Set");
    }

    @Override
    public void visit(org.kframework.kil.Ambiguity ambiguity) {
        result.append("amb(");
        boolean first = true;
        for (Term term : ambiguity.getContents()) {
            if (!first) {
                result.append(",");
            } else {
                first = false;
            }
            if (term != null) {
                term.accept(this);
            } else {
                result.append("null");
            }
        }
        result.append(")");
    }

    @Override
    public void visit(org.kframework.kil.Context context) {
        result.append("mb context ");
        this.visit((Sentence) context);
        result.append("\n");
    }

    @Override
    public void visit(LiterateDefinitionComment literateDefinitionComment) {
        // do nothing
    }

    @Override
    public void visit(LiterateModuleComment literateModuleComment) {
        // do nothing
    }

    @Override
    public void visit(org.kframework.kil.Require require) {
        // do nothing
    }

    @Override
    public void visit(BackendTerm term) {
        result.append(term.getValue());
    }

    @Override
    public void visit(Bracket term) {
        term.getContent().accept(this);
    }

    @Override
    public void visit(Cast term) {
        throw new RuntimeException("don't know how to maudify Cast at "+term.getFilename()+" "+term.getLocation());
    }

    @Override
    public void visit(MapUpdate term) {
        result.append("_`(_`)(Map2KLabel(");
        result.append("update(");
        result.append("remove(");
        result.append(term.map().getName() + ":Map , (.Map ");
        for (java.util.Map.Entry<Term, Term> t : term.removeEntries().entrySet()) {
            t.getKey().accept(this);
            result.append(" |-> ");
            t.getValue().accept(this);
            result.append(" ");
        }
        result.append(")), ");

        result.append("(.Map ");
        for (java.util.Map.Entry<Term, Term> t : term.updateEntries().entrySet()) {
            t.getKey().accept(this);
            result.append(" |-> ");
            t.getValue().accept(this);
            result.append(" ");
        }
        result.append("))");
        result.append(") , .KList)");
    }

    private static java.util.Map<KSort, String> maudeCollectionConstructors = new HashMap<KSort, String>();
    static {
        maudeCollectionConstructors.put(KSort.Bag, "__");
        maudeCollectionConstructors.put(KSort.Map, "__");
        maudeCollectionConstructors.put(KSort.Set, "__");
        maudeCollectionConstructors.put(KSort.List, "__");
        maudeCollectionConstructors.put(KSort.K, "_~>_");
        maudeCollectionConstructors.put(KSort.KList, "_`,`,_");
    }

    public static String getMaudeConstructor(String sort) {
        return maudeCollectionConstructors.get(KSort.getKSort(sort));
    }
}
