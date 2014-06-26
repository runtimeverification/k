// Copyright (c) 2012-2014 K Team. All Rights Reserved.
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
    public Void visit(Definition definition, Void _) {
        unusedTransitions.addAll(options.transition);
        if (unusedTransitions.contains(KompileOptions.DEFAULT_TRANSITION)) {
            unusedTransitions.remove(KompileOptions.DEFAULT_TRANSITION);
        }
        // TODO: remove hack for token membership predicates

        for (DefinitionItem di : definition.getItems()) {
            this.visitNode(di);
            result.append(" \n");
        }
        if (!(unusedTransitions.isEmpty())) {
            GlobalSettings.kem
                    .register(new KException(ExceptionType.WARNING, KExceptionGroup.COMPILER,
                            "These specified transition tags were not used (mispelled?):\n\t\t" + unusedTransitions,
                            "command line arguments", "--transition"));
        }
        return null;
    }

    @Override
    public Void visit(Import imp, Void _) {
        result.append("including ");
        String name = imp.getName();
        final String iface = "-INTERFACE";
        if (name.startsWith("#") && name.endsWith(iface)) {
            name = name.substring(0, name.length() - iface.length());
        }
        result.append(name);
        result.append(" .");
        return null;
    }

    @Override
    public Void visit(Module mod, Void _) {
          result.append("mod ");
          result.append(mod.getName());
          result.append(" is\n");

        result.append(" op fresh : #String -> KItem . \n");
        for (Map.Entry<String, String> entry : context.freshFunctionNames.entrySet()) {
            result.append(" eq fresh(\"").append(entry.getKey()).append("\") = ");
            result.append(StringUtil.escapeMaude(entry.getValue()));
            result.append("('#counter(.KList)) .\n");
        }

          // TODO(AndreiS): move declaration of #token in a .maude file
          result.append("op #token : #String #String -> KLabel .\n");

          for (ModuleItem mi : mod.getItems()) {
            this.visitNode(mi);
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
          return null;
    }

    @Override
    public Void visit(PriorityExtended syn, Void _) {
        return null;
    }

    @Override
    public Void visit(Syntax syn, Void _) {
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
                            this.visitNode(p.getAttributes());
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
                        this.visitNode(p.getAttributes());
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
                        this.visitNode(p);
                        result.append(" -> ");
                        result.append(syn.getSort());
                        // if (!isEmptyAttributes(p.getCellAttributes())) {
                        result.append(" [metadata \"");
                        this.visitNode(p.getAttributes());
                        result.append("\"]");
                        // }
                        result.append(" .\n");
                    }
                }
            }
        }
        return null;
    }

    @Override
    public Void visit(PriorityExtendedAssoc priorityBlock, Void _) {
        return null;
    }

    @Override
    public Void visit(PriorityBlock priorityBlock, Void _) {
        result.append("production");
        return null;
    }

    @Override
    public Void visit(Production prod, Void _) {
        boolean first = true;
        for (ProductionItem pi : prod.getItems()) {
            if (!first) {
                result.append(" ");
            } else {
                first = false;
            }
            if (pi instanceof Sort) {
                this.visitNode(pi);
            }
        }
        return null;
    }

    @Override
    public Void visit(Sort sort, Void _) {
        result.append(sort.getName());
        return null;
    }

    @Override
    public Void visit(Terminal terminal, Void _) {
        // do nothing
        return null;
    }

    @Override
    public Void visit(StringSentence stringSentence, Void _) {
        result.append("StringSentence should not be maudifiable");
        return null;
    }

    @Override
    public Void visit(UserList userList, Void _) {
        // do nothing
        return null;
    }

    @Override
    public Void visit(KList listOfK, Void _) {
        this.visit((Collection) listOfK, _);
        // throw new RuntimeException("don't know how to maudify KList");
        return null;
    }

    @Override
    public Void visit(Attributes attributes, Void _) {
        firstAttribute = true;
        for (Attribute entry : attributes.getContents()) {
            if (!entry.getKey().equals("klabel")) {
                this.visitNode(entry);
            }
        }
        return null;
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
        reject.add("regex");

        if (!reject.contains(entry.getKey())) {
            return false;
        }
        return true;
    }

    @Override
    public Void visit(Attribute attribute, Void _) {
        java.util.List<String> reject = new LinkedList<String>();
        reject.add("cons");
        reject.add("kgeneratedlabel");
        reject.add("latex");
        reject.add("prefixlabel");
        reject.add("regex");

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
        return null;
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
    public Void visit(Configuration configuration, Void _) {
        if (cfgStr == null) return null;
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

        return null;
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
    public Void visit(Cell cell, Void _) {
        String id = cell.getId();
        result.append("<_>_</_>(" + id + ", ");
        if (cell.getContents() != null) {
            this.visitNode(cell.getContents());
        } else {
            result.append("null");
        }
        result.append(", " + id + ")");
        return null;
    }

    @Override
    public Void visit(Variable variable, Void _) {
        if (variable.isFreshConstant()) {
            variable = variable.shallowCopy();
            variable.setSort(KSorts.KITEM);
        }
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
        return null;
    }

    @Override
    public Void visit(ListTerminator empty, Void _) {
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
        return null;
    }

    @Override
    public Void visit(Rule rule, Void _) {
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

        boolean conditional = (null != condition);
        Set<Variable> variables = body.variables();
        for (Variable variable : variables) {
            if (variable.isFreshConstant()) {
                conditional = true;
                break;
            }
        }
        if (conditional) {
            result.append("c");
        }
        if (isTransition) {
            result.append("rl ");
        } else {
            result.append("eq ");
        }
        this.visitNode(body.getLeft());
        if (isTransition) {
            result.append(" => ");
        } else {
            result.append(" = ");
        }
        this.visitNode(body.getRight());

        boolean addAnd = false;
        if (conditional) {
            result.append(" if ");
            if (null != condition) {
                this.visitNode(condition);
                result.append(" = _`(_`)(# true, .KList)");
                addAnd = true;
            }
            for (Variable variable : variables) {
                if (variable.isFreshConstant()) {
                    if (addAnd) {
                        result.append(" /\\ ");
                    }
                    addAnd = true;
                    Variable kVariable = variable.shallowCopy();
                    kVariable.setSort(KSorts.KITEM);
                    this.visitNode(kVariable);
                    result.append(" := fresh(\"").append(variable.getSort()).append("\")");
                }
            }
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
            this.visitNode(rule.getAttributes());
            result.append("\"] .\n");
        }
        return null;
    }

    @Override
    public Void visit(KApp kapp, Void _) {
        result.append("_`(_`)(");
        this.visitNode(kapp.getLabel());
        result.append(", ");
        this.visitNode(kapp.getChild());
        result.append(")");
        return null;
    }

    @Override
    public Void visit(KSequence ksequence, Void _) {
        this.visit((Collection) ksequence, _);
        return null;
        // throw new RuntimeException("don't know how to maudify KSequence");
    }

    @Override
    public Void visit(TermCons termCons, Void _) {
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
                this.visitNode(term);
            } else {
                result.append("null");
            }
        }
        if (termCons.getContents().size() > 0) {
            result.append(")");
        }
        return null;
    }

    @Override
    public Void visit(Sentence sentence, Void _) {
        this.visitNode(sentence.getBody());
        result.append(" ");
        if (sentence.getRequires() != null) {
            result.append("when ");
            this.visitNode(sentence.getRequires());
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
        this.visitNode(sentence.getAttributes());
        result.append("\"] .");
        return null;
    }

    @Override
    public Void visit(Rewrite rewrite, Void _) {
        result.append("_=>_(");
        if (rewrite.getLeft() == null) {
            result.append("null");
        } else {
            this.visitNode(rewrite.getLeft());
        }
        result.append(",");
        if (rewrite.getRight() == null) {
            result.append("null");
        } else {
            this.visitNode(rewrite.getRight());
        }
        result.append(")");

        return null;
    }

    @Override
    public Void visit(KLabelConstant kLabelConstant, Void _) {
        result.append(StringUtil.escapeMaude(kLabelConstant.getLabel()));
        return null;
    }

    private java.util.Set<String> maudeBuiltinTokenSorts =
        ImmutableSet.of("#LtlFormula");

    @Override
    public Void visit(GenericToken token, Void _) {
        if (maudeBuiltinTokenSorts.contains(token.tokenSort())) {
            result.append("#_(" + token.value() + ")");
        } else {
            result.append(token);
        }
        return null;
    }
    
    boolean floatWarning = false;
    @Override
    public Void visit(FloatBuiltin token, Void _) {
        result.append("#_(");
        if (token.bigFloatValue().isNegativeZero() || token.bigFloatValue().isNaN()) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, 
                    "Attempting to compile a definition containing -0.0 or NaN with the Maude backend. "
                            + "Maude does not support these features, and floating point arithmetic is "
                            + "unsupported in the Maude backend. Please recompile with --backend java."));
        }
        result.append(FloatBuiltin.printKFloat(token.bigFloatValue()));
        result.append(")");
        if (!floatWarning) {
            GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.INTERNAL, 
                    "The Maude backend does not officially support floating point numbers. The results of "
                    + "this semantics may be undefined or, in some cases, "
                    + "incorrect."));
            floatWarning = true;
        }
        return null;
    }
    
    @Override
    public Void visit(StringBuiltin token, Void _) {
        result.append("#_(\"" + StringUtil.escape(token.stringValue()) + "\")");
        return null;
    }

    @Override
    public Void visit(Token token, Void _) {
        result.append("#_(" + token.value() + ")");
        return null;
    }

    @Override
    public Void visit(Collection collection, Void _) {
        if (collection.getContents().size() == 0) {
            this.visitNode(new ListTerminator(collection.getSort(), null));
        } else if (collection.getContents().size() == 1) {
            this.visitNode(collection.getContents().get(0));
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
                this.visitNode(term);
            }

            result.append(")");
        }
        return null;
    }

    @Override
    public Void visit(CollectionItem collectionItem, Void _) {
        throw new RuntimeException("don't know how to maudify CollectionItem");
    }

    @Override
    public Void visit(BagItem bagItem, Void _) {
        result.append("BagItem(");
        this.visitNode(bagItem.getItem());
        result.append(")");
        return null;
    }

    @Override
    public Void visit(DataStructureBuiltin dataStructure, Void _) {
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

            if (!(dataStructure instanceof ListBuiltin)) {
                visitDataStructureBaseTerms(dataStructure);
            }

            result.append(")");
        } else {
            result.append(DataStructureSort.LABELS.get(dataStructure.sort().type()).get(
                    DataStructureSort.Label.UNIT));
        }

        result.append("), .KList)");
        return null;
    }

    private void visitDataStructureVariable(String varName, String varType) {
        result.append(varName);
        result.append(":");
        result.append(varType);
    }

    private void visitCollectionElements(CollectionBuiltin collection) {
        for (Term term : collection.elements()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(collection.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            this.visitNode(term);
            result.append(")");
        }
    }

    public Void visitListBuiltinElements(ListBuiltin listBuiltin) {
        // append lhs elements
        for (Term term : listBuiltin.elementsLeft()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(listBuiltin.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            this.visitNode(term);
            result.append(")");
        }

        visitDataStructureBaseTerms(listBuiltin);

        // append rhs elements
        for (Term term : listBuiltin.elementsRight()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(listBuiltin.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            this.visitNode(term);
            result.append(")");
        }
        return null;
    }

    private void visitDataStructureBaseTerms(DataStructureBuiltin listBuiltin) {
        // append base elements
        for (Term term : listBuiltin.baseTerms()) {
            result.append(", ");
            if (term instanceof Variable) {
                visitDataStructureVariable(
                        ((Variable)term).getName(),
                        listBuiltin.sort().type());
            } else {
                result.append("K2" + listBuiltin.sort().type());
                result.append("(");
                    this.visitNode(term);
                    result.append(")");
            }
        }
    }

    private void visitMapElements(MapBuiltin map) {
        for (Map.Entry<Term, Term> entry : map.elements().entrySet()) {
            result.append(", ");
            result.append(DataStructureSort.LABELS.get(map.sort().type()).get(
                    DataStructureSort.Label.ELEMENT));
            result.append("(");
            this.visitNode(entry.getKey());
            result.append(", ");
            this.visitNode(entry.getValue());
            result.append(")");
        }
    }

    @Override
    public Void visit(CollectionBuiltin collection, Void _) {
        visit((DataStructureBuiltin) collection, _);
        return null;
    }

    @Override
    public Void visit(MapBuiltin map, Void _) {
        visit((DataStructureBuiltin) map, _);
        return null;
    }
    
    @Override
    public Void visit(SetBuiltin set, Void _) throws RuntimeException {
        visit((DataStructureBuiltin) set, _);
        return null;
    }
    
    @Override
    public Void visit(ListBuiltin set, Void _) throws RuntimeException {
        visit((DataStructureBuiltin) set, _);
        return null;
    }


    @Override
    public Void visit(Hole hole, Void _) {
        result.append("HOLE");
        return null;
    }

    @Override
    public Void visit(FreezerHole hole, Void _) {
        result.append("HOLE");
        return null;
    }

    @Override
    public Void visit(KInjectedLabel kInjectedLabel, Void _) {
        Term term = kInjectedLabel.getTerm();
        String sort = term.getSort().equals("K") ? "KList" : term.getSort();
        if (MetaK.isKSort(sort)) {
            //result.append(StringUtil.escapeMaude(kInjectedLabel.getInjectedSort(term.getSort())));
            result.append(KInjectedLabel.getInjectedSort(sort));
            result.append("2KLabel_(");
        } else if (MetaK.isCellSort(sort)){
            result.append(sort + "2KLabel_(");

        } else {
            result.append("#_(");
        }
        this.visitNode(term);
        result.append(")");
        return null;
    }

    @Override
    public Void visit(FreezerLabel freezerLabel, Void _) {
        Term term = freezerLabel.getTerm();
        result.append("#freezer_(");
        this.visitNode(term);
        result.append(")");
        return null;
    }

    @Override
    public Void visit(Freezer freezer, Void _) {
        this.visitNode(freezer.getTerm());
        return null;
    }

    @Override
    public Void visit(KLabel kLabel, Void _) {
        throw new RuntimeException("don't know how to maudify KLabel of type" + kLabel.getClass());
    }

    @Override
    public Void visit(TermComment termComment, Void _) {
        result.append(" .Bag ");
        return null;
    }

    /**
     * Pretty printing a Bag to Maude.
     *
     * The code is slightly altered to also work with printing cell contents
     * when cells are sorted
     * @param bag
     */
    @Override
    public Void visit(Bag bag, Void _) {
        if (bag.getContents().isEmpty()) {
            this.visitNode(new ListTerminator(KSorts.BAG, null));
            return null;
        }
        for (Term item: bag.getContents()) {
            if (item instanceof TermComment) continue;
            result.append("(");
            this.visitNode(item);
            result.append(")");
            result.append(" ");
        }
        return null;
//        this.visit((Collection) bag);
        // throw new RuntimeException("don't know how to maudify Bag");
    }

    @Override
    public Void visit(org.kframework.kil.Ambiguity ambiguity, Void _) {
        result.append("amb(");
        boolean first = true;
        for (Term term : ambiguity.getContents()) {
            if (!first) {
                result.append(",");
            } else {
                first = false;
            }
            if (term != null) {
                this.visitNode(term);
            } else {
                result.append("null");
            }
        }
        result.append(")");
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context context, Void _) {
        result.append("mb context ");
        this.visit((Sentence) context, _);
        result.append("\n");
        return null;
    }

    @Override
    public Void visit(LiterateDefinitionComment literateDefinitionComment, Void _) {
        return null;
        // do nothing
    }

    @Override
    public Void visit(LiterateModuleComment literateModuleComment, Void _) {
        return null;
        // do nothing
    }

    @Override
    public Void visit(org.kframework.kil.Require require, Void _) {
        return null;
        // do nothing
    }

    @Override
    public Void visit(BackendTerm term, Void _) {
        result.append(term.getValue());
        return null;
    }

    @Override
    public Void visit(Bracket term, Void _) {
        this.visitNode(term.getContent());
        return null;
    }

    @Override
    public Void visit(Cast term, Void _) {
        throw new RuntimeException("don't know how to maudify Cast at "+term.getFilename()+" "+term.getLocation());
    }

    @Override
    public Void visit(MapUpdate term, Void _) {
        result.append("_`(_`)(Map2KLabel(");
        result.append("update(");
        result.append("remove(");
        result.append(term.map().getName() + ":Map , (.Map ");
        for (java.util.Map.Entry<Term, Term> t : term.removeEntries().entrySet()) {
            this.visitNode(t.getKey());
            result.append(" |-> ");
            this.visitNode(t.getValue());
            result.append(" ");
        }
        result.append(")), ");

        result.append("(.Map ");
        for (java.util.Map.Entry<Term, Term> t : term.updateEntries().entrySet()) {
            this.visitNode(t.getKey());
            result.append(" |-> ");
            this.visitNode(t.getValue());
            result.append(" ");
        }
        result.append("))");
        result.append(") , .KList)");
        return null;
    }

    private static java.util.Map<KSort, String> maudeCollectionConstructors = new HashMap<KSort, String>();
    static {
        maudeCollectionConstructors.put(KSort.Bag, "__");
        maudeCollectionConstructors.put(KSort.K, "_~>_");
        maudeCollectionConstructors.put(KSort.KList, "_`,`,_");
    }

    public static String getMaudeConstructor(String sort) {
        return maudeCollectionConstructors.get(KSort.getKSort(sort));
    }
}
