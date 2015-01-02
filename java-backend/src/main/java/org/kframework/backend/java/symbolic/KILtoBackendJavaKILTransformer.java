// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import static org.kframework.kil.KLabelConstant.ANDBOOL_KLABEL;
import static org.kframework.kil.KLabelConstant.BOOL_ANDBOOL_KLABEL;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.FloatToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.indexing.IndexingTable;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.CellLabel;
import org.kframework.backend.java.kil.ConcreteCollectionVariable;
import org.kframework.backend.java.kil.DataStructures;
import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.GlobalContext;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.JavaBackendRuleData;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KItemProjection;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.DataStructureSort;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.GenericToken;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.TermComment;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.errorsystem.KExceptionManager.KEMException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import com.google.common.collect.Iterables;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.inject.Inject;


/**
 * Convert a term from the KIL representation into the Java Rewrite engine internal representation.
 *
 * @author AndreiS
 */
public class KILtoBackendJavaKILTransformer extends CopyOnWriteTransformer {

    private boolean freshRules;

    /**
     * Maps variables representing concrete collections to their sizes. This
     * field is set at the beginning of
     * {@link #visit(org.kframework.kil.Rule)} and reset before that method
     * returns. Moreover, it is only used in
     * {@link #visit(org.kframework.kil.Variable)} when transforming
     * {@code Variable}s inside that {@code Rule}.
     */
    private Map<org.kframework.kil.Variable, Integer> concreteCollectionSize
            = Collections.emptyMap();
    private final GlobalContext globalContext;
    private final IndexingTable.Data indexingData;
    private final KExceptionManager kem;

    @Inject
    public KILtoBackendJavaKILTransformer(
            Context context,
            GlobalContext globalContext,
            @FreshRules boolean freshRules,
            IndexingTable.Data data,
            KExceptionManager kem) {
        super("Transform KIL into java backend KIL", context);
        this.freshRules = freshRules;
        this.globalContext = globalContext;
        this.indexingData = data;
        this.kem = kem;
    }

    public Definition transformDefinition(org.kframework.kil.Definition node) {
        Definition transformedDef = (Definition) this.visitNode(node);
        globalContext.setDefinition(transformedDef);

        Definition expandedDefinition = new MacroExpander(TermContext.of(globalContext), kem).processDefinition();
        globalContext.setDefinition(expandedDefinition);

        Definition evaluatedDefinition = evaluateDefinition(globalContext);
        globalContext.setDefinition(evaluatedDefinition);
        return evaluatedDefinition;
    }

    public Rule transformAndEval(org.kframework.kil.Rule node) {
        Rule rule = null;
        rule = new MacroExpander(TermContext.of(globalContext), kem).processRule((Rule) this.visitNode(node));
        rule = evaluateRule(rule, globalContext);

        return rule;
    }

    public Term transformAndEval(org.kframework.kil.Term node) {
        Term term = null;
        term = new MacroExpander(TermContext.of(globalContext), kem).processTerm((Term) this.visitNode(node));
        term = term.evaluate(TermContext.of(globalContext));

        return term;
    }

    @Override
    public ASTNode complete(ASTNode node, ASTNode r) {
        r.copyAttributesFrom(node);
        return super.complete(node, r);
    }

    @Override
    public ASTNode visit(org.kframework.kil.KApp node, Void _void)  {
        if (node.getLabel() instanceof org.kframework.kil.Token) {
            if (node.getLabel() instanceof BoolBuiltin) {
                return BoolToken.of(((BoolBuiltin) node.getLabel()).booleanValue());
            } else if (node.getLabel() instanceof IntBuiltin) {
                return IntToken.of(((IntBuiltin) node.getLabel()).bigIntegerValue());
            } else if (node.getLabel() instanceof StringBuiltin) {
                return StringToken.of(((StringBuiltin) node.getLabel()).stringValue());
            } else if (node.getLabel() instanceof FloatBuiltin) {
                return FloatToken.of(
                        ((FloatBuiltin) node.getLabel()).bigFloatValue(),
                        ((FloatBuiltin) node.getLabel()).exponent());
            } else if (node.getLabel() instanceof GenericToken) {
                return UninterpretedToken.of(
                        Sort.of(((GenericToken) node.getLabel()).tokenSort()),
                        ((GenericToken) node.getLabel()).value());
            } else {
                assert false : "unsupported Token " + node.getLabel();
            }
        }

        Term kLabel = (Term) this.visitNode(node.getLabel());
        Term kList = (Term) this.visitNode(node.getChild());
        if (kList instanceof Variable) {
            kList = kList.sort().equals(Sort.KLIST) ? kList : KList.singleton(kList);
        }
        return KItem.of(kLabel, kList, TermContext.of(globalContext), node.getSource(), node.getLocation());
    }

    @Override
    public ASTNode visit(org.kframework.kil.KItemProjection node, Void _void)  {
        return new KItemProjection(Kind.of(Sort.of(node.projectedKind())), (Term) this.visitNode(node.getTerm()));
    }

    @Override
    public ASTNode visit(org.kframework.kil.KLabelConstant node, Void _void)  {
        return KLabelConstant.of(node.getLabel(), context);
    }

    @Override
    public ASTNode visit(org.kframework.kil.KLabelInjection node, Void _void)  {
        return new KLabelInjection((Term) this.visitNode(node.getTerm()));
    }

    @Override
    public ASTNode visit(org.kframework.kil.KInjectedLabel node, Void _void)  {
        Term term = (Term) this.visitNode(node.getTerm());
        return new KLabelInjection(term);
    }

    @Override
    public ASTNode visit(org.kframework.kil.FreezerLabel node, Void _void)  {
        Term term = (Term) this.visitNode(node.getTerm());
        return new KLabelFreezer(term);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Hole node, Void _void)  {
        return Hole.HOLE;
    }

    @Override
    public ASTNode visit(org.kframework.kil.FreezerHole node, Void _void)  {
        return Hole.HOLE;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Token node, Void _void)  {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode visit(org.kframework.kil.KSequence node, Void _void)  {
        List<org.kframework.kil.Term> list = new ArrayList<>();
        KILtoBackendJavaKILTransformer.flattenKSequence(list, node.getContents());

        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(org.kframework.kil.Sort.K)) {
            variable = (Variable) this.visitNode(list.remove(list.size() - 1));
        }

        KSequence.Builder builder = KSequence.builder();
        for (org.kframework.kil.Term term : list) {
            builder.concatenate((Term) this.visitNode(term));
        }
        if (variable != null) {
            builder.concatenate(variable);
        }

        return builder.build();
    }

    @Override
    public ASTNode visit(org.kframework.kil.KList node, Void _void)  {
        List<org.kframework.kil.Term> list = new ArrayList<org.kframework.kil.Term>();
        KILtoBackendJavaKILTransformer.flattenKList(list, node.getContents());

        Variable variable = null;
        if (!list.isEmpty()
                && list.get(list.size() - 1) instanceof org.kframework.kil.Variable
                && list.get(list.size() - 1).getSort().equals(org.kframework.kil.Sort.KLIST)) {
            variable = (Variable) this.visitNode(list.remove(list.size() - 1));
        }

        KList.Builder builder = KList.builder();
        for (org.kframework.kil.Term term : list) {
            builder.concatenate((Term) this.visitNode(term));
        }
        if (variable != null) {
            builder.concatenate(variable);
        }

        return builder.build();
    }

    @Override
    public ASTNode visit(org.kframework.kil.Cell node, Void _void)  {
        return CellCollection.singleton(
                CellLabel.of(node.getLabel()),
                (Term) this.visitNode(node.getContents()),
                context);
    }

    @Override
    public ASTNode visit(org.kframework.kil.Bag node, Void _void) {
        List<org.kframework.kil.Term> contents = new ArrayList<org.kframework.kil.Term>();
        org.kframework.kil.Bag.flatten(contents, node.getContents());

        CellCollection.Builder builder = CellCollection.builder(context);
        for (org.kframework.kil.Term term : contents) {
            if (term instanceof TermComment) {
                continue;
            }
            builder.concatenate((Term) this.visitNode(term));
        }

        return builder.build();
    }

    @Override
    public ASTNode visit(org.kframework.kil.ListBuiltin node, Void _void)  {
        BuiltinList.Builder builder = BuiltinList.builder();
        for (org.kframework.kil.Term element : node.elementsLeft()) {
            builder.addItem((Term) this.visitNode(element));
        }
        for (org.kframework.kil.Term term : node.baseTerms()) {
            builder.concatenate((Term) this.visitNode(term));
        }
        for (org.kframework.kil.Term element : node.elementsRight()) {
            builder.addItem((Term) this.visitNode(element));
        }
        return builder.build();
    }

    @Override
    public ASTNode visit(org.kframework.kil.SetBuiltin node, Void _void)  {
        BuiltinSet.Builder builder = BuiltinSet.builder();
        for (org.kframework.kil.Term element : node.elements()) {
            builder.add((Term) this.visitNode(element));
        }
        for (org.kframework.kil.Term term : node.baseTerms()) {
            builder.concatenate((Term) this.visitNode(term));
        }
        return builder.build();
    }

    @Override
    public ASTNode visit(org.kframework.kil.MapBuiltin node, Void _void)  {
        BuiltinMap.Builder builder = BuiltinMap.builder();
        for (Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.elements().entrySet()) {
            builder.put(
                    (Term) this.visitNode(entry.getKey()),
                    (Term) this.visitNode(entry.getValue()));
        }
        for (org.kframework.kil.Term term : node.baseTerms()) {
            builder.concatenate((Term) this.visitNode(term));
        }
        return builder.build();
    }

    @Override
    public ASTNode visit(org.kframework.kil.ListUpdate node, Void _void)  {
        Variable base = (Variable) this.visitNode(node.base());

        return DataStructures.listRange(
                base,
                node.removeLeft().size(),
                node.removeRight().size(),
                TermContext.of(globalContext));
    }

    @Override
    public ASTNode visit(org.kframework.kil.SetUpdate node, Void _void)  {
        Variable set = (Variable) this.visitNode(node.set());

        HashSet<Term> removeSet = new HashSet<Term>(node.removeEntries().size());
        for (org.kframework.kil.Term term : node.removeEntries()) {
            removeSet.add((Term) this.visitNode(term));
        }

        return DataStructures.setDifference(set, removeSet, TermContext.of(globalContext));
    }

     @Override
    public ASTNode visit(org.kframework.kil.MapUpdate node, Void _void)  {
        Variable map = (Variable) this.visitNode(node.map());

        HashSet<Term> removeSet = new HashSet<Term>(node.removeEntries().size());
        for (org.kframework.kil.Term term : node.removeEntries().keySet()) {
            removeSet.add((Term) this.visitNode(term));
        }

        HashMap<Term, Term> updateMap = new HashMap<Term, Term>(node.updateEntries().size());
        for (Map.Entry<org.kframework.kil.Term, org.kframework.kil.Term> entry :
                node.updateEntries().entrySet()) {
            Term key = (Term) this.visitNode(entry.getKey());
            Term value = (Term) this.visitNode(entry.getValue());
            updateMap.put(key, value);
        }

        return DataStructures.mapUpdateAll(
                DataStructures.mapRemoveAll(map, removeSet, TermContext.of(globalContext)),
                updateMap,
                TermContext.of(globalContext));
    }

    @Override
    public ASTNode visit(org.kframework.kil.Variable node, Void _void)  {
        String name = node.fullName();

        if (node.getSort().equals(org.kframework.kil.Sort.BAG)
                || node.getSort().equals(org.kframework.kil.Sort.BAG_ITEM)) {
            return new Variable(name, Kind.CELL_COLLECTION.asSort());
        }

        if (node.getSort().equals(org.kframework.kil.Sort.K)) {
            return new Variable(name, Sort.KSEQUENCE);
        }
        if (node.getSort().equals(org.kframework.kil.Sort.KLIST)) {
            return new Variable(name, Sort.KLIST);
        }

        DataStructureSort dataStructureSort = context.dataStructureSortOf(node.getSort());
        if (dataStructureSort != null) {
            Sort sort = null;
            if (dataStructureSort.type().equals(org.kframework.kil.Sort.LIST)) {
                sort = Sort.LIST;
            } else if (dataStructureSort.type().equals(org.kframework.kil.Sort.MAP)) {
                sort = Sort.MAP;
            } else if (dataStructureSort.type().equals(org.kframework.kil.Sort.SET)) {
                sort = Sort.SET;
            } else {
                assert false: "unexpected data structure " + dataStructureSort.type();
            }

            if (concreteCollectionSize.containsKey(node)) {
                return new ConcreteCollectionVariable(
                        name,
                        sort,
                        concreteCollectionSize.get(node));
            } else {
                return new Variable(name, sort);
            }
        }

        return new Variable(name, Sort.of(node.getSort()));
    }

    @Override
    public ASTNode visit(org.kframework.kil.Rule node, Void _void)  {
        assert node.getBody() instanceof org.kframework.kil.Rewrite;

        JavaBackendRuleData ruleData = node.getAttribute(JavaBackendRuleData.class);
        if (ruleData == null) {
            ruleData = new JavaBackendRuleData();
        }
        concreteCollectionSize = ruleData.getConcreteDataStructureSize();

        org.kframework.kil.Rewrite rewrite = (org.kframework.kil.Rewrite) node.getBody();
        Term leftHandSide = (Term) this.visitNode(rewrite.getLeft());
        Term rightHandSide = (Term) this.visitNode(rewrite.getRight());

        List<Term> requires = new ArrayList<>();
        if (node.getRequires() != null) {
            transformConjunction(requires, (Term) this.visitNode(node.getRequires()));
        }

        List<Term> ensures = new ArrayList<>();
        if (node.getEnsures() != null) {
            transformConjunction(ensures, (Term) this.visitNode(node.getEnsures()));
        }

        UninterpretedConstraint.Builder lookupsBuilder = UninterpretedConstraint.builder();
        for (org.kframework.kil.BuiltinLookup lookup : ruleData.getLookups()) {
            Variable base = (Variable) this.visitNode(lookup.base());
            Term key = (Term) this.visitNode(lookup.key());
            if (lookup instanceof org.kframework.kil.SetLookup) {
                if (lookup.choice()) {
                    lookupsBuilder.add(DataStructures.choice(base, TermContext.of(globalContext)), key, TermContext.of(globalContext));
                } else {
                    lookupsBuilder.add(DataStructures.lookup(base, key, TermContext.of(globalContext)), BoolToken.TRUE, TermContext.of(globalContext));
                }
            } else {
                Term value = (Term) this.visitNode(lookup.value());
                if (lookup instanceof org.kframework.kil.MapLookup) {
                    if (lookup.choice()) {
                        lookupsBuilder.add(DataStructures.choice(base, TermContext.of(globalContext)), key, TermContext.of(globalContext));
                    }
                    lookupsBuilder.add(DataStructures.lookup(base, key, TermContext.of(globalContext)), value, TermContext.of(globalContext));
                } else { // ListLookup
                    lookupsBuilder.add(DataStructures.lookup(base, key, TermContext.of(globalContext)), value, TermContext.of(globalContext));
                }
            }

        }

        // TODO(AndreiS): check !Variable only appears in the RHS
        Set<Variable> freshConstants = node.getBody().variables().stream()
                .filter(v -> v.isFreshConstant())
                .map(v -> (Variable) this.visitNode(v))
                .collect(Collectors.toSet());

        Set<Variable> freshVariables = node.getBody().variables().stream()
                .filter(v -> v.isFreshVariable())
                .map(v -> (Variable) this.visitNode(v))
                .collect(Collectors.toSet());

        assert leftHandSide.kind() == rightHandSide.kind()
                || leftHandSide.kind().isComputational() && rightHandSide.kind().isComputational();

        concreteCollectionSize = Collections.emptyMap();

        java.util.Map<CellLabel, Term> lhsOfReadCell = null;
        java.util.Map<CellLabel, Term> rhsOfWriteCell = null;
        if (ruleData.isCompiledForFastRewriting()) {
            lhsOfReadCell = Maps.newHashMap();
            for (java.util.Map.Entry<String, org.kframework.kil.Term> entry : ruleData.getLhsOfReadCell().entrySet()) {
                lhsOfReadCell.put(CellLabel.of(entry.getKey()), (Term) this.visitNode(entry.getValue()));
            }
            rhsOfWriteCell = Maps.newHashMap();
            for (java.util.Map.Entry<String, org.kframework.kil.Term> entry : ruleData.getRhsOfWriteCell().entrySet()) {
                rhsOfWriteCell.put(CellLabel.of(entry.getKey()), (Term) this.visitNode(entry.getValue()));
            }
        }

        java.util.Set<CellLabel> cellsToCopy = null;
        if (ruleData.getCellsToCopy() != null) {
            cellsToCopy = Sets.newHashSet();
            for (String cellLabelName : ruleData.getCellsToCopy()) {
                cellsToCopy.add(CellLabel.of(cellLabelName));
            }
        }

        Rule rule = new Rule(
                node.getLabel(),
                leftHandSide,
                rightHandSide,
                requires,
                ensures,
                freshConstants,
                freshVariables,
                lookupsBuilder.build(),
                ruleData.isCompiledForFastRewriting(),
                lhsOfReadCell,
                rhsOfWriteCell,
                cellsToCopy,
                ruleData.getMatchingInstructions(),
                node,
                TermContext.of(globalContext));

        if (freshRules) {
            return rule.getFreshRule(TermContext.of(globalContext));
        }
        return rule;
    }

    private void transformConjunction(Collection<Term> requires, Term term) {
        if (term instanceof KItem &&
               (((KItem) term).kLabel().toString().equals(ANDBOOL_KLABEL.getLabel()) ||
                ((KItem) term).kLabel().toString().equals(BOOL_ANDBOOL_KLABEL.getLabel()))) {
            for (Term item : ((KList) ((KItem) term).kList()).getContents()) {
                requires.add(item);
            }
        } else {
            requires.add(term);
        }
    }

    @Override
    public ASTNode visit(org.kframework.kil.Definition node, Void _void) {
        Definition definition = new Definition(context, kem, indexingData);
        globalContext.setDefinition(definition);

        Module singletonModule = node.getSingletonModule();

        for (org.kframework.kil.Rule rule : singletonModule.getRules()) {
            if (rule.containsAttribute(Attribute.PREDICATE_KEY)) {
                continue;
            }

            definition.addRule((Rule) this.visitNode(rule));
        }

        for (String kLabelName : singletonModule.getModuleKLabels()) {
            definition.addKLabel(KLabelConstant.of(kLabelName, context));
        }

        /* collect the productions which have the attributes strict and seqstrict */
        Set<Production> productions = singletonModule.getSyntaxByTag("strict", context);
        productions.addAll(singletonModule.getSyntaxByTag("seqstrict", context));
        for (Production production : productions) {
            definition.addFrozenKLabel(KLabelConstant.of(production.getKLabelOfKItem(), context));
        }

        return definition;
    }

    /**
     * Partially evaluate the right-hand side and the conditions for each rule.
     *
     * @param definition
     *            the definition used for evaluation
     * @return the partially evaluated definition
     */
    private static Definition evaluateDefinition(GlobalContext globalContext) {
        Definition definition = globalContext.getDefinition();
        /* replace the unevaluated rules defining functions with their partially evaluated counterparts */
        ArrayList<Rule> partiallyEvaluatedRules = new ArrayList<>();
        /* iterate until a fixpoint is reached, because the evaluation with functions uses Term#substituteAndEvalaute */
        while (true) {
            boolean change = false;

            partiallyEvaluatedRules.clear();
            for (Rule rule : Iterables.concat(definition.functionRules().values(),
                    definition.anywhereRules().values())) {
                Rule evaluatedRule = evaluateRule(rule, globalContext);
                partiallyEvaluatedRules.add(evaluatedRule);

                if (!evaluatedRule.equals(rule)) {
                    change = true;
                }
            }

            if (!change) {
                break;
            }

            definition.functionRules().clear();
            definition.anywhereRules().clear();
            definition.addRuleCollection(partiallyEvaluatedRules);
        }

        /* replace the unevaluated rules and macros with their partially evaluated counterparts */
        partiallyEvaluatedRules.clear();
        Iterable<Rule> rules = Iterables.concat(
                definition.rules(),
                definition.macros(),
                definition.patternRules().values(),
                definition.patternFoldingRules());
        for (Rule rule : rules) {
            partiallyEvaluatedRules.add(evaluateRule(rule, globalContext));
        }
        definition.rules().clear();
        definition.macros().clear();
        definition.patternRules().clear();
        definition.patternFoldingRules().clear();
        definition.addRuleCollection(partiallyEvaluatedRules);

        return definition;
    }

    /**
     * Partially evaluate the right-hand side and the conditions of a specified rule.
     * @param rule
     *          the rule being partially evaluated
     * @param definition
     *          the definition used for evaluation
     * @return
     *          the partially evaluated rule
     */
    private static Rule evaluateRule(Rule rule, GlobalContext globalContext) {
        try {
            TermContext termContext = TermContext.of(globalContext);
            // TODO(AndreiS): some evaluation is required in the LHS as well
            // TODO(YilongL): cannot simply uncomment the following code because it
            // may evaluate the LHS using the rule itself
            //Term leftHandSide = rule.leftHandSide().evaluate(termContext);

            Rule origRule = rule;
            Term rightHandSide = rule.rightHandSide().evaluate(termContext);
            List<Term> requires = new ArrayList<>();
            for (Term term : rule.requires()) {
                requires.add(term.evaluate(termContext));
            }
            List<Term> ensures = new ArrayList<>();
            for (Term term : rule.ensures()) {
                ensures.add(term.evaluate(termContext));
            }
            UninterpretedConstraint.Builder lookupsBuilder = UninterpretedConstraint.builder();
            for (UninterpretedConstraint.Equality equality : rule.lookups().equalities()) {
                lookupsBuilder.add(
                        equality.leftHandSide().evaluate(termContext),
                        equality.rightHandSide().evaluate(termContext),
                        termContext);
            }

            Map<CellLabel, Term> rhsOfWriteCell = null;
            if (rule.isCompiledForFastRewriting()) {
                rhsOfWriteCell = new HashMap<>();
                for (Map.Entry<CellLabel, Term> entry : rule.rhsOfWriteCell().entrySet()) {
                    rhsOfWriteCell.put(entry.getKey(), entry.getValue().evaluate(termContext));
                }
            }

            Rule newRule = new Rule(
                    rule.label(),
                    rule.leftHandSide(),
                    rightHandSide,
                    requires,
                    ensures,
                    rule.freshConstants(),
                    rule.freshVariables(),
                    lookupsBuilder.build(),
                    rule.isCompiledForFastRewriting(),
                    rule.lhsOfReadCell(),
                    rhsOfWriteCell,
                    rule.cellsToCopy(),
                    rule.matchingInstructions(),
                    rule,
                    termContext);
            return newRule.equals(rule) ? origRule : newRule;
        } catch (KEMException e) {
            e.exception.addTraceFrame("while compiling rule at location " + rule.getSource() + rule.getLocation());
            throw e;
        }
    }

    private static void flattenKSequence(
            List<org.kframework.kil.Term> flatList,
            List<org.kframework.kil.Term> nestedList) {
        for (org.kframework.kil.Term term : nestedList) {
            if (term instanceof org.kframework.kil.KSequence) {
                org.kframework.kil.KSequence kSequence = (org.kframework.kil.KSequence) term;
                KILtoBackendJavaKILTransformer.flattenKSequence(flatList, kSequence.getContents());
            } else {
                flatList.add(term);
            }
        }
    }

    private static void flattenKList(
            List<org.kframework.kil.Term> flatList,
            List<org.kframework.kil.Term> nestedList) {
        for (org.kframework.kil.Term term : nestedList) {
            if (term instanceof org.kframework.kil.KList) {
                org.kframework.kil.KList kList = (org.kframework.kil.KList) term;
                KILtoBackendJavaKILTransformer.flattenKList(flatList, kList.getContents());
            } else {
                flatList.add(term);
            }
        }
    }
}
