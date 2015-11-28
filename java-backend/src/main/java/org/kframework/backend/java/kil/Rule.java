// Copyright (c) 2013-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Multiset;
import com.google.common.collect.Sets;
import org.apache.commons.collections15.list.UnmodifiableList;
import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.rewritemachine.GenerateRHSInstructions;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.rewritemachine.MatchingInstruction;
import org.kframework.backend.java.rewritemachine.RHSInstruction;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.backend.java.symbolic.Equality;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.VariableOccurrencesCounter;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Constants;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;


/**
 * A K rule in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Rule extends JavaSymbolicObject<Rule> {

    private final String label;
    private final Term leftHandSide;
    private final Term rightHandSide;
    private final ImmutableList<Term> requires;
    private final ImmutableList<Term> ensures;
    private final ImmutableSet<Variable> freshConstants;
    private final ImmutableSet<Variable> freshVariables;
    private final ConjunctiveFormula lookups;
    private final IndexingPair indexingPair;
    private final boolean containsKCell;
    private final GlobalContext global;

    /**
     * Specifies whether this rule has been compiled to generate instructions
     * for the {@link KAbstractRewriteMachine}.
     */
    private final boolean compiledForFastRewriting;
    /**
     * Left-hand sides of the local rewrite operations under read cells; such
     * left-hand sides are used as patterns to match against the subject term.
     */
    private final Map<CellLabel, Term> lhsOfReadCells;
    /**
     * Right-hand sides of the local rewrite operations under write cells.
     */
    private final Map<CellLabel, Term> rhsOfWriteCells;
    /**
     * Instructions for constructing rhs of local rewrite operations under write cells.
     */
    private final Map<CellLabel, ImmutableList<RHSInstruction>> instructionsOfWriteCells;
    /**
     * Instructions for evaluating side condition of rule.
     */
    private final List<ImmutableList<RHSInstruction>> instructionsOfRequires;
    /**
     * Instructions for evaluating side condition of rule.
     */
    private final List<ImmutableList<RHSInstruction>> instructionsOfLookups;
    /**
     * @see Rule#computeReusableBoundVars()
     */
    private final Multiset<Variable> reusableVariables;
    /**
     * Ground cells inside the right-hand side of this rule. Since cells are
     * mutable, they must be copied when the RHS is instantiated to avoid
     * undesired sharing.
     */
    private final Set<CellLabel> groundCells;
    /**
     * Instructions generated from this rule to be executed by the
     * {@link KAbstractRewriteMachine}.
     */
    private final List<MatchingInstruction> matchingInstructions;
    private final List<RHSInstruction> rhsInstructions;

    private final boolean modifyCellStructure;

    private final Set<CellLabel> readCells;
    private final Set<CellLabel> writeCells;

    private final Set<Variable> matchingVariables;

    // TODO(YilongL): make it final
    private boolean isSortPredicate;
    private final Sort predSort;
    private final KItem sortPredArg;

    public Rule(
            String label,
            Term leftHandSide,
            Term rightHandSide,
            List<Term> requires,
            List<Term> ensures,
            Set<Variable> freshConstants,
            Set<Variable> freshVariables,
            ConjunctiveFormula lookups,
            boolean compiledForFastRewriting,
            Map<CellLabel, Term> lhsOfReadCells,
            Map<CellLabel, Term> rhsOfWriteCells,
            Set<CellLabel> cellsToCopy,
            List<MatchingInstruction> instructions,
            ASTNode oldRule,
            GlobalContext global) {
        this.label = label;
        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.requires = ImmutableList.copyOf(requires);
        this.ensures = ImmutableList.copyOf(ensures);
        this.freshConstants = ImmutableSet.copyOf(freshConstants);
        this.freshVariables = ImmutableSet.copyOf(freshVariables);
        this.lookups = lookups;
        this.global = global;

        copyAttributesFrom(oldRule);
        setLocation(oldRule.getLocation());
        setSource(oldRule.getSource());

        if (oldRule.containsAttribute(org.kframework.kil.loader.Constants.STDIN)
                || oldRule.containsAttribute(org.kframework.kil.loader.Constants.STDOUT)
                || oldRule.containsAttribute(org.kframework.kil.loader.Constants.STDERR)) {
            Variable listVar = (Variable) lhsOfReadCells.values().iterator().next();
            BuiltinList.Builder streamListBuilder = BuiltinList.builder(global);
            for (Equality eq : lookups.equalities()) {
                streamListBuilder.addItem(eq.rightHandSide());
            }
            if (!(listVar instanceof ConcreteCollectionVariable)) {
                streamListBuilder.concatenate(Variable.getAnonVariable(Sort.LIST));
            }

            Term streamList = streamListBuilder.build();
            this.indexingPair = oldRule.containsAttribute(org.kframework.kil.loader.Constants.STDIN) ?
                    IndexingPair.getInstreamIndexingPair(streamList, global.getDefinition()) :
                    IndexingPair.getOutstreamIndexingPair(streamList, global.getDefinition());
        } else {
            Collection<IndexingPair> indexingPairs = leftHandSide.getKCellIndexingPairs(global.getDefinition());

            /*
             * Compute indexing information only if the left-hand side of this rule has precisely one
             * k cell; set indexing to top otherwise (this rule could rewrite any term).
             */
            if (indexingPairs.size() == 1) {
                this.indexingPair = indexingPairs.iterator().next();
            } else {
                this.indexingPair = global.getDefinition().indexingData.TOP_INDEXING_PAIR;
            }
        }

        containsKCell = !leftHandSide.getCellContentsByName(CellLabel.K).isEmpty();

        isSortPredicate = isFunction() && definedKLabel().isSortPredicate();
        if (isSortPredicate) {
            predSort = definedKLabel().getPredicateSort();

            if (leftHandSide instanceof KItem
                    && rightHandSide.equals(BoolToken.TRUE)
                    && ((KList) ((KItem) leftHandSide).kList()).concreteSize() == 1) {
                Term arg = ((KList) ((KItem) leftHandSide).kList()).get(0);
                sortPredArg = arg instanceof KItem ? (KItem) arg : null;
            } else {
                sortPredArg = null;
            }

            if (sortPredArg == null) {
                isSortPredicate = false;

                /*
                 * YilongL: the right-hand side of the sort predicate rule
                 * is not necessarily {@code BoolToken#True}? for example:
                 *     rule isNat(I:Int) => '_>=Int_(I:Int,, Int(#"0"))
                 */
                // TODO(YilongL): properly re-implement support for sort predicate rules
//                GlobalSettings.kem.registerCriticalWarning("Unexpected sort predicate rule: " + this, null, this);
            }
        } else {
            predSort = null;
            sortPredArg = null;
        }

        // setting fields related to fast rewriting
        this.compiledForFastRewriting = compiledForFastRewriting;
        this.lhsOfReadCells     = compiledForFastRewriting ? ImmutableMap.copyOf(lhsOfReadCells) : null;
        this.rhsOfWriteCells    = compiledForFastRewriting ? ImmutableMap.copyOf(rhsOfWriteCells) : null;
        this.reusableVariables  = computeReusableBoundVars();
        this.groundCells        = cellsToCopy != null ? ImmutableSet.copyOf(cellsToCopy) : null;
        this.matchingInstructions       = compiledForFastRewriting ? ImmutableList.copyOf(instructions) : null;

        GenerateRHSInstructions rhsVisitor = new GenerateRHSInstructions();
        rightHandSide.accept(rhsVisitor);
        this.rhsInstructions = rhsVisitor.getInstructions();

        instructionsOfWriteCells = new HashMap<>();
        if (compiledForFastRewriting) {
            for (Map.Entry<CellLabel, Term> entry :
                rhsOfWriteCells.entrySet()) {
                GenerateRHSInstructions visitor = new GenerateRHSInstructions();
                entry.getValue().accept(visitor);
                ImmutableList<RHSInstruction> rhsInstructions = visitor.getInstructions();
                if (rhsInstructions != null) {
                    instructionsOfWriteCells.put(entry.getKey(), rhsInstructions);
                }
            }
        }
        instructionsOfRequires = new ArrayList<>();
        for (Term require : requires) {
            GenerateRHSInstructions visitor = new GenerateRHSInstructions();
            require.accept(visitor);
            instructionsOfRequires.add(visitor.getInstructions());
        }
        instructionsOfLookups = new ArrayList<>();
        for (Equality equality : lookups.equalities()) {
            GenerateRHSInstructions visitor = new GenerateRHSInstructions();
            equality.leftHandSide().accept(visitor);
            instructionsOfLookups.add(visitor.getInstructions());
        }

        boolean modifyCellStructure;
        if (compiledForFastRewriting) {
            modifyCellStructure = false;
            for (CellLabel wrtCellLabel : rhsOfWriteCells.keySet()) {
                if (global.getDefinition().getConfigurationStructureMap().get(wrtCellLabel.name()).hasChildren()) {
                    modifyCellStructure = true;
                }
            }
        } else {
            modifyCellStructure = true;
        }
        this.modifyCellStructure = modifyCellStructure;

        if (compiledForFastRewriting) {
            final ImmutableSet.Builder<CellLabel> readBuilder = ImmutableSet.builder();
            lhsOfReadCells.keySet().stream().forEach(c -> {
                global.getDefinition().getConfigurationStructureMap().descendants(c.name()).stream()
                        .forEach(s -> readBuilder.add(CellLabel.of(s)));
            });
            readCells = readBuilder.build();
            final ImmutableSet.Builder<CellLabel> writeBuilder = ImmutableSet.builder();
            rhsOfWriteCells.keySet().stream().forEach(c -> {
                global.getDefinition().getConfigurationStructureMap().descendants(c.name()).stream()
                        .forEach(s -> writeBuilder.add(CellLabel.of(s)));
            });
            writeCells = writeBuilder.build();

        } else {
            readCells = writeCells = null;
        }

        Set<Variable> choiceVariables = new HashSet<>();
        if (compiledForFastRewriting) {
            for (int i = 0; i < instructions.size(); ++i) {
                if (instructions.get(i) == MatchingInstruction.CHOICE) {
                    choiceVariables.add(getChoiceVariableForCell(instructions.get(i + 1).cellLabel()));
                }
            }
        }
        matchingVariables = ImmutableSet.copyOf(Sets.union(
                !compiledForFastRewriting ?
                        leftHandSide.variableSet() :
                        Sets.union(
                                lhsOfReadCells.values().stream().map(Term::variableSet).flatMap(Set::stream).collect(Collectors.toSet()),
                                choiceVariables),
                Sets.union(
                        lookups.variableSet(),
                        requires.stream().map(Term::variableSet).flatMap(Set::stream).collect(Collectors.toSet()))));
    }

    public static Variable getChoiceVariableForCell(CellLabel label) {
        return new Variable("__choice_" + label, Sort.BAG);
    }

    /**
     * Private helper method that computes bound variables that can be reused to
     * instantiate the right-hand sides of the local rewrite operations.
     * <p>
     * Essentially, reusable bound variables are
     * <li>variables that occur in the left-hand sides of the rewrite operations
     * under read-write cells, plus
     * <li>variables in the key and value positions of data structure operations
     * (they are initially in the left-hand sides but moved to side conditions
     * during compilation)
     *
     * @return a multi-set representing reusable bound variables
     */
    private Multiset<Variable> computeReusableBoundVars() {
        Multiset<Variable> lhsVariablesToReuse = HashMultiset.create();
        if (compiledForFastRewriting) {
            Set<Term> lhsOfReadOnlyCell = Sets.newHashSet();
            /* add all variables that occur in the left-hand sides of read-write cells */
            for (Map.Entry<CellLabel, Term> entry : lhsOfReadCells.entrySet()) {
                CellLabel cellLabel = entry.getKey();
                Term lhs = entry.getValue();
                if (rhsOfWriteCells.containsKey(cellLabel)) {
                    lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(lhs));
                } else {
                    lhsOfReadOnlyCell.add(lhs);
                }
            }
            /* add variables that occur in the key and value positions of data
             * structure lookup operations under read-write cells */
            for (Equality eq : lookups.equalities()) {
                if (DataStructures.isLookup(eq.leftHandSide())) {
                    if (!lhsOfReadOnlyCell.contains(DataStructures.getLookupBase(eq.leftHandSide()))) {
                        // do not double count base variable again
                        lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(DataStructures.getLookupKey(eq.leftHandSide())));
                        lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(eq.rightHandSide()));
                    }
                }
            }
        } else {
            lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(leftHandSide));
            for (Equality eq : lookups.equalities()) {
                if (DataStructures.isLookup(eq.leftHandSide())) {
                    // do not double count base variable again
                    lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(DataStructures.getLookupKey(eq.leftHandSide())));
                    lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(eq.rightHandSide()));
                }
            }
        }

        return lhsVariablesToReuse;
    }

    public String label() {
        return label;
    }

    public GlobalContext globalContext() {
        return global;
    }

    public ImmutableList<Term> requires() {
        return requires;
    }

    public ImmutableList<Term> ensures() {
        return ensures;
    }

    public ConstrainedTerm createLhsPattern(TermContext termContext) {
        // TODO(YilongL): remove TermContext from the signature once
        // ConstrainedTerm doesn't hold a TermContext anymore
        return new ConstrainedTerm(
                leftHandSide,
                ConjunctiveFormula.of(lookups).addAll(requires),
                termContext);
    }

    public ConstrainedTerm createRhsPattern() {
        return new ConstrainedTerm(
                rightHandSide,
                ConjunctiveFormula.of(global).addAll(ensures),
                TermContext.builder(global).build());
    }

    public ImmutableSet<Variable> freshConstants() {
        return freshConstants;
    }

    public ImmutableSet<Variable> freshVariables() {
        return freshVariables;
    }

    /**
     * @return {@code true} if this rule is a sort predicate rule; otherwise,
     *         {@code false}
     */
    public boolean isSortPredicate() {
        return isSortPredicate;
    }

    /**
     * Gets the predicate sort if this rule is a sort predicate rule.
     */
    public Sort predicateSort() {
        assert isSortPredicate;

        return predSort;
    }

    /**
     * Gets the argument of the sort predicate if this rule is a sort predicate rule.
     */
    public KItem sortPredicateArgument() {
        assert isSortPredicate;

        return sortPredArg;
    }

    public boolean isFunction() {
        return containsAttribute(Attribute.FUNCTION_KEY)
               && !containsAttribute(Attribute.PATTERN_FOLDING_KEY);
    }

    public boolean isAnywhere() {
        return containsAttribute(Attribute.ANYWHERE_KEY);
    }

    public boolean isPattern() {
        return containsAttribute(Attribute.PATTERN_KEY);
    }

    public boolean isLemma() {
        return containsAttribute(Attribute.LEMMA_KEY);
    }

    /**
     * Returns the KLabel constant defined by this rule (either a function or a pattern).
     */
    public KLabelConstant definedKLabel() {
        assert isFunction() || isPattern();

        return (KLabelConstant) ((KItem) leftHandSide).kLabel();
    }

    public KLabelConstant anywhereKLabel() {
        assert isAnywhere();

        return (KLabelConstant) ((KItem) leftHandSide).kLabel();
    }

    public IndexingPair indexingPair() {
        return indexingPair;
    }

    public Term leftHandSide() {
        return leftHandSide;
    }

    public ConjunctiveFormula lookups() {
        return lookups;
    }

    public boolean containsKCell() {
        return containsKCell;
    }

    public Term rightHandSide() {
        return rightHandSide;
    }

    public boolean isCompiledForFastRewriting() {
        return compiledForFastRewriting;
    }

    public Map<CellLabel, Term> lhsOfReadCell() {
        return lhsOfReadCells;
    }

    public Map<CellLabel, Term> rhsOfWriteCell() {
        return rhsOfWriteCells;
    }

    public Map<CellLabel, ImmutableList<RHSInstruction>> instructionsOfWriteCell() {
        return instructionsOfWriteCells;
    }

    public List<ImmutableList<RHSInstruction>> instructionsOfRequires() {
        return UnmodifiableList.decorate(instructionsOfRequires);
    }

    public List<ImmutableList<RHSInstruction>> instructionsOfLookups() {
        return UnmodifiableList.decorate(instructionsOfLookups);
    }

    public Multiset<Variable> reusableVariables() {
        return reusableVariables;
    }

    public Set<CellLabel> cellsToCopy() {
        return groundCells;
    }

    public List<MatchingInstruction> matchingInstructions() {
        return matchingInstructions;
    }

    public List<RHSInstruction> rhsInstructions() {
        return rhsInstructions;
    }

    /**
     * Checks if this rule will modify the cell structure of the subject term.
     */
    public boolean modifyCellStructure() {
        return modifyCellStructure;
    }

    public Set<CellLabel> readCells() {
        return readCells;
    }

    public Set<CellLabel> writeCells() {
        return writeCells;
    }

    public Set<Variable> matchingVariables() {
        return matchingVariables;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof Rule)) {
            return false;
        }

        Rule rule = (Rule) object;
        return label.equals(rule.label)
                && leftHandSide.equals(rule.leftHandSide)
                && rightHandSide.equals(rule.rightHandSide)
                && requires.equals(rule.requires)
                && ensures.equals(rule.ensures)
                && lookups.equals(rule.lookups)
                && freshConstants.equals(rule.freshConstants);
    }

    @Override
    public int hashCode() {
        int h = hashCode;
        if (h == Constants.NO_HASHCODE) {
            h = 1;
            h = h * Constants.HASH_PRIME + label.hashCode();
            h = h * Constants.HASH_PRIME + leftHandSide.hashCode();
            h = h * Constants.HASH_PRIME + rightHandSide.hashCode();
            h = h * Constants.HASH_PRIME + requires.hashCode();
            h = h * Constants.HASH_PRIME + ensures.hashCode();
            h = h * Constants.HASH_PRIME + lookups.hashCode();
            h = h * Constants.HASH_PRIME + freshConstants.hashCode();
            h = h == 0 ? 1 : h;
            hashCode = h;
        }
        return h;
    }

    @Override
    public String toString() {
        String string = "rule ";
        if ((label != null) && (!label.isEmpty()))
            string += "[" + label + "]: ";
        string += leftHandSide + " => " + rightHandSide;
        if (requires != null) {
            string += " requires " + requires;
        }
        if (!lookups.equalities().isEmpty()) {
            if (requires == null) {
                string += " when ";
            } else {
                string += " " + ConjunctiveFormula.SEPARATOR + " ";
            }
            string += lookups;
        }
        if (ensures != null) {
            string += " ensures " + ensures;
        }
        string += " [" + "Location: " + getLocation() + ", " + getSource() + "]";
        return string;
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }
}
