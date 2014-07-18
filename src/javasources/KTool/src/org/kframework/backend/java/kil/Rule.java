// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.rewritemachine.Instruction;
import org.kframework.backend.java.rewritemachine.KAbstractRewriteMachine;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.UninterpretedConstraint;
import org.kframework.backend.java.symbolic.UninterpretedConstraint.Equality;
import org.kframework.backend.java.symbolic.VariableOccurrencesCounter;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.loader.Constants;

import com.google.common.collect.HashMultiset;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Lists;
import com.google.common.collect.Multiset;
import com.google.common.collect.Sets;


/**
 * A K rule in the format of the Java Rewrite Engine.
 *
 * @author AndreiS
 */
public class Rule extends JavaSymbolicObject {

    private final String label;
    private final Term leftHandSide;
    private final Term rightHandSide;
    private final ImmutableList<Term> requires;
    private final ImmutableList<Term> ensures;
    private final ImmutableSet<Variable> freshVariables;
    private final UninterpretedConstraint lookups;
    private final IndexingPair indexingPair;
    private final boolean containsKCell;
    private final boolean hasUnboundVars;

    /**
     * Specifies whether this rule has been compiled to generate instructions
     * for the {@link KAbstractRewriteMachine}.
     */
    private boolean compiledForFastRewriting;
    /**
     * Left-hand sides of the local rewrite operations under read cells; such
     * left-hand sides are used as patterns to match against the subject term.
     */
    private final Map<String, Term> lhsOfReadCells;
    /**
     * Right-hand sides of the local rewrite operations under write cells.
     */
    private final Map<String, Term> rhsOfWriteCells;
    /**
     * @see Rule#computeReusableBoundVars()
     */
    private final Multiset<Variable> reusableVariables;
    /**
     * Ground cells inside the right-hand side of this rule. Since cells are
     * mutable, they must be copied when the RHS is instantiated to avoid
     * undesired sharing.
     */
    private final Set<String> groundCells;
    /**
     * Instructions generated from this rule to be executed by the
     * {@link KAbstractRewriteMachine}.
     */
    private final List<Instruction> instructions;

    /**
     * Unbound variables in the rule before kompilation; that is, all variables
     * on the rhs which do not appear in either lhs or fresh condition(s).
     * Therefore, variables that could be bound by side-condition(s) are also
     * counted. This definition of unbound variable is consistent with the
     * checking algorithm used in the {@link CheckVariables} pass.
     */
    private final ImmutableSet<Variable> unboundVars;
    private final boolean isSortPredicate;
    private final Sort predSort;
    private final KItem sortPredArg;

    public Rule(
            String label,
            Term leftHandSide,
            Term rightHandSide,
            Collection<Term> requires,
            Collection<Term> ensures,
            Collection<Variable> freshVariables,
            UninterpretedConstraint lookups,
            boolean compiledForFastRewriting,
            Map<String, Term> lhsOfReadCells,
            Map<String, Term> rhsOfWriteCells,
            Set<String> cellsToCopy,
            List<Instruction> instructions,
            Attributes attributes,
            Definition definition) {
        this.label = label;
        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.requires = ImmutableList.copyOf(requires);
        this.ensures = ImmutableList.copyOf(ensures);
        this.freshVariables = ImmutableSet.copyOf(freshVariables);
        this.lookups = lookups;

        super.setAttributes(attributes);

        if (attributes.containsKey(Constants.STDIN)
                || attributes.containsKey(Constants.STDOUT)
                || attributes.containsKey(Constants.STDERR)) {
            Variable listVar = (Variable) lhsOfReadCells.values().iterator().next();
            BuiltinList streamList = listVar instanceof ConcreteCollectionVariable ?
                    new BuiltinList() : new BuiltinList(listVar);
            for (Equality eq : Lists.reverse(lookups.equalities())) {
                streamList.addLeft(eq.rightHandSide());
            }
            this.indexingPair = attributes.containsKey(Constants.STDIN) ?
                    IndexingPair.getInstreamIndexingPair(streamList, definition) :
                    IndexingPair.getOutstreamIndexingPair(streamList, definition);
        } else {
            Collection<IndexingPair> indexingPairs = leftHandSide.getKCellIndexingPairs(definition);

            /*
             * Compute indexing information only if the left-hand side of this rule has precisely one
             * k cell; set indexing to top otherwise (this rule could rewrite any term).
             */
            if (indexingPairs.size() == 1) {
                this.indexingPair = indexingPairs.iterator().next();
            } else {
                this.indexingPair = IndexingPair.TOP;
            }
        }

        leftHandSide.accept(new BottomUpVisitor() {
            @Override
            public void visit(Cell cell) {
                if (cell.getLabel().equals("k")) {
                    tempContainsKCell = true;
                } else if (cell.contentKind() == Kind.CELL_COLLECTION) {
                    super.visit(cell);
                }
            }
        });
        containsKCell = tempContainsKCell;

        hasUnboundVars = super.containsAttribute(CheckVariables.UNBOUND_VARS);
        if (hasUnboundVars) {
            // TODO(YilongL): maybe compute unbound variables in the generic KIL instead
            Set<Variable> ubVars = new HashSet<>(rightHandSide.variableSet());
            ubVars.removeAll(leftHandSide.variableSet());
            for (UninterpretedConstraint.Equality eq : lookups.equalities()) {
                ubVars.remove(eq.leftHandSide());
            }
            unboundVars = ImmutableSet.copyOf(ubVars);
        } else {
            unboundVars = null;
        }

        isSortPredicate = isFunction() && functionKLabel().isSortPredicate();
        if (isSortPredicate) {
            predSort = functionKLabel().getPredicateSort();

            assert leftHandSide instanceof KItem
                    && rightHandSide.equals(BoolToken.TRUE)
                    && ((KList) ((KItem) leftHandSide).kList()).size() == 1 :
                        "unexpected sort predicate rule: " + this;
            Term arg = ((KList) ((KItem) leftHandSide).kList()).get(0);
            assert arg instanceof KItem : "unexpected sort predicate rule: " + this;
            sortPredArg = (KItem) arg;
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
        this.instructions       = compiledForFastRewriting ? ImmutableList.copyOf(instructions) : null;
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
            for (Map.Entry<String, Term> entry : lhsOfReadCells.entrySet()) {
                String cellLabel = entry.getKey();
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
                assert eq.leftHandSide() instanceof DataStructureLookupOrChoice;
                if (eq.leftHandSide() instanceof DataStructureLookup) {
                    DataStructureLookup lookup = (DataStructureLookup) eq.leftHandSide();
                    Term value = eq.rightHandSide();

                    if (!lhsOfReadOnlyCell.contains(lookup.base())) {
                        // do not double count base variable again
                        lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(lookup.key()));
                        lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(value));
                    }
                }
            }
        } else {
            lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(leftHandSide));
            for (Equality eq : lookups.equalities()) {
                assert eq.leftHandSide() instanceof DataStructureLookupOrChoice;
                if (eq.leftHandSide() instanceof DataStructureLookup) {
                    DataStructureLookup lookup = (DataStructureLookup) eq.leftHandSide();
                    Term value = eq.rightHandSide();

                    // do not double count base variable again
                    lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(lookup.key()));
                    lhsVariablesToReuse.addAll(VariableOccurrencesCounter.count(value));
                }
            }
        }

        return lhsVariablesToReuse;
    }

    private boolean tempContainsKCell = false;

    public String label() {
        return label;
    }

    public ImmutableList<Term> requires() {
        return requires;
    }

    public ImmutableList<Term> ensures() {
        return ensures;
    }

    public ImmutableSet<Variable> freshVariables() {
        return freshVariables;
    }

    public boolean hasUnboundVariables() {
        return hasUnboundVars;
    }

    public ImmutableSet<Variable> unboundVariables() {
        return unboundVars == null ? ImmutableSet.<Variable>of() : unboundVars;
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
        return super.containsAttribute(Attribute.FUNCTION_KEY);
    }

    public KLabelConstant functionKLabel() {
        assert isFunction();

        return (KLabelConstant) ((KItem) leftHandSide).kLabel();
    }

    /**
     * Returns a copy of this {@code Rule} with each {@link Variable} renamed to a fresh name.
     */
    public Rule getFreshRule(TermContext context) {
        return this.substitute(Variable.getFreshSubstitution(variableSet()), context);
    }

    public IndexingPair indexingPair() {
        return indexingPair;
    }

    public Term leftHandSide() {
        return leftHandSide;
    }

    public UninterpretedConstraint lookups() {
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

    public Map<String, Term> lhsOfReadCell() {
        return lhsOfReadCells;
    }

    public Map<String, Term> rhsOfWriteCell() {
        return rhsOfWriteCells;
    }

    public Multiset<Variable> reusableVariables() {
        return reusableVariables;
    }

    public Set<String> cellsToCopy() {
        return groundCells;
    }

    public List<Instruction> instructions() {
        return instructions;
    }

    @Override
    public Rule substitute(Map<Variable, ? extends Term> substitution, TermContext context) {
        return (Rule) super.substitute(substitution, context);
    }

    /**
     * Returns a new {@code Rule} instance obtained from this rule by substituting variable with
     * term.
     */
    @Override
    public Rule substituteWithBinders(Variable variable, Term term, TermContext context) {
        return (Rule) super.substituteWithBinders(variable, term, context);
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
                && freshVariables.equals(rule.freshVariables);
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + label.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + leftHandSide.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + rightHandSide.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + requires.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + ensures.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + lookups.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + freshVariables.hashCode();
        }
        return hashCode;
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
                string += " " + SymbolicConstraint.SEPARATOR + " ";
            }
            string += lookups;
        }
        if (ensures != null) {
            string += " ensures " + ensures;
        }
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
