// Copyright (c) 2013-2014 K Team. All Rights Reserved.

package org.kframework.backend.java.kil;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.indexing.IndexingPair;
import org.kframework.backend.java.symbolic.BottomUpVisitor;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.UninterpretedConstraint;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.compile.checks.CheckVariables;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;

import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableSet;


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
     * Unbound variables in the rule before kompilation; that is, all variables
     * on the rhs which do not appear in either lhs or fresh condition(s).
     * Therefore, variables that could be bound by side-condition(s) are also
     * counted. This definition of unbound variable is consistent with the
     * checking algorithm used in the {@link CheckVariables} pass.
     */
    private final ImmutableSet<Variable> unboundVars;
    private final boolean isSortPredicate;
    private final String predSort;
    private final KItem sortPredArg;

    public Rule(
            String label,
            Term leftHandSide,
            Term rightHandSide,
            Collection<Term> requires,
            Collection<Term> ensures,
            Collection<Variable> freshVariables,
            UninterpretedConstraint lookups,
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

        Collection<IndexingPair> indexingPairs = leftHandSide.getIndexingPairs(definition);
        /*
         * Compute indexing information only if the left-hand side of this rule has precisely one
         * k cell; set indexing to top otherwise (this rule could rewrite any term).
         */
        if (indexingPairs.size() == 1) {
            this.indexingPair = indexingPairs.iterator().next();
        } else {
            this.indexingPair = IndexingPair.TOP;
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
        
        isSortPredicate = isFunction()
                && functionKLabel().toString().startsWith("is");
        if (isSortPredicate) {
            predSort = functionKLabel().toString().substring(2);
            
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
    }

    private boolean tempContainsKCell = false;
    
    /*
    public Rule(Term leftHandSide, Term rightHandSide, Term requires) {
        this(leftHandSide, rightHandSide, requires, null);
    }

    public Rule(Term leftHandSide, Term rightHandSide, Attributes attributes) {
        this(leftHandSide, rightHandSide, null, attributes);
    }

    public Rule(Term leftHandSide, Term rightHandSide) {
        this(leftHandSide, rightHandSide, null, null);
    }
    */
    
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
    public String predicateSort() {
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
