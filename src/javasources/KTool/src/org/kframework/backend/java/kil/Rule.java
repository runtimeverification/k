package org.kframework.backend.java.kil;

import java.util.Collection;
import java.util.Map;

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
    private final boolean hasUnboundedVars;
    private int hashCode = 0;

    public Rule(
            String label,
            Term leftHandSide,
            Term rightHandSide,
            Collection<Term> requires,
            Collection<Term> ensures,
            Collection<Variable> freshVariables,
            UninterpretedConstraint lookups,
            Attributes attributes) {
        this.label = label;
        this.leftHandSide = leftHandSide;
        this.rightHandSide = rightHandSide;
        this.requires = ImmutableList.copyOf(requires);
        this.ensures = ImmutableList.copyOf(ensures);
        this.freshVariables = ImmutableSet.copyOf(freshVariables);
        this.lookups = lookups;

        Collection<IndexingPair> indexingPairs = leftHandSide.getIndexingPairs();
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
        
        hasUnboundedVars = attributes.containsAttribute(CheckVariables.UNBOUNDED_VARS);

        super.setAttributes(attributes);
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
    
    public boolean hasUnboundedVariables() {
        return hasUnboundedVars;
    }

    public KLabelConstant functionKLabel() {
        assert super.containsAttribute(Attribute.FUNCTION_KEY);

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
