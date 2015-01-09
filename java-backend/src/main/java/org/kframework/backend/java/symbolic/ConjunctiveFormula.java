package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;

import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Created by andrei on 12/8/14.
 */
public class ConjunctiveFormula extends Term {

    private final Substitution<Variable, Term> substitution;
    private final PersistentUniqueList<Equality> equalities;
    private final PersistentUniqueList<DisjunctiveFormula> disjunctions;

    private final TruthValue truthValue;

    private final TermContext context;

    public ConjunctiveFormula(ConjunctiveFormula formula) {
        this(formula.substitution,
             formula.equalities,
             formula.disjunctions,
             formula.truthValue,
             formula.context);
    }

    public ConjunctiveFormula(
            Substitution<Variable, Term> substitution,
            PersistentUniqueList<Equality> equalities,
            PersistentUniqueList<DisjunctiveFormula> disjunctions,
            TruthValue truthValue, TermContext context) {
        super(Kind.KITEM);

        this.substitution = substitution;
        this.equalities = equalities;
        this.disjunctions = disjunctions;
        this.truthValue = truthValue;
        this.context = context;
    }

    public Substitution<Variable, Term> substitution() {
        return substitution;
    }

    public PersistentUniqueList<Equality> equalities() {
        return equalities;
    }

    public PersistentUniqueList<DisjunctiveFormula> disjunctions() {
        return disjunctions;
    }

    public ConjunctiveFormula addAndSimplify(Object term) {
        return add(term).simplify();
    }

    public ConjunctiveFormula add(ConjunctiveFormula conjunction) {
        return add(conjunction.substitution)
                .addAll(conjunction.equalities)
                .addAll(conjunction.disjunctions);
    }

    public ConjunctiveFormula add(Substitution<Variable, Term> substitution) {
        return addAll(substitution.equalities(context));
    }

    public ConjunctiveFormula add(Equality equality) {
        return new ConjunctiveFormula(
                substitution,
                equalities.plus(equality),
                disjunctions,
                truthValue,
                context);
    }

    public ConjunctiveFormula add(DisjunctiveFormula disjunction) {
        return new ConjunctiveFormula(
                substitution,
                equalities,
                disjunctions.plus(disjunction),
                truthValue,
                context);
    }

    @SuppressWarnings("unchecked")
    public ConjunctiveFormula add(Object term) {
        if (term instanceof ConjunctiveFormula) {
            return add((ConjunctiveFormula) term);
        } else if (term instanceof Substitution) {
            return add((Substitution) term);
        } else if (term instanceof Equality) {
            return add((Equality) term);
        } else if (term instanceof DisjunctiveFormula) {
            return add((DisjunctiveFormula) term);
        } else {
            assert false : "invalid argument found: " + term;
            return null;
        }
    }

    public ConjunctiveFormula addAll(Iterable<? extends Object> terms) {
        ConjunctiveFormula result = this;
        for (Object term : terms) {
            result = result.add(term);
            if (result == null) {
                return null;
            }
        }
        return result;
    }

    /**
     * Simplifies this conjunctive formula as much as possible.
     * Decomposes equalities by using unification.
     */
    public ConjunctiveFormula simplify() {
        Substitution<Variable, Term> substitution = this.substitution;
        PersistentUniqueList<Equality> equalities = this.equalities;
        PersistentUniqueList<DisjunctiveFormula> disjunctions = this.disjunctions;

        boolean change;
        do {
            change = false;
            PersistentUniqueList<Equality> pendingEqualities = PersistentUniqueList.empty();
            for (int i = 0; i < equalities.size(); ++i) {
                Equality equality = equalities.get(i);
                Term leftHandSide = equality.leftHandSide().substituteAndEvaluate(substitution, context);
                Term rightHandSide = equality.rightHandSide().substituteAndEvaluate(substitution, context);
                equality = new Equality(leftHandSide, rightHandSide, context);
                if (equality.isTrue()) {
                    // delete
                } else if (equality.truthValue() == TruthValue.FALSE) {
                    // conflict
                    return new ConjunctiveFormula(
                            substitution,
                            equalities,
                            disjunctions,
                            TruthValue.FALSE,
                            context);
                } else {
                    if (equality.isSimplifiableByCurrentAlgorithm()) {
                        // (decompose + conflict)*
                        SymbolicUnifier unifier = new SymbolicUnifier(context);
                        if (!unifier.symbolicUnify(leftHandSide, rightHandSide)) {
                            return new ConjunctiveFormula(
                                    substitution,
                                    equalities,
                                    disjunctions,
                                    TruthValue.FALSE,
                                    context);
                        }
                        // TODO(AndreiS): add the entire conjunction (with substitution and disjunctions)
                        equalities.plusAll(i + 1, unifier.constraint().equalities());
                    } else if (leftHandSide instanceof Variable
                            && !rightHandSide.variableSet().contains(leftHandSide)) {
                        // eliminate
                        substitution = Substitution.composeAndEvaluate(
                                substitution,
                                Substitution.singleton((Variable) leftHandSide, rightHandSide),
                                context);
                        change = true;
                        if (substitution.isFalse(context)) {
                            return new ConjunctiveFormula(
                                    substitution,
                                    equalities,
                                    disjunctions,
                                    TruthValue.FALSE,
                                    context);
                        }
                    } else if (rightHandSide instanceof Variable
                            && !leftHandSide.variableSet().contains(rightHandSide)) {
                        // swap + eliminate
                        substitution = Substitution.composeAndEvaluate(
                                substitution,
                                Substitution.singleton((Variable) rightHandSide, leftHandSide),
                                context);
                        change = true;
                        if (substitution.isFalse(context)) {
                            return new ConjunctiveFormula(
                                    substitution,
                                    equalities,
                                    disjunctions,
                                    TruthValue.FALSE,
                                    context);
                        }
                    } else if (leftHandSide instanceof Variable
                            && rightHandSide.isNormal()
                            && rightHandSide.variableSet().contains(leftHandSide)) {
                        return new ConjunctiveFormula(
                                substitution,
                                equalities,
                                disjunctions,
                                TruthValue.FALSE,
                                context);
                    } else if (rightHandSide instanceof Variable
                            && leftHandSide.isNormal()
                            && leftHandSide.variableSet().contains(rightHandSide)) {
                        return new ConjunctiveFormula(
                                substitution,
                                equalities,
                                disjunctions,
                                TruthValue.FALSE,
                                context);
                    } else {
                        // unsimplified equation
                        pendingEqualities.add(equality);
                    }
                }
            }
            equalities = pendingEqualities;
        } while(change);

        return new ConjunctiveFormula(
                substitution,
                equalities,
                disjunctions,
                truthValue,
                context);
    }

    public DisjunctiveFormula getDisjunctiveNormalForm() {
        if (disjunctions.isEmpty()) {
            return new DisjunctiveFormula(PersistentUniqueList.singleton(this));
        }

        ConjunctiveFormula result = new ConjunctiveFormula(
                substitution,
                equalities,
                PersistentUniqueList.empty(),
                truthValue,
                context);

        List<Set<ConjunctiveFormula>> collect = disjunctions.stream()
                .map(disjunction -> ImmutableSet.<ConjunctiveFormula>copyOf(disjunction.conjunctions()))
                .collect(Collectors.toList());
        List<ConjunctiveFormula> collect1 = Sets.cartesianProduct(collect).stream()
                .map(result::addAll)
                .collect(Collectors.toList());

        return new DisjunctiveFormula(PersistentUniqueList.from(collect1));
    }

    @Override
    public boolean isExactSort() {
        return true;
    }

    @Override
    public boolean isSymbolic() {
        return true;
    }

    @Override
    public Sort sort() {
        return Sort.BOOL;
    }

    @Override
    protected boolean computeMutability() {
        return false;
    }

    @Override
    protected int computeHash() {
        int hashCode = 1;
        hashCode = hashCode * Utils.HASH_PRIME + substitution.hashCode();
        hashCode = hashCode * Utils.HASH_PRIME + equalities.hashCode();
        return hashCode;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ConjunctiveFormula)) {
            return false;
        }

        ConjunctiveFormula conjunction = (ConjunctiveFormula) object;
        return substitution.equals(conjunction.substitution)
                && equalities.equals(conjunction.equalities)
                && disjunctions.equals(conjunction.disjunctions);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {

    }

    @Override
    public void accept(Unifier unifier, Term pattern) {

    }

    @Override
    public void accept(Visitor visitor) {

    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return null;
    }
}
