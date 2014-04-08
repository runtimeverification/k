package org.kframework.backend.java.kil;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.Matcher;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.backend.java.util.Utils;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.krun.K;
import org.kframework.utils.general.GlobalSettings;

import com.google.common.collect.Sets;


/**
 * Represents a K application which applies a {@link KLabel} to a {@link KList}.
 * Or in the usual syntax of K, it can be defined as the following:
 * <p>
 * <blockquote>
 *
 * <pre>
 * syntax KItem ::= KLabel "(" KList ")"
 * </pre>
 *
 * </blockquote>
 * <p>
 *
 * @author AndreiS
 */
@SuppressWarnings("serial")
public final class KItem extends Term {

    private final Term kLabel;
    private final Term kList;
    private final boolean isExactSort;
    private final String sort;
    private Boolean evaluable = null;

    /**
     * Valid only if {@code kLabel} is a constructor. Must contain a sort
     * which is subsorted or equal to {@code sort} when it is valid.
     */
    private final Set<String> possibleMinimalSorts;

    public KItem(Term kLabel, Term kList, TermContext termContext) {
        super(Kind.KITEM);

        this.kLabel = kLabel;
        this.kList = kList;

        Definition definition = termContext.definition();
        Context context = definition.context();

        if (kLabel instanceof KLabelConstant && kList instanceof KList
                && !((KList) kList).hasFrame()) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

            Set<String> sorts = new HashSet<>();
            Set<String> possibleMinimalSorts = new HashSet<>();

            if (!K.do_kompilation) {
                /**
                 * Sort checks in the Java engine are not implemented as
                 * rewrite rules, so we need to precompute the sort of
                 * terms. However, right now, we also want to allow users
                 * to provide user-defined sort predicate rules, e.g.
                 *      ``rule isVal(cons V:Val) => true''
                 * to express the same meaning as overloaded productions
                 * which are not allowed to write in the current front-end.
                 */
                /* YilongL: user-defined sort predicate rules are interpreted as overloaded productions at runtime */
                for (KLabelConstant sortPredLabel : definition.sortPredLabels()) {
                    Collection<Rule> rules = definition.functionRules().get(sortPredLabel);
                    for (Rule rule : rules) {
                        KItem predArg = rule.getSortPredArgument();
                        if (MetaK.matchable(kLabel, predArg.kLabel(), termContext).equals(BoolToken.TRUE)
                                && MetaK.matchable(kList, predArg.kList(), termContext).equals(BoolToken.TRUE)) {
                            sorts.add(rule.getPredSort());
                            if (kLabelConstant.isConstructor()) {
                                possibleMinimalSorts.add(rule.getPredSort());
                            }
                        } else if (MetaK.matchable(kLabel, predArg.kLabel(), termContext).equals(BoolToken.TRUE)
                                && MetaK.unifiable(kList, predArg.kList(), termContext).equals(BoolToken.TRUE)) {
                            if (kLabelConstant.isConstructor()) {
                                possibleMinimalSorts.add(rule.getPredSort());
                            }
                        }
                    }
                }
            }

            List<Production> productions = kLabelConstant.productions();
            if (productions.size() != 0) {
                for (Production production : productions) {
                    boolean mustMatch = true;
                    boolean mayMatch = true;

                    /* check if the production can match this KItem */
                    // TODO(YilongL): I guess the only point of this check is to
                    // distinguish between overloaded productions, however, once
                    // we have passed the front-end the arguments of a K label
                    // can violate its original declaration, therefore the code
                    // below would need to be revised
                    if (((KList) kList).size() == production.getArity()) {
                        for (int i = 0; i < ((KList) kList).size(); ++i) {
                            String childSort;
                            Term childTerm = ((KList) kList).get(i);
                            /* extract the real injected term when necessary */
                            if (childTerm instanceof KItem){
                                KItem kItem = (KItem) childTerm;
                                if (isInjectionWrapper(kItem)) {
                                    childTerm = extractInjectedTerm(kItem);
                                }
                            }
                            childSort = childTerm.sort();

                            if (!context.isSubsortedEq(production.getChildSort(i), childSort)) {
                                mustMatch = false;

                                if (kLabelConstant.isConstructor()) {
                                    if (childTerm instanceof Variable) {
                                        Set<String> set = Sets.newHashSet(production.getChildSort(i), childTerm.sort());
                                        if (context.getCommonSubsorts(set).isEmpty()) {
                                            mayMatch = false;
                                        }
                                    } else if (childTerm instanceof KItem) {
                                        mayMatch = false;
                                        if (((KItem) childTerm).possibleMinimalSorts() != null) {
                                            for (String pms : ((KItem) childTerm).possibleMinimalSorts()) {
                                                if (context.isSubsortedEq(production.getChildSort(i), pms)) {
                                                    mayMatch = true;
                                                    break;
                                                }
                                            }
                                        }
                                    } else { // e.g., childTerm is a HOLE
                                        mayMatch = false;
                                    }

                                    if (!mayMatch) {
                                        // mayMatch == false => mustMatch == false
                                        break;
                                    }
                                }
                            }
                        }
                    }

                    if (mustMatch) {
                        sorts.add(production.getSort());
                    }

                    if (mayMatch && kLabelConstant.isConstructor()) {
                        possibleMinimalSorts.add(production.getSort());
                    }
                }
            } else {    /* productions.size() == 0 */
                /* a list terminator does not have conses */
                Set<String> listSorts = context.listLabels.get(kLabelConstant.label());
                if (listSorts != null && ((KList) kList).size() == 0) {
                    sorts.addAll(listSorts);
                }
            }

            /* no production matches this KItem */
            if (sorts.isEmpty()) {
                sorts.add(kind.toString());
            }

            sort = context.getGLBSort(sorts);
            assert sort != null && !sort.equals("null"):
                    "The greatest lower bound (GLB) of sorts " + sorts + "doesn't exist!";
            /* this sort is exact if the KLabel is a constructor and there are no possible smaller sorts */
            isExactSort = kLabelConstant.isConstructor() && sorts.containsAll(possibleMinimalSorts);

            if (kLabelConstant.isConstructor()) {
                possibleMinimalSorts.add(sort);
                Set<String> nonMinimalSorts = new HashSet<String>();
                for (String s1 : possibleMinimalSorts) {
                    for (String s2 : possibleMinimalSorts) {
                        if (context.isSubsorted(s1, s2)) {
                            nonMinimalSorts.add(s1);
                        }
                    }
                }
                possibleMinimalSorts.removeAll(nonMinimalSorts);
                this.possibleMinimalSorts = possibleMinimalSorts;
            } else {
                this.possibleMinimalSorts = null;
            }
        } else {    /* not a KLabelConstant or the kList contains a frame variable */
            sort = kind.toString();
            isExactSort = false;
            possibleMinimalSorts = null;
        }
    }

    public boolean isEvaluable(TermContext context) {
        if (evaluable != null) {
            return evaluable;
        }

        evaluable = false;
        if (!(kLabel instanceof KLabelConstant)) {
            return false;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        if (!(kList instanceof KList)) {
            return false;
        }

        if (kLabelConstant.label().startsWith("is")
                || !context.definition().functionRules().get(kLabelConstant).isEmpty()
                || BuiltinFunction.isBuiltinKLabel(kLabelConstant)) {
            evaluable = true;
        }
        return evaluable;
    }

    /**
     * Evaluates this {@code KItem} if it is a predicate or function
     *
     * @param constraint
     *            the existing symbolic constraint that needs to be taken into
     *            consideration when evaluating this function
     * @param context
     *            a term context
     * @return the evaluated result on success, or this {@code KItem} otherwise
     */
    public Term evaluateFunction(SymbolicConstraint constraint, TermContext context) {
        if (!isEvaluable(context)) {
            return this;
        }

        Definition definition = context.definition();

        if (!(kLabel instanceof KLabelConstant)) {
            return this;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        if (!(kList instanceof KList)) {
            return this;
        }
        KList kList = (KList) this.kList;

        if (BuiltinFunction.isBuiltinKLabel(kLabelConstant)) {
            try {
                Term[] arguments = kList.getContents().toArray(new Term[kList.getContents().size()]);
                Term result = BuiltinFunction.invoke(context, kLabelConstant, arguments);
                if (result != null) {
                    assert result.kind() == Kind.KITEM:
                            "unexpected kind " + result.kind() + " of term " + result + ";"
                            + "expected kind " + Kind.KITEM + " instead";
                    return result;
                }
            } catch (IllegalAccessException | IllegalArgumentException e) {
            } catch (RuntimeException e) {
                if (GlobalSettings.verbose) {
                    System.err.println("Ignored exception thrown by hook " + kLabelConstant + " : ");
                    e.printStackTrace();
                }
            }
        }

        /* evaluate a sort membership predicate */
        // TODO(YilongL): maybe we can move sort membership evaluation after
        // applying user-defined rules to allow the users to provide their
        // own rules for checking sort membership
        if (kLabelConstant.label().startsWith("is") && kList.getContents().size() == 1) {
            Term checkResult = SortMembership.check(this, context.definition().context());
            if (checkResult != this) {
                return checkResult;
            }
        }

        /* apply rules for user defined functions */
        if (!definition.functionRules().get(kLabelConstant).isEmpty()) {
            ConstrainedTerm constrainedTerm = new ConstrainedTerm(kList, context);

            Term result = null;

            /*
             * YilongL: consider applying rules with attribute [owise]
             * only after no other rules can be applied for sure
             */
            boolean mayUseOwiseRule = true;
            LinkedHashSet<Term> owiseResults = new LinkedHashSet<Term>();
            for (Rule rule : definition.functionRules().get(kLabelConstant)) {
                SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(context);
                leftHandSideConstraint.addAll(rule.requires());
                for (Variable variable : rule.freshVariables()) {
                    leftHandSideConstraint.add(variable, IntToken.fresh());
                }

                ConstrainedTerm leftHandSide = new ConstrainedTerm(
                        ((KItem) rule.leftHandSide()).kList,
                        rule.lookups().getSymbolicConstraint(context),
                        leftHandSideConstraint,
                        context);

                Collection<SymbolicConstraint> solutions = constrainedTerm.unify(leftHandSide);
                if (solutions.isEmpty()) {
                    continue;
                }

                SymbolicConstraint solution = solutions.iterator().next();
                if (K.do_kompilation) {
                    assert solutions.size() <= 1 : "function definition is not deterministic";
                    if (!solution.isMatching(leftHandSide)) {
                        mayUseOwiseRule = false;
                        continue;
                    }
                } else if (K.do_concrete_exec) {
                    assert solutions.size() <= 1 : "function definition is not deterministic";
                    assert solution.isMatching(leftHandSide) : "Pattern matching expected in concrete execution mode";
                }

                solution.orientSubstitution(rule.leftHandSide().variableSet());

                Term rightHandSide = rule.rightHandSide();

                if (rule.hasUnboundedVariables()) {
                    /* rename rule variables in the constraints */
                    Map<Variable, Variable> freshSubstitution = solution.rename(rule.variableSet());
                    /* rename rule variables in the rule RHS */
                    result = result.substituteWithBinders(freshSubstitution, context);
                }
                /* apply the constraints substitution on the rule RHS */
                rightHandSide = rightHandSide.substituteAndEvaluate(solution.substitution(), context);
                /* eliminate anonymous variables */
                // solution.eliminateAnonymousVariables();

                /* update the constraint */
                if (K.do_kompilation || K.do_concrete_exec) {
                    // in kompilation and concrete execution mode, the
                    // evaluation of user-defined functions will not create
                    // new constraints
                } else if (constraint != null) {
                    throw new RuntimeException(
                            "Fix it; need to find a proper way to update "
                                    + "the constraint without interferring with the "
                                    + "potential ongoing normalization process");
                } else { // constraint == null
                    if (solution.isUnknown() || solution.isFalse()) {
                        throw new RuntimeException(
                                "Fix it; no reference to the symbolic " +
                                "constraint that needs to be updated");
                    }
                }

                if (rule.containsAttribute("owise")) {
                    owiseResults.add(rightHandSide);
                } else {
                    if (K.do_concrete_exec) {
                        assert result == null || result.equals(rightHandSide):
                                "function definition is not deterministic";
                    }
                    result = rightHandSide;
                }

                /*
                 * If the function definitions do not need to be deterministic, try them in order
                 * and apply the first one that matches.
                 */
                if (!K.deterministic_functions && result != null) {
                    return result;
                }
            }

            if (result != null) {
                return result;
            } else if (mayUseOwiseRule && !owiseResults.isEmpty()) {
                assert owiseResults.size() == 1 : "function definition is not deterministic";
                return owiseResults.iterator().next();
            }
        }

        return this;
    }

    public Term kLabel() {
        return kLabel;
    }

    public Term kList() {
        return kList;
    }

    @Override
    public boolean isExactSort() {
        return isExactSort;
    }

    /**
     * A {@code KItem} cannot be further decomposed in a unification task if and
     * only if its {@code KLabel} represents a function.
     */
    @Override
    public boolean isSymbolic() {
        // TODO(AndreiS): handle KLabel variables
        //return !(kLabel instanceof KLabel) || ((KLabel) kLabel).isFunction();
        return kLabel instanceof KLabel && ((KLabel) kLabel).isFunction();
    }

    /**
     * @return a {@code String} representation of the sort of this K application.
     */
    @Override
    public String sort() {
        return sort;
    }

    /**
     * @return a unmodifiable view of the possible minimal sorts of this
     *         {@code KItem} when its {@code KLabel} is a constructor;
     *         otherwise, null;
     */
    public Set<String> possibleMinimalSorts() {
        if (possibleMinimalSorts != null) {
            return Collections.unmodifiableSet(possibleMinimalSorts);
        } else {
            return null;
        }
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof KItem)) {
            return false;
        }

        KItem kItem = (KItem) object;
        return kLabel.equals(kItem.kLabel) && kList.equals(kItem.kList);
    }

    @Override
    public int hashCode() {
        if (hashCode == 0) {
            hashCode = 1;
            hashCode = hashCode * Utils.HASH_PRIME + kLabel.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + kList.hashCode();
            hashCode = hashCode * Utils.HASH_PRIME + sort.hashCode();
        }
        return hashCode;
    }

    @Override
    public String toString() {
        return kLabel + "(" + kList.toString() + ")";
    }

    @Override
    public void accept(Unifier unifier, Term pattern) {
        unifier.unify(this, pattern);
    }

    @Override
    public void accept(Matcher matcher, Term pattern) {
        matcher.match(this, pattern);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

    @Override
    public ASTNode accept(Transformer transformer) {
        return transformer.transform(this);
    }

    /**
     * Checks if the specified KItem is merely used as a wrapper for a non-K
     * term.
     *
     * @param kItem
     *            the specified KItem
     * @return {@code true} if the specified KItem is an injection wrapper;
     *         otherwise, {@code false}
     */
    public static boolean isInjectionWrapper(KItem kItem) {
        return kItem.kLabel.getClass() == KLabelInjection.class && kItem.kList instanceof KList
                && ((KList) kItem.kList).contents.isEmpty();
    }

    /**
     * Extracts the injected non-K term inside the specified KItem.
     *
     * @param kItem
     *            the specified KItem
     * @return the injected term
     */
    public static Term extractInjectedTerm(KItem kItem) {
        assert isInjectionWrapper(kItem);
        return ((KLabelInjection) kItem.kLabel).term();
    }

}
