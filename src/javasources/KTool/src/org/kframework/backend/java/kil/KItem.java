package org.kframework.backend.java.kil;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.kil.ConstrainedTerm.UnificationType;
import org.kframework.backend.java.symbolic.BuiltinFunction;
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
public class KItem extends Term implements Sorted {

    private final Term kLabel;
    private final Term kList;
    private final String sort;
    
    /**
     * Valid only if {@code kLabel} is a constructor. Must contain a sort
     * which is subsorted or equal to {@code sort} when it is valid.
     */
    private final Set<String> possibleMinimalSorts;

    public KItem(Term kLabel, Term kList, Context context) {
        super(Kind.KITEM);

        this.kLabel = kLabel;
        this.kList = kList;

        Set<String> possibleMinimalSorts = null;
        if (kLabel instanceof KLabelConstant && kList instanceof KList) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            if (kLabelConstant.isConstructor()) {
                possibleMinimalSorts = new HashSet<>();
            }

            List<Production> productions = kLabelConstant.productions();
            if (productions.size() != 0) {
                Set<String> sorts = new HashSet<String>();

                for (Production production : productions) {
                    boolean mustMatch = true;
                    boolean mayMatch = true;

                    /* check if the production can match this KItem */
                    // TODO(YilongL): I guess the only point of this check is to
                    // distinguish between overloaded productions, however, once
                    // we have passed the front-end the arguments of a K label
                    // can violate its original declaration, therefore the code
                    // below would need to be revised
                    if (!((KList) kList).hasFrame() && ((KList) kList).size() == production.getArity()) {
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

                            if (childTerm instanceof Sorted) {
                                childSort = ((Sorted) childTerm).sort();
                            } else {
                                childSort = kind.toString();
                            }

                            if (!context.isSubsortedEq(production.getChildSort(i), childSort)) {
                                mustMatch = false;

                                if (kLabelConstant.isConstructor()) {
                                    if (childTerm instanceof Variable) {
                                        Set<String> set = Sets.newHashSet(production.getChildSort(i), ((Variable) childTerm).sort());
                                        if (context.getCommonSubsorts(set).isEmpty()) {
                                            mayMatch = false;
                                        }
                                    } else if (childTerm instanceof KItem) {
                                        mayMatch = false;
                                        if (((KItem) childTerm).kLabel instanceof KLabel
                                                && ((KLabel) ((KItem) childTerm).kLabel).isConstructor()) {
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

                if (!sorts.isEmpty()) { /* one or more productions match this KItem */
                    if (sorts.size() == 1) {
                        sort = sorts.iterator().next();
                    } else {
                        // TODO(YilongL): Why set the sort of the KItem to be
                        // the GLB of the sorts of all matching productions?
                        // What if there is no GLB?
                        sort = context.getGLBSort(sorts);
                    }
                } else {    /* no production matches this KItem */
                    sort = kind.toString();
                }
            } else {    /* productions.size() == 0 */
                /* a list terminator does not have conses */
                Set<String> listSorts = context.listLabels.get(kLabelConstant.label());
                if (listSorts != null && !((KList) kList).hasFrame() && ((KList) kList).size() == 0) {
                    if (listSorts.size() == 1) {
                        sort = listSorts.iterator().next();
                    } else {
                        sort = context.getGLBSort(listSorts);
                    }
                } else {
                    sort = kind.toString();
                }
            }
        } else {    /* not a KLabelConstant */
            sort = kind.toString();
        }
        
        
        if (possibleMinimalSorts != null) {
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
//        System.out.printf("KItem = %s, sort = %s, possibleMinimalSorts = %s\n", this, sort, possibleMinimalSorts);
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
        Definition definition = context.definition();
        KLabelConstant kLabelConstant = null; // the function symbol
        Term[] arguments = null;

        if (kLabel.getClass().equals(KLabelInjection.class)) {
            /*
             * if the kLabel is a KLabelInjection and the term injected inside
             * is a TermCons, then this TermCons must be a function whose return
             * value is a KLabel or a KList
             */
            Term term = ((KLabelInjection) kLabel).term();
            if (term instanceof TermCons) {
                TermCons termCons = (TermCons) term;
                String kLabel = termCons.production().getAttribute("klabel");
                kLabelConstant = KLabelConstant.of(kLabel, definition.context());
                arguments = termCons.contents().toArray(new Term[termCons.contents().size()]);
            } else {
                return this;
            }
        } else {
            if (!(kLabel instanceof KLabelConstant)) {
                return this;
            }
            kLabelConstant = (KLabelConstant) kLabel;

            if (!(kList instanceof  KList)) {
                return this;
            }
            arguments = ((KList) kList).getContents().toArray(new Term[((KList) kList).getContents().size()]);

            /* evaluate a sort membership predicate */
            // TODO(YilongL): maybe we can move sort membership evaluation after
            // applying user-defined rules to allow the users to provide their
            // own rules for checking sort membership
            if (kLabelConstant.label().startsWith("is") && ((KList) kList).getContents().size() == 1
                    && ((KList) kList).getContents().get(0) instanceof Sorted) {
                return SortMembership.check(this, context.definition().context());
            }

            /* apply rules for user defined functions */
            if (!definition.functionRules().get((KLabelConstant) kLabel).isEmpty()) {
                ConstrainedTerm constrainedTerm = new ConstrainedTerm(kList, context);

                // TODO(YilongL): consider applying rules with attribute [owise]
                // only after no other rules can be applied
                Term result = null;
                for (Rule rule : definition.functionRules().get((KLabelConstant) kLabel)) {
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
                        if (!(constrainedTerm.getTypeOfUnification() == UnificationType.PatternMatching && solution.isSubstitution())) {
                            continue;
                        }
                    } else if (K.do_concrete_exec) {
                        assert solutions.size() <= 1 : "function definition is not deterministic";
                        assert constrainedTerm.getTypeOfUnification() == UnificationType.PatternMatching : "the result of unification between:"
                                + constrainedTerm.term()
                                + " (the ground subject term) and "
                                + leftHandSide.term()
                                + " (the pattern) should be a substitution";
                        assert solution.isSubstitution() : "the solution shall not contain pending functions but found:\n" + solution.equalities();
                    }
                    
                    solution.orientSubstitution(rule.leftHandSide().variableSet(), context);

                    /* rename rule variables in the constraints */
                    Map<Variable, Variable> freshSubstitution = solution.rename(rule.variableSet());

                    Term rightHandSide = rule.rightHandSide();
                    /* rename rule variables in the rule RHS */
                    rightHandSide = rightHandSide.substitute(freshSubstitution, context);
                    /* apply the constraints substitution on the rule RHS */
                    rightHandSide = rightHandSide.substituteAndEvaluate(solution.substitution(), context);
                    /* eliminate anonymous variables */
                    solution.eliminateAnonymousVariables();

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

                    if (K.do_concrete_exec) {
                        assert result == null : "function definition is not deterministic";
                    }
                    result = rightHandSide;
                }

                if (result != null) {
                    return result;
                }
            }
        }

        if (!BuiltinFunction.isBuiltinKLabel(kLabelConstant)) {
            return this;
        }

        try {
            Term result = BuiltinFunction.invoke(context, kLabelConstant, arguments);
//            System.err.println(this + " => " + result);
            if (result == null) {
                result = this;
            } else if (result instanceof KLabel) {
                result = new KItem(new KLabelInjection(result), new KList(), definition.context());
            } else if (result instanceof KList) {
                // TODO: handle the case that KList as return value
                assert false : "YilongL: Fix it; handle the case where the return value is a KList";
            }
            return result;
        } catch (IllegalAccessException | IllegalArgumentException e) {
            //e.printStackTrace();
        } catch (RuntimeException e) {
            if (GlobalSettings.verbose) {
                System.err.println("Ignored exception thrown by hook " + kLabelConstant + " : ");
                e.printStackTrace();
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

    /**
     * A {@code KItem} cannot be further decomposed in a unification task if and
     * only if its {@code KLabel} represents a function.
     */
    @Override
    public boolean isSymbolic() {
        return !(kLabel instanceof KLabel) || ((KLabel) kLabel).isFunction();
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
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + kLabel.hashCode();
        hash = hash * Utils.HASH_PRIME + kList.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return kLabel + "(" + kList.toString() + ")";
    }

    @Override
    public void accept(Unifier unifier, Term patten) {
        unifier.unify(this, patten);
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
