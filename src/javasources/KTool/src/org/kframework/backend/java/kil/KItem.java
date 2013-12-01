package org.kframework.backend.java.kil;

import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.SortMembership;
import org.kframework.backend.java.symbolic.BuiltinFunction;
import org.kframework.backend.java.symbolic.SymbolicConstraint;
import org.kframework.backend.java.symbolic.Unifier;
import org.kframework.backend.java.symbolic.Transformer;
import org.kframework.backend.java.symbolic.Utils;
import org.kframework.backend.java.symbolic.Visitor;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Production;
import org.kframework.kil.loader.Context;
import org.kframework.utils.general.GlobalSettings;

import com.google.common.collect.Sets;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * A K application.
 *
 * @author AndreiS
 */
public class KItem extends Term implements Sorted {

    private final KLabel kLabel;
    private final KList kList;
    private final String sort;
    
    /**
     * Valid only if {@code kLabel} is a constructor. Must contain a sort
     * which is subsorted or equal to {@code sort} when it is valid.
     */
    private final Set<String> possibleMinimalSorts;

    public KItem(KLabel kLabel, KList kList, Context context) {
        super(Kind.KITEM);

        this.kLabel = kLabel;
        this.kList = kList;
        Set<String> possibleMinimalSorts = kLabel.isConstructor() ? new HashSet<String>() : null;

        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            List<Production> productions = kLabelConstant.productions();
            if (productions.size() != 0) {
                Set<String> sorts = new HashSet<String>();

                for (Production production : productions) {
                    boolean mustMatch = true;
                    boolean mayMatch = true;

                    /* check if the production can match this KItem */
                    if (!kList.hasFrame() && kList.size() == production.getArity()) {
                        for (int i = 0; i < kList.size(); ++i) {
                            String childSort;
                            Term childTerm = kList.get(i);

                            if (childTerm instanceof Sorted) {
                                childSort = ((Sorted) childTerm).sort();
                            } else {
                                childSort = kind.toString();
                            }

                            if (!context.isSubsortedEq(production.getChildSort(i), childSort)) {
                                mustMatch = false;

                                if (kLabel.isConstructor()) {
                                    if (childTerm instanceof Variable) {
                                        Set<String> set = Sets.newHashSet(production.getChildSort(i), ((Variable) childTerm).sort());
                                        if (context.getCommonSubsorts(set).isEmpty()) {
                                            mayMatch = false;
                                        }
                                    } else if (childTerm instanceof KItem) {
                                        mayMatch = false;
                                        if (((KItem) childTerm).kLabel.isConstructor()) {
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
                    
                    if (mayMatch && kLabel.isConstructor()) {
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
                if (listSorts != null && !kList.hasFrame() && kList.size() == 0) {
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
     * @param context a term context
     * @return the evaluated result on success, or this {@code KItem} otherwise
     */
    public Term evaluateFunction(TermContext context) {
        Definition definition = context.definition();
        if (!(kLabel instanceof KLabelConstant)) {
            return this;
        }
        KLabelConstant kLabelConstant = (KLabelConstant) kLabel;

        /* evaluate a sort membership predicate */
        if (kLabelConstant.label().startsWith("is") && kList.getItems().size() == 1
                && kList.getItems().get(0) instanceof Sorted) {
            return SortMembership.check(this);
        }

        /* apply rules for user defined functions */
        if (!definition.functionRules().get((KLabelConstant) kLabel).isEmpty()) {
            ConstrainedTerm constrainedTerm = new ConstrainedTerm(kList, context);

            // TODO(YilongL): There are at least two missing features here:
            // 1) consider applying rules with attribute [owise] only after
            // no other rules can be applied;
            // 2) check the determinism of the function definition across
            // multiple rules; currently the determinism is only check w.r.t
            // one rule
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

                assert solutions.size() <= 1 : "function definition is not deterministic";

                if (solutions.isEmpty()) {
                    continue;
                }

                SymbolicConstraint constraint = solutions.iterator().next();

                if (!constraint.isSubstitution()) {
                    continue;
                }

                constraint.orientSubstitution(rule.variableSet(), context);

                /* rename rule variables in the constraints */
                Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

                Term result = rule.rightHandSide();
                /* rename rule variables in the rule RHS */
                result = result.substitute(freshSubstitution, context);
                /* apply the constraints substitution on the rule RHS */
                result = result.substitute(constraint.substitution(), context);
                /* evaluate pending functions in the rule RHS */
                result = result.evaluate(context);
                /* eliminate anonymous variables */
                constraint.eliminateAnonymousVariables();

                return result;
            }
        }

        if (!BuiltinFunction.isBuiltinKLabel(kLabelConstant)) {
            return this;
        }

        /* this can be removed, and IllegalArgumentException would be thrown below */
        //for (Term term : kList.getItems()) {
        //    if (!term.isGround()) {
        //        return this;
        //    }
        //}

        try {
            Term[] arguments = kList.getItems().toArray(new Term[kList.getItems().size()]);
            Term result = BuiltinFunction.invoke(context, kLabelConstant, arguments);
            if (result == null) result = this;
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

    public KLabel kLabel() {
        return kLabel;
    }

    public KList kList() {
        return kList;
    }

    /**
     * A {@code KItem} cannot be further decomposed in a unification task if and
     * only if its {@code KLabel} represents a function.
     */
    @Override
    public boolean isSymbolic() {
        return kLabel.isFunction();
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

}
