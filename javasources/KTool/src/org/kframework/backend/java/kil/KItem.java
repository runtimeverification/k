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
import org.kframework.krun.K;
import org.kframework.utils.general.GlobalSettings;

import java.util.Collection;
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

    public KItem(KLabel kLabel, KList kList, Context context) {
        super(Kind.KITEM);

        this.kLabel = kLabel;
        this.kList = kList;

        if (kLabel instanceof KLabelConstant) {
            KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
            List<Production> productions = kLabelConstant.productions();
            if (productions.size() != 0) {
                Set<String> sorts = new HashSet<String>();

            label:
                for (Production production : productions) {
                    if (!kList.hasFrame() && kList.size() == production.getArity()) {
                        for (int i = 0; i < kList.size(); ++i) {
                            String childSort;
                            if (kList.get(i) instanceof Sorted) {
                                childSort = ((Sorted) kList.get(i)).sort();
                            } else {
                                childSort = kind.toString();
                            }

                            if (!context.isSubsortedEq(production.getChildSort(i), childSort)) {
                                continue label;
                            }
                        }

                        sorts.add(production.getSort());
                    }
                }

                if (!sorts.isEmpty()) {
                    if (sorts.size() == 1) {
                        sort = sorts.iterator().next();
                    } else {
                        sort = context.getGLBSort(sorts);
                    }
                } else {
                    sort = kind.toString();
                }
            } else {
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
        } else {
            sort = kind.toString();
        }
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

            for (Rule rule : definition.functionRules().get((KLabelConstant) kLabel)) {
                SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(context);
                leftHandSideConstraint.addAll(rule.condition());
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
        } catch (IllegalAccessException e) {
            //e.printStackTrace();
        } catch (IllegalArgumentException e) {
            //e.printStackTrace();
            if (K.do_testgen) {
                for (Term arg : kList.getItems()) {
                    if (arg instanceof Variable) {
                        Variable evalResult = DomainConstrainedVariable
                                .getFreshContrainedVariable(sort, this);
                        // TODO(YilongL): when to check sat?
                        return evalResult;
                        }
                    }
                assert false; // shouldn't be here
            }
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
