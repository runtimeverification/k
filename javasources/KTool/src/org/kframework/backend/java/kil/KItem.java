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

import java.util.Collection;
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
            List<Production> productions = ((KLabelConstant) kLabel).productions();
            if (productions.size() == 1) {
                Production production = productions.get(0);
                if (!kList.hasFrame() && kList.size() == production.getArity()) {
                    for (int i = 0; i < kList.size(); ++i) {
                        String childSort;
                        if (kList.get(i) instanceof Sorted) {
                            childSort = ((Sorted) kList.get(i)).sort();
                        } else {
                            childSort = kind.toString();
                        }

                        if (!context.isSubsortedEq(production.getChildSort(i), childSort)) {
                            sort = kind.toString();
                            return;
                        }
                    }
                    sort = production.getSort();
                } else {
                    sort = kind.toString();
                }
            } else {
                /* a list terminator does not have conses */
                Set<String> listSorts = context.listLabels.get(((KLabelConstant) kLabel).label());
                if (listSorts != null) {
                    if (listSorts.size() == 1) {
                        sort = listSorts.iterator().next();
                    } else {
                        sort = context.getLUBSort(listSorts);
                    }
                } else {
                    sort = kind.toString();
                }
            }
        } else {
            sort = kind.toString();
        }
    }

    public Term evaluateFunction(Definition definition) {
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
            ConstrainedTerm constrainedTerm = new ConstrainedTerm(this, definition);

            for (Rule rule : definition.functionRules().get((KLabelConstant) kLabel)) {
                SymbolicConstraint leftHandSideConstraint = new SymbolicConstraint(definition);
                leftHandSideConstraint.addAll(rule.condition());
                for (Variable variable : rule.freshVariables()) {
                    leftHandSideConstraint.add(variable, IntToken.fresh());
                }

                ConstrainedTerm leftHandSide = new ConstrainedTerm(
                        rule.leftHandSide(),
                        rule.lookups(),
                        leftHandSideConstraint);

                Collection<SymbolicConstraint> solutions = constrainedTerm.unify(
                        leftHandSide,
                        definition);

                assert solutions.size() <= 1 : "function definition is not deterministic";

                SymbolicConstraint constraint = solutions.iterator().next();

                if (!constraint.isSubstitution()) {
                    continue;
                }

                /* rename rule variables in the constraints */
                Map<Variable, Variable> freshSubstitution = constraint.rename(rule.variableSet());

                Term result = rule.rightHandSide();
                /* rename rule variables in the rule RHS */
                result = result.substitute(freshSubstitution, definition);
                /* apply the constraints substitution on the rule RHS */
                result = result.substitute(constraint.substitution(), definition);
                /* evaluate pending functions in the rule RHS */
                result = result.evaluate(definition);
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
            return BuiltinFunction.invoke(kLabelConstant, arguments);
        } catch (IllegalAccessException e) {
            //e.printStackTrace();
        } catch (IllegalArgumentException e) {
            //e.printStackTrace();
        } catch (RuntimeException e) {
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
