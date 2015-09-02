// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Table;

import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.*;
import org.kframework.utils.errorsystem.KEMException;

import java.util.*;


/**
 * Substitutes user-level variables with terms according to a given substitution map.
 *
 * @author TraianSF
 */
public class UserSubstitutionTransformer extends PrePostTransformer {

    private final Map<Term, Term> substitution;
    private final Set<Term> unboundedVars;

    public static Term userSubstitution(Map<Term, Term> substitution, Term term, TermContext context) {
        if (substitution.isEmpty()) return term;
        for (Term var : substitution.keySet()) {
            if (!context.definition().subsorts().isSubsortedEq(Sort.VARIABLE, var.sort())) {
                throw KEMException.criticalError("All keys in substitution should be variables, found " + var + " of sort " + var.sort());
            }
        }
        UserSubstitutionTransformer transformer = new UserSubstitutionTransformer(substitution, context);
        return (Term) term.accept(transformer);
    }


    public UserSubstitutionTransformer(Map<Term, Term> substitution, TermContext context) {
        super(context);
        this.substitution = substitution;
        unboundedVars = new HashSet<>();
        for (Map.Entry<Term, Term> substPair : substitution.entrySet()) {
            Set<Term> unboundedVars1 = UnboundedVariablesCollector.getUnboundedVars(substPair.getValue(), context);
            unboundedVars1.remove(substPair.getKey());
            unboundedVars.addAll(unboundedVars1);
        }

        preTransformer.addTransformer(new BinderSubstitution(context));
        preTransformer.addTransformer(new LocalSubstitutionTransformer());
    }

    /**
     * Local transformer that performs the actual substitution of variables.
     */
    private class LocalSubstitutionTransformer extends LocalTransformer {

        @Override
        public ASTNode transform(Term variable) {
            Term replacement = substitution.get(variable);
            if (replacement != null) {
                return new DoneTransforming(replacement);
            } else {
                return variable;
            }
        }
    }

     private class BinderSubstitution extends LocalTransformer {
        public BinderSubstitution(TermContext context) {
            super(context);
        }

        @Override
        public ASTNode transform(KItem kItem) {
            // TODO(AndreiS): fix binder when dealing with KLabel variables and non-concrete KLists
            if (!(kItem.kLabel() instanceof KLabel) || !(kItem.kList() instanceof KList)) {
                return super.transform(kItem);
            }

            KLabel kLabel = (KLabel) kItem.kLabel();
            KList kList = (KList) kItem.kList();
            if (kLabel instanceof KLabelConstant) {
                KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
                if (kLabelConstant.isBinder()) {  // if label is a binder rename all bound variables
                    Multimap<Integer, Integer> binderMap =  kLabelConstant.getBinderMap();
                    //get fresh variables for those in danger of capturing other variables
                    Table<Integer, Term, Term> freshSubstitution = getFreshSubstitution(kList, binderMap);
                    // We link positions in which the renamed variables are bound to their binding variable position
                    Multimap<Integer, Integer> backBinding = HashMultimap.create();
                    for (int keyIndex : freshSubstitution.rowKeySet()) {
                        backBinding.put(keyIndex, keyIndex);
                        for (Integer valueIndex : binderMap.get(keyIndex)) {
                            backBinding.put(valueIndex, keyIndex);
                        }
                    }
                    List<Term> termList = new ArrayList<>();
                    termList.addAll(kList.getContents());
                    for (int idx = 0; idx < termList.size(); idx++) {
                        //each term in the list will be applied a new substitution derived from the original one
                        Map<Term, Term> newSubstitution = new HashMap<>(substitution);
                        if (backBinding.containsKey(idx)) { // if some variables are renamed for this position
                            for (Integer boundPosition : backBinding.get(idx)) { // for all positions which bind variables in this term
                                for (Term variable :  kList.get(boundPosition).userVariableSet(context)) {
                                    // for all variables bound at this position
                                    if (unboundedVars.contains(variable)) { // if they are potentially capturing
                                        // update the new substitution to rename this variable
                                        newSubstitution.put(variable, freshSubstitution.get(boundPosition, variable));
                                    } else if (substitution.containsKey(variable)) { // if this is a substituted variable
                                        // remove it from the new substitution as there will not be any free occurrences
                                        newSubstitution.remove(variable);
                                    }
                                }
                            }
                        }
                        Term bindingExp = termList.get(idx);
                        Term resultBindingExp = userSubstitution(newSubstitution, bindingExp, context);
                        termList.set(idx, resultBindingExp);
                    }

                    kItem = KItem.of(kLabel, KList.concatenate(termList), context,
                                kItem.getSource(), kItem.getLocation());
                    return new DoneTransforming(kItem);
                }
            }
            return super.transform(kItem);
        }

         /**
          * Given a binder term's binderMap and lsit of direct subterms, figures out which of the variables bound by this
          * binder are problematic w.r.t. the substitution and computes a substitution yielding fresh symbols for
          * those variables.
          * @param termList  the list of direct subterms of a binder
          * @param binderMap the multimap of bound positions -> binding position of a binder {@link org.kframework.kil.Production#getBinderMap()}
          * @return A table of (idx,var,rvar) tuples meaning tha at position idx in the list, variable var is replaced by rvar
          */
         private Table<Integer, Term, Term> getFreshSubstitution(KList termList, Multimap<Integer, Integer> binderMap) {
             Table<Integer, Term, Term> freshSubstitution = HashBasedTable.create();
             for (int keyIndex : binderMap.keySet()) {
                 // retrieve all variables in the pattern at this position
                 Set<Term> boundVars = termList.get(keyIndex).userVariableSet(context);
                 Set<Term> capturingVars = new HashSet<>();
                 for (Term boundVar : boundVars) {
                     // all variables which are free in the substitution values or are bound by the substitution are problematic
                     if (unboundedVars.contains(boundVar) || substitution.containsKey(boundVar)) {
                         capturingVars.add(boundVar);
                     }
                 }
                 for (Term boundVar : capturingVars) {
                     Term freshBoundVar = FreshOperations.fresh(boundVar.sort(), context);
                     freshSubstitution.put(keyIndex, boundVar, freshBoundVar);
                 }
             }
             return freshSubstitution;
         }
     }

}
