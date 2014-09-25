// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import org.kframework.backend.java.builtins.FreshOperations;
import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.kil.*;

import java.util.*;
import java.util.List;
import java.util.Map;
import java.util.Set;


/**
 * Substitutes user-level variables with terms according to a given substitution map.
 *
 * @author TraianSF
 */
public class UserSubstitutionTransformer extends PrePostTransformer {

    private final Map<Term, Term> substitution;
    private final Set<Term> unboundedTerms;

    public static Term userSubstitution(Map<Term, Term> substitution, Term term, TermContext context) {
        if (substitution.isEmpty()) return term;
        UserSubstitutionTransformer transformer = new UserSubstitutionTransformer(substitution, context);
        return (Term) term.accept(transformer);
    }


    public UserSubstitutionTransformer(Map<Term, Term> substitution, TermContext context) {
        super(context);
        this.substitution = substitution;
        unboundedTerms = new HashSet<>();
        for (Map.Entry<Term, Term> substPair : substitution.entrySet()) {
            Set<Term> unboundedTerms1 = UnboundedTermsCollector.getUnboundedTerms(substPair.getValue());
            unboundedTerms1.remove(substPair.getKey());
            unboundedTerms.addAll(unboundedTerms1);
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
                    Map<Integer, Term> freshSubstitution = new HashMap<>();
                    Multimap<Integer, Integer> backBinding = HashMultimap.create();
                    Multimap<Integer, Integer> binderMap =  kLabelConstant.getBinderMap();
                    for (Integer keyIndex : binderMap.keySet()) {
                        Term boundVar = kList.get(keyIndex);
                        if (!unboundedTerms.contains(boundVar) && !substitution.containsKey(boundVar)) continue;
                        Term freshBoundVar = FreshOperations.fresh(boundVar.sort(), context);
                        freshSubstitution.put(keyIndex, freshBoundVar);
                        backBinding.put(keyIndex, keyIndex);
                        for (Integer valueIndex : binderMap.get(keyIndex)) {
                            backBinding.put(valueIndex, keyIndex);
                        }
                    }
                    List<Term> termList = new ArrayList<>();
                    termList.addAll(kList.getContents());
                    for (int idx = 0; idx < termList.size(); idx++) {
                        Map<Term, Term> newSubstitution = new HashMap<>(substitution);
                        if (backBinding.containsKey(idx)) {
                            for (Integer boundPosition : backBinding.get(idx)) {
                                Term variable = kList.get(boundPosition);
                                if (unboundedTerms.contains(variable)) {
                                    newSubstitution.put(variable, freshSubstitution.get(boundPosition));
                                } else if (substitution.containsKey(variable)) {
                                    newSubstitution.remove(variable);
                                }
                            }
                        }
                        Term bindingExp = termList.get(idx);
                        Term resultBindingExp = userSubstitution(newSubstitution, bindingExp, context);
                        termList.set(idx, resultBindingExp);
                    }

                    kItem = KItem.of(kLabel, KList.concatenate(termList), context);
                    return new DoneTransforming(kItem);
                }
            }
            return super.transform(kItem);
        }
    }

}
