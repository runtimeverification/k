// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.common.collect.ImmutableList;
import org.kframework.backend.java.builtins.MetaK;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.kil.*;
import org.kframework.kil.ASTNode;

import java.util.Map;
import java.util.Set;


/**
 * Substitutes variables with terms according to a given substitution map.
 * 
 * @author AndreiS
 */
public class UserSubstitutionTransformer extends PrePostTransformer {

    private final Map<Term, Term> substitution;

    public UserSubstitutionTransformer(Map<Term, Term> substitution,
                                       TermContext context) {
        super(context);
        this.substitution = substitution;
        preTransformer.addTransformer(new BinderSubstitution(context));
        postTransformer.addTransformer(new LocalSubstitutionTransformer());
    }
    
    /**
     * Local transformer that performs the actual substitution of variables.
     */
    private class LocalSubstitutionTransformer extends LocalTransformer {

        @Override
        public Term transform(Term variable) {
            Term term = substitution.get(variable);
            if (term != null) {
                if (term instanceof KCollectionFragment) {
                    KCollectionFragment fragment = (KCollectionFragment) term;
                    ImmutableList.Builder<Term> builder = new ImmutableList.Builder<Term>();
                    builder.addAll(fragment);

                    KCollection kCollection;
                    if (fragment.getKCollection() instanceof KSequence) {
                        if (fragment.hasFrame()) {
                            kCollection = new KSequence(builder.build(), fragment.frame());
                        } else {
                            kCollection = new KSequence(builder.build());
                        }
                    } else {
                        assert fragment.getKCollection() instanceof KList;

                        if (fragment.hasFrame()) {
                            kCollection = new KList(builder.build(), fragment.frame());
                        } else {
                            kCollection = new KList(builder.build());
                        }
                    }

                    return kCollection;
                } else {
                    return term;
                }
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
            assert kItem.kLabel() instanceof KLabel : "KLabel variables are not supported";
            assert kItem.kList() instanceof KList : "KList must be concrete";

            KLabel kLabel = (KLabel) kItem.kLabel();
            KList kList = (KList) kItem.kList();
            if (kLabel instanceof KLabelConstant) {
                KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
                if (kLabelConstant.isBinder()) {
                    assert kList.getContents().size()==2 && !kList.hasFrame() :
                            "Only supporting binders of the form lambda x. e for now";
                    Term boundVar = kList.get(0);
//                    if (boundVar instanceof Variable ||
//                            boundVar instanceof BuiltinList || boundVar instanceof BuiltinSet) {
                        // only rename vars if they are already a builtin structure.
                        Term bindingExp = kList.get(1);
                        Term variable = boundVar;
                        Term freshBoundVars = MetaK.fresh(StringToken.of(variable.sort()), context);
                        Term current = substitution.get(boundVar);
                        substitution.put(boundVar, freshBoundVars);
                        Term resultBindingExp = (Term) bindingExp.accept(this);
                        if (current != null) {
                            substitution.put(boundVar, current);
                        }
                        kList = new KList(ImmutableList.<Term>of(freshBoundVars,resultBindingExp));
                        return new KItem(kLabel, kList, context);

//                    }
                }
            }
            return super.transform(kItem);
        }
    }
   
}
