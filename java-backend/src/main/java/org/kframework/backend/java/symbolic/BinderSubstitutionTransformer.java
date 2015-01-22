// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import java.util.Map;
import java.util.Set;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabel;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Location;
import org.kframework.kil.Source;


/**
 * Substitutes variables with terms according to a given substitution map using binders.
 *
 * @author TraianSF
 */
public class BinderSubstitutionTransformer extends SubstitutionTransformer {

    public BinderSubstitutionTransformer(Map<Variable, ? extends Term> substitution, TermContext context) {
        super(substitution, context);
    }

    @Override
    public ASTNode transform(KItem kItem) {
        return proceed(kItem) ? super.transform(binderSensitiveSubstitute(kItem, context)) : kItem;
    }

    public static KItem binderSensitiveSubstitute(KItem kItem, TermContext context) {
        // TODO(AndreiS): fix binder when dealing with KLabel variables and non-concrete KLists
        if (kItem.kLabel() instanceof KLabel && kItem.kList() instanceof KList) {
//            assert kItem.kLabel() instanceof KLabel : "KLabel variables are not supported";
//            assert kItem.kList() instanceof KList : "KList must be concrete";

            KLabel kLabel = (KLabel) kItem.kLabel();
            KList kList = (KList) kItem.kList();
            if (kLabel instanceof KLabelConstant) {
                KLabelConstant kLabelConstant = (KLabelConstant) kLabel;
                if (kLabelConstant.isMetaBinder()) {
                    assert kList.getContents().size()==2 && !kList.hasFrame() :
                            "Only supporting binders of the form lambda x. e for now";
                    Term boundVars = kList.get(0);
//                    if (boundVars instanceof Variable ||
//                            boundVars instanceof BuiltinList || boundVars instanceof BuiltinSet) {
                        // only rename vars if they are already a builtin structure.
                        Term bindingExp = kList.get(1);
                        Set<Variable> variables = boundVars.variableSet();
                        Map<Variable,Variable> freshSubstitution = Variable.getFreshSubstitution(variables);
                        Term freshBoundVars = boundVars.substitute(freshSubstitution, context);
                        Term freshbindingExp = bindingExp.substitute(freshSubstitution, context);
                        kItem = KItem.of(kLabel, KList.concatenate(freshBoundVars, freshbindingExp), context,
                                    kItem.getSource(), kItem.getLocation());
//                    }
                }
            }
        }
        return kItem;
    }

}
