// Copyright (c) 2013-2019 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.InjectedKLabel;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;


/**
 * Interface for a unifier. A unifier implements a visitor pattern specialized for unification,
 * which uses double dispatch to reduce an invocation of {@code unify} with two generic {@link
 * Term} arguments to an invocation of {@code unify} with the first argument of the actual class.
 *
 * @author AndreiS
 */
public interface Unifier {

    String getName();

    void unify(Bottom bottom, Bottom term);
    void unify(BuiltinList builtinList, BuiltinList term);
    void unify(BuiltinMap builtinMap, BuiltinMap term);
    void unify(BuiltinSet builtinSet, BuiltinSet term);

    void unify(Hole hole, Hole term);
    void unify(KItem kItem, KItem term);
    void unify(KLabelConstant kLabelConstant, KLabelConstant term);
    void unify(KLabelInjection kLabelInjection, KLabelInjection term);
    void unify(KList kList, KList term);
    void unify(KSequence kSequence, KSequence term);
    void unify(Token token, Token term);
    void unify(InjectedKLabel injectedKLabel, InjectedKLabel term);

}
