// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.Bottom;
import org.kframework.backend.java.kil.BuiltinList;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.Hole;
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
 * @see Unifiable
 *
 * @author AndreiS
 */
public interface Unifier {

    public String getName();

    public void unify(Bottom bottom, Term term);
    public void unify(BuiltinList builtinList, Term term);
    public void unify(BuiltinMap builtinMap, Term term);
    public void unify(BuiltinSet builtinSet, Term term);
    public void unify(CellCollection cellCollection, Term term);
    public void unify(Hole hole, Term term);
    public void unify(KItem kItem, Term term);
    public void unify(KLabelConstant kLabelConstant, Term term);
    public void unify(KLabelInjection kLabelInjection, Term term);
    public void unify(KList kList, Term term);
    public void unify(KSequence kSequence, Term term);
    public void unify(Token token, Term term);

}
