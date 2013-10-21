package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.builtins.BoolToken;
import org.kframework.backend.java.builtins.IntToken;
import org.kframework.backend.java.builtins.Int32Token;
import org.kframework.backend.java.builtins.StringToken;
import org.kframework.backend.java.builtins.UninterpretedToken;
import org.kframework.backend.java.kil.BuiltinMap;
import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;

import java.io.Serializable;


/**
 * Interface for a unifier. A unifier implements a visitor pattern specialized for unification,
 * which uses double dispatch to reduce an invocation of {@code unify} with two generic {@link
 * Term} arguments to an invocation of {@code unify} with the first argument of the actual class.
 *
 * @author AndreiS
 */
public interface Unifier {

    public String getName();

    public void unify(BoolToken boolToken, Term term);
    public void unify(BuiltinMap builtinMap, Term term);
    public void unify(BuiltinSet builtinSet, Term term);
    public void unify(Cell cell, Term term);
    public void unify(CellCollection cellCollection, Term term);
    public void unify(Hole hole, Term term);
    public void unify(IntToken intToken, Term term);
    public void unify(Int32Token intToken, Term term);
    public void unify(KItem kItem, Term term);
    public void unify(KLabelConstant kLabelConstant, Term term);
    public void unify(KLabelFreezer kLabelFreezer, Term term);
    public void unify(KLabelInjection kLabelInjection, Term term);
    public void unify(KList kList, Term term);
    public void unify(KSequence kSequence, Term term);
    public void unify(MetaVariable metaVariable, Term term);
    public void unify(StringToken stringToken, Term term);
    public void unify(Term term, Term otherTerm);
    public void unify(Token token, Term term);
    public void unify(UninterpretedToken uninterpretedToken, Term term);
    public void unify(Variable variable, Term term);

}
