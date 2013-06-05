package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.BoolToken;
import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.IntToken;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KLabelInjection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;

/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 3/24/13
 * Time: 4:25 PM
 * To change this template use File | Settings | File Templates.
 */
public interface Matcher {

    public String getName();

    public void match(BuiltinConstant builtinConstant, Term pattern);
    public void match(Cell cell, Term pattern);
    public void match(CellCollection cellCollection, Term pattern);
    public void match(Hole hole, Term pattern);
    public void match(KItem kItem, Term pattern);
    public void match(Token token, Term pattern);
    public void match(BoolToken boolToken, Term pattern);
    public void match(IntToken intToken, Term pattern);
    public void match(KLabelConstant kLabelConstant, Term pattern);
    public void match(KLabelFreezer kLabelFreezer, Term pattern);
    public void match(KLabelInjection kLabelInjection, Term pattern);
    public void match(KList kList, Term pattern);
    public void match(KSequence kSequence, Term pattern);
    public void match(Map map, Term pattern);
    public void match(Variable variable, Term pattern);

}
