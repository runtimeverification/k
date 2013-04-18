package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.BuiltinConstant;
import org.kframework.backend.java.kil.Cell;
import org.kframework.backend.java.kil.CellCollection;
import org.kframework.backend.java.kil.ConstantKLabel;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.InjectionKLabel;
import org.kframework.backend.java.kil.K;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Map;
import org.kframework.backend.java.kil.Term;
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
    public void match(ConstantKLabel constantKLabel, Term pattern);
    public void match(Hole hole, Term pattern);
    public void match(InjectionKLabel injectionKLabel, Term pattern);
    public void match(K k, Term pattern);
    public void match(KList kList, Term pattern);
    public void match(KSequence kSequence, Term pattern);
    public void match(Map map, Term pattern);
    public void match(Variable variable, Term pattern);

}
