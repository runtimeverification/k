package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.BuiltinSet;
import org.kframework.backend.java.kil.MetaVariable;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kil.loader.Context;

import java.util.HashSet;
import java.util.Set;


/**
 * @author: AndreiS
 */
public class MetaK {

    private static Context context = null;

    public static void init(Context context) {
        assert MetaK.context == null;

        MetaK.context = context;
    }

    public static Term rename(Term term, BuiltinSet builtinSet) {
        if (builtinSet.hasFrame() || !builtinSet.operations().isEmpty()) {
            return term;
        }

        Set<Variable> variables = new HashSet<Variable>();
        for (Term element : builtinSet.elements()) {
            if (!(element instanceof MetaVariable)) {
                return term;
            }

            variables.add(new Variable((MetaVariable) element));
        }

        return term.substitute(Variable.getFreshSubstitution(variables), context);
    }

    public static BuiltinSet variables(Term term) {
        Set<Term> metaVariables = new HashSet<Term>();
        for (Variable variable : term.variableSet()) {
            metaVariables.add(new MetaVariable(variable));
        }
        return new BuiltinSet(metaVariables);
    }

}
