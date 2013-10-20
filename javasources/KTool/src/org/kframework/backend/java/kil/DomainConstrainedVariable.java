package org.kframework.backend.java.kil;

import org.kframework.backend.java.symbolic.BuiltinFunction;

/**
 * A variable to represent the evaluated result of some builtin function term.
 * 
 * @see org.kframework.backend.java.kil.KItem#evaluateFunction(TermContext)
 */
@SuppressWarnings("serial")
public class DomainConstrainedVariable extends Variable {

    private KItem builtinFunc;
    
    /**
     * Returns a fresh onymous variable.
     */
    public static DomainConstrainedVariable getFreshContrainedVariable(String sort, KItem funTerm) {
        assert sort.equals(funTerm.sort());
        //return new DomainConstrainedVariable(VARIABLE_PREFIX + (counter++) + "(=" + funTerm + ")", sort, funTerm);
        return new DomainConstrainedVariable(VARIABLE_PREFIX + (counter++), sort, funTerm);
    }    

    private DomainConstrainedVariable(String name, String sort, KItem funTerm) {
        super(name, sort, false);
        assert BuiltinFunction.isBuiltinKLabel((KLabelConstant) funTerm.kLabel());
        builtinFunc = funTerm;
    }

    public KItem getConstraint() {
        return builtinFunc;
    }
    
    @Override
    public boolean equals(Object object) {
        return this == object;
    }

    @Override
    public int hashCode() {
        return 0;
    }
    
    @Override
    public String toString() {
        return super.toString() + "(=" + builtinFunc + ")";
    }
}