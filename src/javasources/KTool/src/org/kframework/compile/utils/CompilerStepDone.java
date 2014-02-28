package org.kframework.compile.utils;

/**
 * An exception which indicates the halt of the compilation process.
 */
public class CompilerStepDone extends Exception {
    private static final long serialVersionUID = 1L;
    private Object result;
    
    public CompilerStepDone(Object result) {
        this.result = result;
    }

    public Object getResult() {
        return result;
    }
}
