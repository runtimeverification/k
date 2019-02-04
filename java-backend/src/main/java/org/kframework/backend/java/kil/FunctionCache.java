package org.kframework.backend.java.kil;

import com.google.common.collect.HashBasedTable;
import com.google.common.collect.Table;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Denis Bogdanas
 * Created on 29-Jan-19.
 */
public class FunctionCache {

    final Table<JavaSymbolicObject<?>, ConjunctiveFormula, Term> evaluationCache = HashBasedTable.create();
    final Map<JavaSymbolicObject<?>, Term> nullConstraintEvalCache = new HashMap<>();

    public void clearCache() {
        evaluationCache.clear();
        nullConstraintEvalCache.clear();
    }
}
