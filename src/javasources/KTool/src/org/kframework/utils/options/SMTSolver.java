// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.utils.options;

/**
 * Enum storing information about which SMT solver is being used
 * 
 * TODO(dwightguth): create a proper SMT interface and put this class in that package
 * @author dwightguth
 */
public enum SMTSolver {
    /**
     * No SMT. Interpreter may fail to reason about certain types of situations.
     */
    NONE, 
    
    /**
     * The Microsoft Z3 SMT solver.
     */
    Z3,
    
    /**
     * Uses {@link GappaServer}.
     */
    GAPPA;
    
}
