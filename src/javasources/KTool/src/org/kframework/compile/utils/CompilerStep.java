// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;
import org.kframework.utils.Stopwatch;

/**
 * Represents a compilation step for a certain type of abstract syntax tree
 * (AST) in the definition. <br>
 * <p>
 * For instance, the ASTs on which this compilation operates can be just
 * {@code Module}s or {@code Rule}s of the definition.
 * </p>
 * 
 * @param <T>
 *            the type of the AST
 */
public interface CompilerStep<T extends ASTNode> {
    
    /**
     * Applies a certain compilation step to a given abstract syntax tree (AST)
     * in the definition.
     * 
     * @param ast
     *            the given AST
     * @param haltAfterStep
     *            the name of the compilation step after which the compilation
     *            should halt
     * @return the resulting AST after this compilation step
     * @throws CompilerStepDone
     */
    T compile(T ast, String haltAfterStep) throws CompilerStepDone;
    
    /**
     * Returns the name of this compilation step.
     */
    String getName();

    /**
     * Sets the stop watch of this compilation step.
     * @param sw the stop watch
     */
    void setSw(Stopwatch sw);
}
