// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.transformation;

import org.kframework.kil.Attributes;

/**
 * The basic unit of a K tool transformation sequence.
 *
 * K is a compiler and an interpreter. In essence, its purpose is to take inputs in
 * a certain form and provide outputs in a different form. These forms take a variety
 * of types under different circumstances. For example, a parser might transform
 * a String into an ASTNode. A pretty-printer might transform an ASTNode into a String.
 * An execution engine might transform an input program into an output execution state.
 *
 * Each of these individual actions becomes one implementation of the Transformation
 * interface. By combining these transformations together in a prearranged sequence,
 * we are able to represent the entire execution of the tool.
 * @author dwightguth
 *
 * @param <P> The input type of the transformation.
 * @param <R> The output type of the transformation.
 */
public interface Transformation<P, R> {

    /**
     * Executes the transformation.
     *
     * @param p The input of the transformation.
     * @param attrs The context of the transformation.
     * It is good programming practice for implementing classes to declare
     * the context keys that they require in their javadoc. For example,
     * a transformation which pretty prints the edge of a graph might
     * require access to the graph the edge is a part of.
     * @return The output of the transformation.
     */
    public R run(P p, Attributes attrs);

    /**
     * A user-friendly name describing the transformation step.
     * It is best if this name clearly identifies to the user
     * what the step is doing and why it has been activated by the
     * tool (e.g., because you specified the --backend java flag).
     * @return
     */
    public String getName();
}
