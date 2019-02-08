// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.unparser;

/**
 * To be implemented by instances of {@code Rewriter} that need an object of type PrettyPrinter.
 *
 * @author Denis Bogdanas
 * Created on 08-Feb-19.
 * @see org.kframework.rewriter.Rewriter
 */
public interface WantsPrettyPrinter {
    void setPrettyPrinter(PrettyPrinter prettyPrinter);
}
