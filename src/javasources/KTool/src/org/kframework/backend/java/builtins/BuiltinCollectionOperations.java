package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.TermContext;


/**
 * Table of {@code public static} methods common to multiple builtin collections.
 *
 * @author AndreiS
 */
public final class BuiltinCollectionOperations {

    private BuiltinCollectionOperations() { }

    public static IntToken size(Collection term, TermContext context) {
        return !term.hasFrame() ? IntToken.of(term.size()) : null;
    }

}
