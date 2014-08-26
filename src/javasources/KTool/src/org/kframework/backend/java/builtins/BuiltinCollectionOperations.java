// Copyright (c) 2014 K Team. All Rights Reserved.
package org.kframework.backend.java.builtins;

import org.kframework.backend.java.kil.AssociativeCommutativeCollection;
import org.kframework.backend.java.kil.Collection;
import org.kframework.backend.java.kil.TermContext;


/**
 * Table of {@code public static} methods common to multiple builtin collections.
 *
 * @author AndreiS
 */
public final class BuiltinCollectionOperations {

    public static IntToken size(Collection collection, TermContext context) {
        if (collection instanceof AssociativeCommutativeCollection) {
            return ((AssociativeCommutativeCollection) collection).isConcreteCollection()
                    ? IntToken.of(collection.concreteSize()) : null;
        } else {
            // TODO(AndreiS): support List
            return null;
        }
    }

}
