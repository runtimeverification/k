// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import java.util.HashSet;
import java.util.Set;

/**
 * A Set of exceptions gathered during disambiguation of ambiguous trees.
 */
@SuppressWarnings("serial")
public class ParseFailedExceptionSet extends RuntimeException {
    public ParseFailedExceptionSet() {
    }

    public ParseFailedExceptionSet(ParseFailedException pe) {
        exceptions.add(pe);
    }

    public Set<ParseFailedException> exceptions = new HashSet<>();
}
