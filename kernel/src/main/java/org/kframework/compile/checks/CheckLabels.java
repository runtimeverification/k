// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Sentence;
import org.kframework.utils.errorsystem.KEMException;

import java.util.Set;
import java.util.TreeSet;

/**
 * Check that all sentence labels in a module are unique.
 */
public class CheckLabels {
    private final Set<KEMException> errors;

    public CheckLabels(Set<KEMException> errors) {
        this.errors = errors;
    }

    private final Set<String> labels = new TreeSet<>();

    public void check(Sentence sentence) {
        if (sentence instanceof ContextAlias) {
            return;
        }
        if (sentence.label().isPresent()) {
            String label = sentence.label().get();
            if (!labels.add(label)) {
                errors.add(KEMException.compilerError("Found duplicate sentence label " + label, sentence));
            }
        }
    }
}

