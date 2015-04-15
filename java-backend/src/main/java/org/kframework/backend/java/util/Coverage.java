// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.*;
import org.kframework.attributes.Source;
import org.kframework.attributes.Location;
import org.kframework.utils.errorsystem.KExceptionManager;

import java.io.File;
import java.io.IOException;

import static org.apache.commons.io.FileUtils.writeStringToFile;

/**
 * For measuring semantic coverage
 *
 * @author daejunpark
 */
public class Coverage {

    /**
     * Print location information of {@code constrainedTerm} into {@code file}.
     * - If {@code file} is null, then it does nothing.
     * - If the location information is not available, then it does nothing.
     *
     * @param file could be null.
     * @param constrainedTerm should not be null.
     */
    public static void print(File file, ConstrainedTerm constrainedTerm) {
        if (file != null) {
            print(file, getSourceLocation(constrainedTerm));
        }
    }

    /**
     * Print location information of {@code term} into {@code file}.
     * - If {@code file} is {@code null}, then it does nothing.
     * - If the location information is not available, then it does nothing.
     *
     * @param file could be null.
     * @param term should not be null.
     */
    public static void print(File file, Term term) {
        if (file != null) {
            print(file, getSourceLocation(term));
        }
    }

    /**
     * Print location information of {@code rule} into {@code file}.
     * - If {@code file} is {@code null}, then it does nothing.
     * - If the location information is not available, then it does nothing.
     *
     * @param file could be null.
     * @param rule should not be null.
     */
    public static void print(File file, Rule rule) {
        if (file != null) {
            print(file, getSourceLocation(rule));
        }
    }

    private static void print(File file, String string) {
        if (file != null && string != null) {
            try {
                writeStringToFile(file, string + "\n", true);
            } catch (IOException e) {
                throw KExceptionManager.internalError("Could not write to " + file, e);
            }
        }
    }

    private static String getSourceLocation(ConstrainedTerm constrainedTerm) {
        return getSourceLocation(constrainedTerm.term());
    }

    private static String getSourceLocation(Term term) {
        String s = null; // Return null, if location information is not available.
        Term t = term.getCellContentsByName(CellLabel.K).get(0);
        if (t instanceof KSequence && ((KSequence) t).concreteSize() > 0) {
            t = ((KSequence) t).get(0);
        }
        if (t instanceof KItem) {
            Source source = t.getSource();
            s = source.toString() + ":" + t.getLocation().toString();
        }
        return s;
    }

    private static String getSourceLocation(Rule rule) {
        String s = null; // Return null, if location information is not available.
        Source source = rule.getSource();
        s = source.toString() + ":" + rule.getLocation().toString();
        return s;
    }
}
