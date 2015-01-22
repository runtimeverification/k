// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.backend.java.util;

import org.kframework.backend.java.kil.*;
import org.kframework.kil.FileSource;
import org.kframework.kil.Location;
import org.kframework.kil.Source;
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
            if (source instanceof FileSource) {
                s = toString((FileSource) source) + ":" + toString(t.getLocation());
            }
        }
        return s;
    }

    private static String getSourceLocation(Rule rule) {
        String s = null; // Return null, if location information is not available.
        Source source = rule.getSource();
        if (source instanceof FileSource) {
            s = toString((FileSource) source) + ":" + toString(rule.getLocation());
        }
        return s;
    }

    // Customized toString method for FileSource.
    private static String toString(FileSource source) {
        return source.getFile().getAbsolutePath();
    }

    // Customized toString method for Location.
    private static String toString(Location location) {
        return  location.lineStart + ":" + location.columnStart
        + ":" + location.lineEnd   + ":" + location.columnEnd;
    }

}
