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

    public static void print(File file, ConstrainedTerm subject) {
        if (file != null) {
            print(file, getSourceLocation(subject));
        }
    }

    public static void print(File file, Term subject) {
        if (file != null) {
            print(file, getSourceLocation(subject));
        }
    }

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

    private static String getSourceLocation(ConstrainedTerm subject) {
        return getSourceLocation(subject.term());
    }

    private static String getSourceLocation(Term subject) {
        String s = null;
        Term t = subject.getCellContentsByName(CellLabel.K).get(0);
        if (t instanceof KSequence && ((KSequence) t).concreteSize() > 0) {
            t = ((KSequence) t).get(0);
        }
        if (t instanceof KItem) {
            Source source = t.getSource();
            if (source instanceof FileSource) {
                s = stringOf((FileSource) source) + ":" + stringOf(t.getLocation());
            }
        }
        return s;
    }

    private static String getSourceLocation(Rule rule) {
        String s = null;
        Source source = rule.getSource();
        if (source instanceof FileSource) {
            s = stringOf((FileSource) source) + ":" + stringOf(rule.getLocation());
        }
        return s;
    }

    private static String stringOf(FileSource source) {
        return source.getFile().getAbsolutePath().toString();
    }

    private static String stringOf(Location location) {
        return  location.lineStart
        + ":" + location.columnStart
        + ":" + location.lineEnd
        + ":" + location.columnEnd;
    }

}
