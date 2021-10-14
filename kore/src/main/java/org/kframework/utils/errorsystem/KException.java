// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.attributes.HasLocation;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

import java.io.Serializable;
import java.util.*;

public class KException implements Serializable, HasLocation {
    protected final ExceptionType type;
    final KExceptionGroup exceptionGroup;
    private final Source source;
    private final Location location;
    private final String message;
    private final Throwable exception;
    private final boolean printException;
    private StringBuilder trace = new StringBuilder();

    private static final Map<KExceptionGroup, String> labels;
    static {
        labels = new HashMap<KException.KExceptionGroup, String>();
        labels.put(KExceptionGroup.COMPILER, "Compiler");
        labels.put(KExceptionGroup.OUTER_PARSER, "Outer Parser");
        labels.put(KExceptionGroup.INNER_PARSER, "Inner Parser");
        labels.put(KExceptionGroup.LISTS, "Lists");
        labels.put(KExceptionGroup.INTERNAL, "Internal");
        labels.put(KExceptionGroup.CRITICAL, "Critical");
        labels.put(KExceptionGroup.DEBUGGER, "Debugger");
    }

    public static KException criticalError(String message) {
        return new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message) {
        this(type, label, message, null, (Location) null, null);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, Throwable e) {
        this(type, label, message, null, (Location) null, e);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, Source source, Location location) {
        this(type, label, message, source, location, null, true);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, Source source, Location location, Throwable exception) {
        this(type, label, message, source, location, exception, true);
    }

    public KException(
            ExceptionType type,
            KExceptionGroup label,
            String message,
            Source source,
            Location location,
            Throwable exception,
            boolean printException) {
        super();
        this.type = type;
        this.exceptionGroup = label;
        this.message = message;
        this.source = source;
        this.location = location;
        this.exception = exception;
        this.printException = printException;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        KException that = (KException) o;
        return type == that.type &&
                exceptionGroup == that.exceptionGroup &&
                Objects.equals(source, that.source) &&
                Objects.equals(location, that.location) &&
                Objects.equals(message, that.message) &&
                Objects.equals(exception, that.exception) &&
                Objects.equals(trace.toString(), that.trace.toString());
    }

    @Override
    public int hashCode() {
        return Objects.hash(type, exceptionGroup, source, location, message, exception, trace.toString());
    }

    @Override
    public Optional<Location> location() {
        return Optional.ofNullable(location);
    }

    @Override
    public Optional<Source> source() {
        return Optional.ofNullable(source);
    }

    public enum KExceptionGroup {
        OUTER_PARSER, INNER_PARSER, COMPILER, LISTS, INTERNAL, CRITICAL, DEBUGGER
    }

    public enum ExceptionType {
        ERROR,
        RULE_HAS_MACRO_ATT,
        NON_EXHAUSTIVE_MATCH,
        UNDELETED_TEMP_DIR,
        MISSING_HOOK_OCAML,
        MISSING_SYNTAX_MODULE,
        INVALID_EXIT_CODE,
        INVALID_CONFIG_VAR,
        FUTURE_ERROR,
        UNUSED_VAR,
        PROOF_LINT,
        NON_LR_GRAMMAR,
        FIRST_HIDDEN, // warnings below here are hidden by default
        MISSING_HOOK_JAVA,
        USELESS_RULE,
        UNRESOLVED_FUNCTION_SYMBOL,
        MALFORMED_MARKDOWN,
        INVALIDATED_CACHE,
        UNUSED_SYMBOL
    }

    @Override
    public String toString() {
        return toString(false);
    }

    public String toString(boolean verbose) {
        return "[" + (type == ExceptionType.ERROR ? "Error" : "Warning") + "] " + labels.get(exceptionGroup) + ": " + message
                + (exception != null && printException ? " (" + exception.getClass().getSimpleName() + ": " + exception.getMessage() + ")" : "")
                + trace.toString() + traceTail()
                + (source == null ? "" : "\n\t" + source)
                + (location == null ? "" : "\n\t" + location);
    }

    public String getMessage() {
        return message;
    }

    public Throwable getException() {
        return exception;
    }

    public ExceptionType getType() {
        return type;
    }

    private String traceTail() {
        if (identicalFrames > 1) {
            return " * " + identicalFrames;
        }
        return "";
    }

    private int frames = 0;
    private int identicalFrames = 1;
    private CharSequence lastFrame;
    public void addTraceFrame(CharSequence frame) {
        if (frames < 1024) {
            if (frame.equals(lastFrame)) {
                identicalFrames++;
            } else {
                if (identicalFrames > 1) {
                    trace.append(" * ").append(identicalFrames);
                    identicalFrames = 1;
                }
                trace.append("\n  ").append(frame);
                lastFrame = frame;
                frames++;
            }
        }
    }

    public void formatTraceFrame(String format, Object... args) {
        StringBuilder sb = new StringBuilder();
        new Formatter(sb).format(format, args);
        addTraceFrame(sb);
    }

    public Source getSource() {
        return source;
    }

    public Location getLocation() {
        return location;
    }

    public KExceptionGroup getExceptionGroup() {
        return exceptionGroup;
    }
}
