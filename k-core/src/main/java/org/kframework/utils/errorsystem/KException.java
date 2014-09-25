// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.Location;
import org.kframework.kil.Source;

public class KException {
    protected final ExceptionType type;
    private final KExceptionGroup exceptionGroup;
    private final Source source;
    private final Location location;
    private final String message;
    private final Throwable exception;
    private String compilationPhase = null;
    private StringBuilder trace = new StringBuilder();

    private static final Map<ExceptionType, String> types;
    private static final Map<KExceptionGroup, String> labels;
    static {
        types = new HashMap<KException.ExceptionType, String>();
        types.put(ExceptionType.ERROR, "Error");
        types.put(ExceptionType.WARNING, "Warning");
        types.put(ExceptionType.HIDDENWARNING, "Warning");

        labels = new HashMap<KException.KExceptionGroup, String>();
        labels.put(KExceptionGroup.COMPILER, "Compiler");
        labels.put(KExceptionGroup.OUTER_PARSER, "Outer Parser");
        labels.put(KExceptionGroup.INNER_PARSER, "Inner Parser");
        labels.put(KExceptionGroup.LISTS, "Lists");
        labels.put(KExceptionGroup.INTERNAL, "Internal");
        labels.put(KExceptionGroup.CRITICAL, "Critical");
    }

    public static KException criticalError(String message) {
        return new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, message);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message) {
        this(type, label, message, null, null, null, null);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, Throwable e) {
        this(type, label, message, null, null, null, e);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, Source source, Location location) {
        this(type, label, message, null, source, location, null);
    }

    public KException(
            ExceptionType type,
            KExceptionGroup label,
            String message,
            Source source,
            Location location,
            Throwable e) {
        this(type, label, message, null, source, location, e);
    }

    public KException(
            ExceptionType type,
            KExceptionGroup label,
            String message,
            String compilationPhase,
            Source source,
            Location location,
            Throwable exception) {
        super();
        this.type = type;
        this.exceptionGroup = label;
        this.message = message;
        this.compilationPhase = compilationPhase;
        this.source = source;
        this.location = location;
        this.exception = exception;
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, String compilationPhase, Source source, Location location) {
        this(type,label,message,compilationPhase,source,location, null);
    }

    public enum KExceptionGroup {
        OUTER_PARSER, INNER_PARSER, COMPILER, LISTS, INTERNAL, CRITICAL
    }

    public enum ExceptionType {
        ERROR, WARNING, HIDDENWARNING
    }

    @Override
    public String toString() {
        return toString(false);
    }

    public String toString(boolean verbose) {
        return "[" + types.get(type) + "] " + labels.get(exceptionGroup) + ": " + message
                + trace.toString() + traceTail()
                + (source == null ? "" : "\n\tSource: " + source)
                + (location == null ? "" : "\n\tLocation: " + location)
                + (compilationPhase == null || !verbose ? "" : "\n\tCompilation Phase: " + compilationPhase);
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
    private String lastFrame;
    public void addTraceFrame(String frame) {
        if (frames < 1024) {
            if (frame.equals(lastFrame)) {
                identicalFrames++;
            } else {
                if (identicalFrames > 1) {
                    trace.append(" * " + identicalFrames);
                    identicalFrames = 1;
                }
                trace.append("\n  " + frame);
                lastFrame = frame;
                frames++;
            }
        }
    }
}
