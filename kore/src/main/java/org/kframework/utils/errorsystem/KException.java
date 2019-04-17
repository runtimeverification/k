// Copyright (c) 2012-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;

import org.kframework.attributes.Location;
import org.kframework.attributes.Source;

import java.io.Serializable;
import java.util.Formatter;
import java.util.HashMap;
import java.util.Map;

public class KException implements Serializable {
    protected final ExceptionType type;
    final KExceptionGroup exceptionGroup;
    private final Source source;
    private final Location location;
    private final String message;
    private final Throwable exception;
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
        this(type, label, message, source, location, null);
    }

    public KException(
            ExceptionType type,
            KExceptionGroup label,
            String message,
            Source source,
            Location location,
            Throwable exception) {
        super();
        this.type = type;
        this.exceptionGroup = label;
        this.message = message;
        this.source = source;
        this.location = location;
        this.exception = exception;
    }

    public enum KExceptionGroup {
        OUTER_PARSER, INNER_PARSER, COMPILER, LISTS, INTERNAL, CRITICAL, DEBUGGER
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
                + (exception == null ? "" : " (" + exception.getMessage() + ")")
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
}
