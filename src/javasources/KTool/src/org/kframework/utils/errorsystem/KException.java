package org.kframework.utils.errorsystem;

import java.util.HashMap;
import java.util.Map;

public class KException {
    protected final ExceptionType type;
    private final KExceptionGroup exceptionGroup;
    private final String filename;
    private final String location;
    private final String message;
    private String compilationPhase = null;

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

    public KException(ExceptionType type, KExceptionGroup label, String message) {
        this(type, label, message, null, null);
    }

    public KException(ExceptionType type, KExceptionGroup label, String message, String filename, String location) {
        super();
        this.type = type;
        this.exceptionGroup = label;
        this.message = message;
        this.filename = filename;
        this.location = location;
    }
    
    public KException(ExceptionType type, KExceptionGroup label, String message, String compilationPhase, String filename, String location) {
        this(type,label,message,filename,location);
        this.compilationPhase = compilationPhase;
    }

    public enum KExceptionGroup {
        OUTER_PARSER, INNER_PARSER, COMPILER, LISTS, INTERNAL, CRITICAL
    }

    public enum ExceptionType {
        ERROR, WARNING, HIDDENWARNING
    }

    @Override
    public String toString() {
        return "[" + types.get(type) + "] " + labels.get(exceptionGroup) + ": " + message
            + (filename == null ? "" : "\n\tFile: " + filename)
            + (location == null ? "" : "\n\tLocation: " + location)
            + (compilationPhase == null ? "" : "\n\tCompilation Phase: " + compilationPhase);
        
    }

    public String getMessage() {
        return message;
    }
}
