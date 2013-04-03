package org.kframework.utils.errorsystem;

import java.util.HashMap;
import java.util.Map;

public class KException {
	protected ExceptionType type;
	protected KExceptionGroup exceptionGroup;
	protected String filename;
	protected String location;
	protected int level;
	protected String message;
	private String compilationPhase = null;

	protected static Map<ExceptionType, String> types;
	protected static Map<KExceptionGroup, String> labels;
	static {
		types = new HashMap<KException.ExceptionType, String>();
		types.put(ExceptionType.ERROR, "Error");
		types.put(ExceptionType.WARNING, "Warning");
		types.put(ExceptionType.HIDDENWARNING, "Warning");

		labels = new HashMap<KException.KExceptionGroup, String>();
		labels.put(KExceptionGroup.COMPILER, "Compiler");
		labels.put(KExceptionGroup.PARSER, "Parser");
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
		PARSER, COMPILER, LISTS, INTERNAL, CRITICAL
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

	public ExceptionType getType() {
		return type;
	}

	public void setType(ExceptionType type) {
		this.type = type;
	}

	public KExceptionGroup getExceptionGroup() {
		return exceptionGroup;
	}

	public void setExceptionGroup(KExceptionGroup exceptionGroup) {
		this.exceptionGroup = exceptionGroup;
	}

	public String getFilename() {
		return filename;
	}

	public void setFilename(String filename) {
		this.filename = filename;
	}

	public String getLocation() {
		return location;
	}

	public void setLocation(String location) {
		this.location = location;
	}

	public int getLevel() {
		return level;
	}

	public void setLevel(int level) {
		this.level = level;
	}

	public String getMessage() {
		return message;
	}

	public void setMessage(String message) {
		this.message = message;
	}

	public String getCompilationPhase() {
		return compilationPhase;
	}

	public void setCompilationPhase(String compilationPhase) {
		this.compilationPhase = compilationPhase;
	}
}
