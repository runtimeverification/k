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

	private Map<ExceptionType, String> types;
	private Map<KExceptionGroup, String> labels;

	public KException(ExceptionType type, KExceptionGroup label, String message, String filename, String location, int level) {
		super();
		this.type = type;
		this.exceptionGroup = label;
		this.message = message;
		this.filename = filename;
		this.location = location;
		this.level = level;
		initialize();
	}

	private void initialize() {
		types = new HashMap<KException.ExceptionType, String>();
		types.put(ExceptionType.ERROR, "Error");
		types.put(ExceptionType.WARNING, "Warning");
		types.put(ExceptionType.STATUS, "Status");

		labels = new HashMap<KException.KExceptionGroup, String>();
		labels.put(KExceptionGroup.COMPILER, "Compiler");
		labels.put(KExceptionGroup.PARSER, "Parser");
		labels.put(KExceptionGroup.LISTS, "Lists");
		labels.put(KExceptionGroup.INTERNAL, "Internal");
		labels.put(KExceptionGroup.CRITICAL, "Critical");
	}

	public enum KExceptionGroup {
		PARSER, COMPILER, LISTS, INTERNAL, CRITICAL
	};

	public enum ExceptionType {
		ERROR, WARNING, STATUS
	};

	@Override
	public String toString() {
		return "[" + types.get(type) + "] " + labels.get(exceptionGroup) + ": " + message + "\n\tFile: " + filename + "\n\tLocation: " + location;
	}
}