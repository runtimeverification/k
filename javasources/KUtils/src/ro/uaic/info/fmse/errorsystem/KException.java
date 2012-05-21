package ro.uaic.info.fmse.errorsystem;

import java.util.HashMap;
import java.util.Map;

public class KException {

	protected ExceptionType type;
	protected Label label;
	protected String filename;
	protected String location;
	protected int level;
	protected String message;
	
	private Map<ExceptionType, String> types;
	private Map<Label, String> labels;
	
	public KException(ExceptionType type, Label label, String message, String filename, String location) {
		super();
		this.type = type;
		this.label = label;
		this.message = message;
		this.filename = filename;
		this.location = location;
		
		initialize();
	}
	
	
	private void initialize() {
		types = new HashMap<KException.ExceptionType, String>();
		types.put(ExceptionType.ERROR, "Error");
		types.put(ExceptionType.WARNING, "Warning");
		types.put(ExceptionType.STATUS, "Status");
		
		labels = new HashMap<KException.Label, String>();
		labels.put(Label.COMPILER, "Compiler");
		labels.put(Label.PARSER, "Parser");
		labels.put(Label.LISTS, "Lists");
		labels.put(Label.INTERNAL, "Internal");
		labels.put(Label.CRITICAL, "Critical");
	}


	public enum Label { PARSER, COMPILER, LISTS, INTERNAL, CRITICAL};
	public enum ExceptionType { ERROR, WARNING, STATUS };
	
	@Override
	public String toString() {
		return "[" + types.get(type) + "] " + labels.get(label) + ":" + message + "\n\tFile: " + filename + "\n\tLocation: " + location;
	}
}