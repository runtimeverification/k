package org.kframework.compile.utils;

public class CompilerStepDone extends Exception {
	private static final long serialVersionUID = 1L;
	private Object result;
	
	public CompilerStepDone(Object result) {
		this.result = result;
	}

	public Object getResult() {
		return result;
	}
}
