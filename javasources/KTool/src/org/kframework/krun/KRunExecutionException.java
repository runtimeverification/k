package org.kframework.krun;

public class KRunExecutionException extends Exception {
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;

	KRunExecutionException() {
		super();
	}
	
	KRunExecutionException(String message){
		super(message);
	}
	
	KRunExecutionException(String message, Throwable t){
		super(message, t);
	}
	
	KRunExecutionException(Throwable t){
		super(t);
	}
}
