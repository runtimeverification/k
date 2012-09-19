package org.kframework.exceptions;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.general.GlobalSettings;

@SuppressWarnings("serial")
public class TransformerException extends Exception {
	KException exception;

	public TransformerException(KException kException) {
		exception = kException;
	}

	public TransformerException(TransformerException exception2) {
		exception = exception2.exception;
	}

	@Override
	public void printStackTrace() {
		super.printStackTrace();
		report();
	}

	public void report() {
		GlobalSettings.kem.register(exception);
	}
	
	
}
