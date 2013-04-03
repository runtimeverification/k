package org.kframework.kil.visitors.exceptions;

import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

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
		report();
	}

	public void report() {
		GlobalSettings.kem.register(exception);
	}

	public String getMessage() {
		return exception.getMessage();
	}
}
