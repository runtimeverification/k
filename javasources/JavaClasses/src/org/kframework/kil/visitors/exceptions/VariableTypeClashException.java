package org.kframework.kil.visitors.exceptions;

import ro.uaic.info.fmse.errorsystem.KException;

@SuppressWarnings("serial")
public class VariableTypeClashException extends TransformerException {

	public VariableTypeClashException(KException kex) {
		super(kex);
	}
}
