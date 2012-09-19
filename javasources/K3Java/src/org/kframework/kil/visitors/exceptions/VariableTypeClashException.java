package org.kframework.kil.visitors.exceptions;

import org.kframework.utils.errorsystem.KException;

@SuppressWarnings("serial")
public class VariableTypeClashException extends TransformerException {

	public VariableTypeClashException(KException kex) {
		super(kex);
	}
}
