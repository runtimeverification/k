package org.kframework.kil.visitors.exceptions;

import org.kframework.utils.errorsystem.KException;

@SuppressWarnings("serial")
public class PriorityException extends TransformerException {

	public PriorityException(KException kex) {
		super(kex);
	}
}
