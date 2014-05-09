// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.visitors.exceptions;

import org.kframework.utils.errorsystem.KException;

@SuppressWarnings("serial")
public class VariableTypeClashException extends ParseFailedException {

    public VariableTypeClashException(KException kex) {
        super(kex);
    }
}
