// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;


@SuppressWarnings("serial")
public class VariableTypeClashException extends ParseFailedException {

    public VariableTypeClashException(KException kex) {
        super(kex);
    }
}
