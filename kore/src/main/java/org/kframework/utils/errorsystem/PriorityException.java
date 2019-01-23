// Copyright (c) 2014-2019 K Team. All Rights Reserved.
package org.kframework.utils.errorsystem;


@SuppressWarnings("serial")
public class PriorityException extends ParseFailedException {

    public PriorityException(KException kex) {
        super(kex);
    }
}
