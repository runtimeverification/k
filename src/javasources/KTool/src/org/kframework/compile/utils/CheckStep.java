// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.utils;

import org.kframework.kil.ASTNode;

public interface CheckStep<T extends ASTNode> {
    boolean check(T def);

    String getName();
}
