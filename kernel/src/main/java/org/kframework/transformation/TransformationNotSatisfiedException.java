// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.transformation;

import java.util.Set;

import com.google.inject.TypeLiteral;

public class TransformationNotSatisfiedException extends Exception {

    private final TypeLiteral<?> fromType, toType;
    private final Set<ToolActivation> tools;

    public TransformationNotSatisfiedException(TypeLiteral<?> fromType, TypeLiteral<?> toType, Set<ToolActivation> tools) {
        this.fromType = fromType;
        this.toType = toType;
        this.tools = tools;
    }

    @Override
    public String getMessage() {
        return "Incomplete transformation sequence: Could not transform " + fromType + " to " + toType
                + ".\nValid transformations include: " + tools.toString();
    }

}
