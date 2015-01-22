// Copyright (c) 2014-2015 K Team. All Rights Reserved.
package org.kframework.transformation;

import java.util.ArrayList;
import java.util.List;

import com.google.common.base.Joiner;

public class AmbiguousTransformationException extends Exception {

    private Transformation<?, ?>[] transformations;

    public AmbiguousTransformationException(Transformation<?, ?>... transformations) {
        this.transformations = transformations;
    }

    @Override
    public String getMessage() {
        StringBuilder sb = new StringBuilder();
        sb.append("Ambiguous transformations activated: \"");
        List<String> parts = new ArrayList<>(transformations.length);
        for (Transformation<?, ?> trans : transformations) {
            parts.add(trans.getName());
        }
        Joiner.on("\", \"").appendTo(sb, parts);
        sb.append("\"");
        return sb.toString();
    }
}
