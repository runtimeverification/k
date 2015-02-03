// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.kil;

import java.io.Serializable;
import java.util.List;

import com.google.common.collect.ImmutableList;


public class SortSignature implements Serializable {
    private final ImmutableList<Sort> parameters;
    private final Sort result;

    public SortSignature(ImmutableList<Sort> parameters, Sort result) {
        this.parameters = parameters;
        this.result = result;
    }

    public List<Sort> parameters() {
        return parameters;
    }

    public Sort result() {
        return result;
    }
}
