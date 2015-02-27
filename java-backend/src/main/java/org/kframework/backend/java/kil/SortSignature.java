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

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result
                + ((parameters == null) ? 0 : parameters.hashCode());
        result = prime * result
                + ((this.result == null) ? 0 : this.result.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        SortSignature other = (SortSignature) obj;
        if (parameters == null) {
            if (other.parameters != null)
                return false;
        } else if (!parameters.equals(other.parameters))
            return false;
        if (result == null) {
            if (other.result != null)
                return false;
        } else if (!result.equals(other.result))
            return false;
        return true;
    }
}
