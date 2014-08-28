package org.kframework.transformation;

import org.kframework.kil.Attributes;

public interface Transformation<P, R> {

    public R run(P p, Attributes attrs);

    public String getName();
}
