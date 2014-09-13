// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign;

import org.apache.commons.collections15.Transformer;
import edu.uci.ics.jung.graph.Graph;

class ClusterVertexSizeFunction<V> implements Transformer<V, Integer> {

    private int size;

    public ClusterVertexSizeFunction(Integer size) {
        this.size = size;
    }

    public Integer transform(V v) {
        if (v instanceof Graph) {
            return 50;
        }
        return size;
    }
}