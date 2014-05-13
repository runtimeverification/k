// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.UIDesign;

import java.awt.Shape;
import edu.uci.ics.jung.graph.Graph;
import edu.uci.ics.jung.visualization.decorators.EllipseVertexShapeTransformer;

class ClusterVertexShapeFunction<V> extends EllipseVertexShapeTransformer<V> {

    ClusterVertexShapeFunction() {
        setSizeTransformer(new ClusterVertexSizeFunction<V>(40));
    }

    @SuppressWarnings("rawtypes")
    @Override
    public Shape transform(V v) {
        if (v instanceof Graph) {
            int size = ((Graph) v).getVertexCount();
            if (size < 8) {
                int sides = Math.max(size, 3);
                return factory.getRegularPolygon(v, sides);
            } else {
                return factory.getRegularStar(v, size);

            }
        }
        return super.transform(v);
    }

}