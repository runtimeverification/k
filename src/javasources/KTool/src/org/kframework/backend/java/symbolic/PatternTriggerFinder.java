package org.kframework.backend.java.symbolic;

import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.MapLookup;

import java.util.ArrayList;
import java.util.List;

/**
 * @author AndreiS
 */
public class PatternTriggerFinder extends BottomUpVisitor {

    public final List<KItem> patterns = new ArrayList<>();

    @Override
    public void visit(MapLookup mapLookup) {
        for (KItem pattern : BuiltinMapUtils.getMapPatterns(mapLookup.map())) {
            // TODO(AndreiS): refine to only consider input parameters
            if (((KList) pattern.kList()).getContents().contains(mapLookup.key())) {
                patterns.add(pattern);
            }
        }
    }

}
