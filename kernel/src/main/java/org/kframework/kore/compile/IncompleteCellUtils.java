// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.List;

import static org.kframework.kore.KORE.*;

/**
 * Utility methods for dealing with cells as seen in Full K.
 * These are represented in kast by applying the cell label
 * to three argument - (left dots, body, right dots)
 * rather than the arity declared in their production.
 * dots are represented with an application #dots() or #noDots()
 * Multiple cells, rewrites, or other items are joined into
 * a single argument by using the label #cells
 * (which this class will allow with arbitrary arity).
 */
public class IncompleteCellUtils {
    private final static KApply dots = KApply(KLabel("#dots"));
    private final static KApply noDots = KApply(KLabel("#noDots"));

    private static boolean isOpen(K flag) {
        if (dots.equals(flag)) {
            return true;
        } else if (noDots.equals(flag)) {
            return false;
        } else {
            throw KEMException.criticalError("Instead of #dots() or #noDots(), got " + flag);
        }
    }

    public static boolean isOpenLeft(KApply cell) {
        return isOpen(cell.klist().items().get(0));
    }
    public static boolean isOpenRight(KApply cell) {
        return isOpen(cell.klist().items().get(2));
    }

    private static void flattenCells(List<K> children, K item) {
        if (item instanceof KApply && ((KApply)item).klabel().name().equals("#cells")) {
            for (K deeper : ((KApply) item).klist().items()) {
                flattenCells(children, deeper);
            }
        } else {
            children.add(item);
        }
    }
    public static List<K> flattenCells(K cells) {
        List<K> children = new ArrayList<K>();
        flattenCells(children, cells);
        return children;
    }

    public static List<K> getChildren(KApply cell) {
        return flattenCells(cell.klist().items().get(1));
    }

    private static KApply makeDots(boolean isOpen) {
        return isOpen ? dots : noDots;
    }
    private static K makeBody(List<? extends K> children) {
        if (children.size() == 1) {
            return children.get(0);
        } else {
            return KApply(KLabel("#cells"), KList(children));
        }
    }

    public static KApply make(KLabel label, boolean openLeft, K child, boolean openRight) {
        return KApply(label, KList(makeDots(openLeft), child, makeDots(openRight)));
    }
    public static KApply make(KLabel label, boolean openLeft, List<? extends K> children, boolean openRight) {
        return KApply(label, KList(makeDots(openLeft), makeBody(children), makeDots(openRight)));
    }
}