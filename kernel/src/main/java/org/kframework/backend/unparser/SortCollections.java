// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.unparser;

import java.awt.Color;
import java.util.Collections;
import java.util.Comparator;
import org.kframework.compile.utils.ConfigurationStructureMap;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.ListBuiltin;
import org.kframework.kil.MapBuiltin;
import org.kframework.kil.SetBuiltin;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.krun.ColorSetting;

public class SortCollections extends CopyOnWriteTransformer {

    private Comparator<Term> comparator = new Comparator<Term>() {

        @Override
        public int compare(Term o1, Term o2) {
            // case 1: one of o1 and o2 is a cell
            if ((o1 instanceof Cell) && !(o2 instanceof Cell)
                    || !(o1 instanceof Cell) && (o2 instanceof Cell)) {
                return o1 instanceof Cell ? -1 : 1;
            }

            // case 2: o1 and o2 are cells with different labels
            if (o1 instanceof Cell && o2 instanceof Cell
                    && (!((Cell) o1).getLabel().equals(((Cell) o2).getLabel()))) {
                Cell c1 = (Cell) o1;
                Cell c2 = (Cell) o2;
                ConfigurationStructureMap sons = context.getConfigurationStructureMap().get(c1.getLabel()).parent.sons;
                assert sons == context.getConfigurationStructureMap().get(c2.getLabel()).parent.sons;
                return sons.positionOf(c1.getLabel()) < sons.positionOf(c2.getLabel()) ? -1 : 1;
            }

            return unparser.compare(o1, o2);
        }
    };

    private final Unparser unparser;

    public SortCollections(Context context, Term termToSort) {
        super("Sort collections", context);
        unparser = new Unparser(context, ColorSetting.OFF, Color.BLACK);
    }

    @Override
    public ASTNode visit(Bag node, Void p) throws RuntimeException {
        Bag sorted = (Bag) super.visit(node, p);
        Collections.sort(sorted.getContents(), comparator);
        return sorted;
    }

    @Override
    public ASTNode visit(SetBuiltin node, Void _void) {
        return ((SetBuiltin)super.visit(node, _void)).toKApp(context, comparator);
    }

    @Override
    public ASTNode visit(ListBuiltin node, Void _void) {
        return ((ListBuiltin)super.visit(node, _void)).toKApp(context, comparator);
    }

    @Override
    public ASTNode visit(MapBuiltin node, Void _void) {
        return ((MapBuiltin)super.visit(node, _void)).toKApp(context, comparator);
    }
}
