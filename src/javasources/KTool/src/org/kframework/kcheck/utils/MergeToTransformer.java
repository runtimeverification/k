// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.kcheck.utils;

import java.util.LinkedList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.KSorts;
import org.kframework.kil.Term;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;

public class MergeToTransformer extends CopyOnWriteTransformer {

    private Term toMerge;

    public MergeToTransformer(Context context, Term toMerge) {
        super("Left merge of a term into accepting term", context);
        this.toMerge = toMerge;
    }

    @Override
    public ASTNode visit(Cell node, Void _)  {
//
//        // retrieve the content of the left hand side
//        ExtractCellContent ecc = new ExtractCellContent(context,
//                node.getLabel());
//        ecc.visitNode(toMerge);
//        Term lcontent = ecc.getContent();
//
//        if (lcontent != null) {
//            // Then, do "sort case" merging
//            String sort = node.getContents().getSort();
//            Cell newCell = node.shallowCopy();
//            if (context.isSubsortedEq(KSorts.K, sort)) {
//                // K: replace the entire content - this is mainly for the K cell
//                newCell.setContents(lcontent);
//                return newCell;
//            } else if (sort.equals(KSorts.MAP)) {
//                // Map: append all the MapItems except variables of any kind
//                Map rmap = (Map) node.getContents();
//                Map lmap = (Map) lcontent;
//
//                List<Term> terms = new LinkedList<Term>();
//
//                for (Term term : rmap.getContents()) {
//                    terms.add(term);
//                }
//                for (Term term : lmap.getContents()) {
//                    if (!(term instanceof Variable))
//                        if (term instanceof MapItem) {
//                            MapItem mapItem = (MapItem) term;
//                            Term texist = null;
//                            for (Term t : terms) {
//                                if (((MapItem)t).getKey().equals(mapItem.getKey())) {
//                                    texist = t;
//                                }
//                            }
//                            if (texist != null) {
//                                terms.remove(texist);
//                            }
//                            terms.add(term);
//                        }
//                }
//                newCell.setContents(new Map(terms));
//                return newCell;
//            }
//        }
//        // System.out.println("Node: " + node + "\nLL: " + lcontent + "\n\n");

        return super.visit(node, _);
    }

}
