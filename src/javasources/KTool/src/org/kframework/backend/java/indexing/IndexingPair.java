// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.backend.java.indexing;

import org.kframework.backend.java.kil.*;
import org.kframework.backend.java.util.Utils;

import java.io.Serializable;


/**
 * @author AndreiS
 */
public class IndexingPair implements Serializable {

    public static final IndexingPair TOP = new IndexingPair(TopIndex.TOP, TopIndex.TOP);

    public static Index getIndex(Term term, Definition definition) {
        if (term instanceof KItem) {
            KItem kItem = (KItem) term;
            if (kItem.kLabel() instanceof KLabelConstant) {
                KLabelConstant kLabel = (KLabelConstant) kItem.kLabel();
                return new KLabelIndex(kLabel);
            } else if (kItem.kLabel() instanceof KLabelFreezer) {
                KLabelFreezer freezer = (KLabelFreezer) kItem.kLabel();
                KItem frozenKItem = (KItem) freezer.term();
                return new FreezerIndex(
                        (KLabelConstant) frozenKItem.kLabel(),
                        ((KList) frozenKItem.kList()).getContents().indexOf(Hole.HOLE));
            }
        } else {
            if (definition.builtinSorts().contains(term.sort())) {
                return new TokenIndex(term.sort());
            }
        }

        return TopIndex.TOP;
    }

    public static IndexingPair getKCellIndexingPair(Cell cell, Definition definition) {
        assert cell.getLabel().equals("k");
        
        Term term = cell.getContent();
        if (term instanceof KSequence) {
            KSequence kSequence = (KSequence) term;

            if (kSequence.size() == 0) {
                if (kSequence.hasFrame()) {
                    return new IndexingPair(TopIndex.TOP, TopIndex.TOP);
                } else {
                    return new IndexingPair(BottomIndex.BOTTOM, BottomIndex.BOTTOM);
                }
            }
            else if (kSequence.size() == 1) {
                if (kSequence.hasFrame()) {
                    return new IndexingPair(getIndex(kSequence.get(0), definition), TopIndex.TOP);
                } else {
                    return new IndexingPair(getIndex(kSequence.get(0), definition), BottomIndex.BOTTOM);
                }
            }
            else {
                return new IndexingPair(
                        getIndex(kSequence.get(0), definition),
                        getIndex(kSequence.get(1), definition));
            }
        } else {
            return new IndexingPair(getIndex(term, definition), BottomIndex.BOTTOM);
        }
    }
    
    /**
     * Retrieves {@code IndexingPair} from an input stream pattern based on the
     * first and last elements.
     * 
     * @param instream
     *            the input stream pattern
     * @param definition
     *            the definition
     * @return the indexing pair
     */
    public static IndexingPair getInstreamIndexingPair(BuiltinList instream, Definition definition) {
        Index fstIndex;
        Index sndIndex;
        
        if (instream.hasFrame()) {
            fstIndex = instream.elementsLeft().isEmpty() ? TopIndex.TOP : getIndex(instream.get(0), definition);
            sndIndex = instream.elementsRight().isEmpty() ? TopIndex.TOP : getIndex(instream.get(-1), definition);
        } else {
            fstIndex = instream.isEmpty() ? BottomIndex.BOTTOM : getIndex(instream.get(0), definition);
            sndIndex = instream.size() < 2 ? BottomIndex.BOTTOM : getIndex(instream.get(-1), definition);
        }
        
        return new IndexingPair(fstIndex, sndIndex);
    }
    
    /**
     * Retrieves {@code IndexingPair} from an output stream pattern based on the
     * first and second elements.
     * 
     * @param outstream
     *            the output stream pattern
     * @param definition
     *            the definition
     * @return the indexing pair
     */
    public static IndexingPair getOutstreamIndexingPair(BuiltinList outstream, Definition definition) {
        Index fstIndex;
        Index sndIndex;
        
        if (outstream.hasFrame()) {
            fstIndex = outstream.elementsLeft().isEmpty() ? TopIndex.TOP : getIndex(outstream.get(0), definition);
            sndIndex = outstream.elementsLeft().size() < 2 ? TopIndex.TOP : getIndex(outstream.get(1), definition);
        } else {
            fstIndex = outstream.isEmpty() ? BottomIndex.BOTTOM : getIndex(outstream.get(0), definition);
            sndIndex = outstream.size() < 2 ? BottomIndex.BOTTOM : getIndex(outstream.get(1), definition);
        }
        
        return new IndexingPair(fstIndex, sndIndex);
    }

    public final Index first;
    public final Index second;

    public IndexingPair(Index first, Index second) {
        this.first = first;
        this.second = second;
    }

    public boolean isUnifiable(IndexingPair pair) {
        return first.isUnifiable(pair.first) && second.isUnifiable(pair.second);
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof IndexingPair)) {
            return false;
        }

        IndexingPair pair = (IndexingPair) object;
        return first.equals(pair.first) && second.equals(pair.second);
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Utils.HASH_PRIME + first.hashCode();
        hash = hash * Utils.HASH_PRIME + second.hashCode();
        return hash;
    }

    @Override
    public String toString() {
        return "(" + first + ", " + second + ")";
    }

}
