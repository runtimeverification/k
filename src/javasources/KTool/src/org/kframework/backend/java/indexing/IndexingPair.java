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

    public static IndexingPair getIndexingPair(Term term, Definition definition) {
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
