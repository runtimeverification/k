package org.kframework.backend.java.indexing;

import org.kframework.backend.java.kil.Definition;
import org.kframework.backend.java.kil.Hole;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KLabelFreezer;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Sorted;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.Utils;

import java.io.Serializable;


/**
 * @author AndreiS
 */
public class IndexingPair implements Serializable {

    public static final IndexingPair TOP = new IndexingPair(TopIndex.TOP, TopIndex.TOP);

    public static Index getIndex(Term term) {
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
                        frozenKItem.kList().getItems().indexOf(Hole.HOLE));
            }
        } else if (term instanceof Sorted) {
            Sorted sorted = (Sorted) term;
            if (Definition.TOKEN_SORTS.contains(sorted.sort())) {
                return new TokenIndex(sorted.sort());
            }
        }

        return TopIndex.TOP;
    }

    public static IndexingPair getIndexingPair(Term term) {
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
                    return new IndexingPair(getIndex(kSequence.get(0)), TopIndex.TOP);
                } else {
                    return new IndexingPair(getIndex(kSequence.get(0)), BottomIndex.BOTTOM);
                }
            }
            else {
                return new IndexingPair(getIndex(kSequence.get(0)), getIndex(kSequence.get(1)));
            }
        } else {
            return new IndexingPair(getIndex(term), BottomIndex.BOTTOM);
        }
    }

    private final Index first;
    private final Index second;

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
