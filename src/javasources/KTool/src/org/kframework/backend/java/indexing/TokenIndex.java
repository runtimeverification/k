package org.kframework.backend.java.indexing;


/**
 * @author AndreiS
 */
public class TokenIndex implements Index {

    private final String sort;

    public TokenIndex(String sort) {
        this.sort = sort;
    }
    
    public String sort() {
        return sort;
    }

    @Override
    public boolean isUnifiable(Index index) {
        return index instanceof TopIndex
                || equals(index)
                /*
                 * TokenSort can also have non-lexical productions and,
                 * therefore, it's possible to match a TokenIndex with a
                 * KLabelIndex. For instance, consider the following productions
                 * and rule:
                 * 
                 * syntax Name ::= some lexical production
                 *               | "$h"
                 *               
                 * rule X:Name => .      
                 * 
                 * The above rule should be able to match when "$h" appears 
                 * on top of the k cell.
                 */
                || (index instanceof KLabelIndex && 
                        ((KLabelIndex) index).kLabel().sorts().contains(sort));
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof TokenIndex)) {
            return false;
        }

        TokenIndex index = (TokenIndex) object;
        return sort.equals(index.sort);
    }

    @Override
    public int hashCode() {
        return sort.hashCode();
    }

    @Override
    public String toString() {
        return "@" + sort;
    }

}
