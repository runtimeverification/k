package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

/**
 * A builtin list
 *
 * @author TraianSF
 */
public class ListBuiltin extends CollectionBuiltin {
    private final Collection<Term> elementsRight;

    public ListBuiltin(DataStructureSort sort, Collection<Term> elementsLeft, Collection<Term> elementsRight,
                       Collection<Term> terms) {
        super(sort, elementsLeft, terms);
        this.elementsRight = elementsRight;
    }

    public Collection<Term> elementsLeft() {
        return elements();
    }

    public Collection<Term> elementsRight() {
        return Collections.unmodifiableCollection(elementsRight);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }
}
