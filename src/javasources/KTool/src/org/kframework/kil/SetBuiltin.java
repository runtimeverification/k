package org.kframework.kil;

import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import static java.util.Collections.emptySet;

/**
 * A builtin set
 *
 * @author TraianSF
 */
public class SetBuiltin extends CollectionBuiltin {
    public SetBuiltin(DataStructureSort sort, Collection<Term> baseTerms, java.util.Collection<Term> elements) {
        super(sort, baseTerms, elements);
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }
}
