package org.kframework.kil;

import java.util.Collection;
import java.util.Collections;
import java.util.Set;

import static java.util.Collections.emptySet;

/**
 * Created with IntelliJ IDEA.
 * User: Traian
 * Date: 02.07.2013
 * Time: 12:40
 * To change this template use File | Settings | File Templates.
 */
public class SetBuiltin extends CollectionBuiltin {
    private final Set<Term> removeElements;
    public SetBuiltin(DataStructureSort sort, java.util.Collection<Term> elements, Collection<Term> terms) {
        super(sort, elements, terms);
        this.removeElements = Collections.<Term>emptySet();
    }
}
