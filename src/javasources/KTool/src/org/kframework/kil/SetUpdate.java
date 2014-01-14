package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.Collections;
import java.util.Collection;


/**
 * Builtin set update operation.
 *
 * @author TraianSF (refactoring from {@link org.kframework.kil.MapUpdate})
 */
public class SetUpdate extends Term {

    /** {@link org.kframework.kil.Variable} name of the set */
    private final Variable set;

    /** {@code Map} of entries to be removed from the set */
    private final  Collection<Term> removeEntries;

    public SetUpdate(Variable set, Collection<Term> removeEntries) {
        super(set.getSort());
        this.set = set;
        this.removeEntries = removeEntries;
    }

    public Variable set() {
        return set;
    }

    public Collection<Term> removeEntries() {
        return Collections.unmodifiableCollection(removeEntries);
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + set.hashCode();
        hash = hash * Context.HASH_PRIME + removeEntries.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof SetUpdate)) {
            return false;
        }

        SetUpdate mapUpdate = (SetUpdate) object;
        return set.equals(mapUpdate.set) && removeEntries.equals(mapUpdate.removeEntries);
    }

    @Override
    public void accept(Matcher matcher, Term toMatch) {
        throw new UnsupportedOperationException();
    }

    @Override
    public ASTNode accept(Transformer transformer) throws TransformerException {
        return transformer.transform(this);
    }

    @Override
    public void accept(Visitor visitor) {
        visitor.visit(this);
    }

}
