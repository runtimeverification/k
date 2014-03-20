package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Builtin list lookup operation. The operation has the form {@code value :=  get(list, key)}
 * where {@code key}  with the semantics that the key element from the list will be retrieved.
 * If {@code key < -1} then the {@code -key} element from the back will be retrieved from list. When
 * resolving a lookup operation during the application of a rule, the variables
 * in {@code value} may be bound by this lookup operation.
 *
 * @author TraianSF  (refactoring from {@link MapLookup})
 */
public class ListLookup extends BuiltinLookup {

    /** {@link Term} representation of the value */
    private final Term value;

    public ListLookup(Variable base, Term key, Term value, KSort kind) {
        super(base, key, kind, false);
        this.value = value;
    }

    public ListLookup(Variable base, int key, Term value, KSort kind) {
        this(base, IntBuiltin.kAppOf(key), value, kind);
    }

    @Override
    public Term value() {
        return value;
    }

    @Override
    public Term shallowCopy() {
        throw new UnsupportedOperationException();
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * Context.HASH_PRIME + base().hashCode();
        hash = hash * Context.HASH_PRIME + key().hashCode();
        hash = hash * Context.HASH_PRIME + value().hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof ListLookup)) {
            return false;
        }

        ListLookup listLookup = (ListLookup) object;
        return base().equals(listLookup.base()) && key().equals(listLookup.key()) && value().equals(listLookup.value());
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
