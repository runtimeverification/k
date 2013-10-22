package org.kframework.kil;

import org.kframework.kil.loader.Context;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;


/**
 * Builtin map lookup operation. The operation has the form {@code value := map[key]} with
 * the semantics that {@code map} contains an entry matching the form {@code key |-> value}. When
 * resolving a lookup operation during the application a rule, the variables in {@code key} must
 * be already bound, while the variables in {@code value} may be bound by this lookup  operation.
 *
 * @author AndreiS
 */
public class MapLookup extends BuiltinLookup {

    /** {@link Term} representation of the value */
    private final Term value;

    public MapLookup(Variable base, Term key, Term value) {
        super(base, key);
        this.value = value;
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
        hash = hash * Context.HASH_PRIME + value.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        if (this == object) {
            return true;
        }

        if (!(object instanceof MapLookup)) {
            return false;
        }

        MapLookup mapLookup = (MapLookup) object;
        return base().equals(mapLookup.base()) && key().equals(mapLookup.key())
               && value.equals(mapLookup.value);
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
