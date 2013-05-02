package org.kframework.kil;

import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.matchers.Matcher;
import org.kframework.kil.visitors.Transformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.HashMap;
import java.util.Map;


/**
 * Created with IntelliJ IDEA.
 * User: andrei
 * Date: 4/16/13
 * Time: 11:43 PM
 * To change this template use File | Settings | File Templates.
 */
public class Token extends Term {

    /*
     * HashMap caches the constants to ensure uniqueness
     */
    private static Map<Token, Token> cache = new HashMap<Token, Token>();

    public static Token of(String sort, String value) {
        return Token.of(StringBuiltin.of(sort), StringBuiltin.of(value));
    }

    public static Token of(Term sortTerm, Term valueTerm) {
        Token token = new Token(sortTerm, valueTerm);
        if (cache.get(token) == null) {
            cache.put(token, token);
        }
        return cache.get(token);
    }

    private final Term sortTerm;
    private final Term valueTerm;

    private Token(Term sortTerm, Term valueTerm) {
        this.sortTerm = sortTerm;
        this.valueTerm = valueTerm;
    }

    public Term getSortTerm() {
        return sortTerm;
    }

    public Term getValueTerm() {
        return valueTerm;
    }

    @Override
    public Term shallowCopy() {
        /* this object is immutable */
        return this;
    }

    @Override
    public int hashCode() {
        int hash = 1;
        hash = hash * DefinitionHelper.HASH_PRIME + sortTerm.hashCode();
        hash = hash * DefinitionHelper.HASH_PRIME + valueTerm.hashCode();
        return hash;
    }

    @Override
    public boolean equals(Object object) {
        /* the cache ensures uniqueness of logically equal object instances */
        return this == object;
    }

    @Override
    public String toString() {
        return "#token(" + sortTerm + ", " + valueTerm + ")";
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
