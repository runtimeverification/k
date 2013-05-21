package org.kframework.compile.sharing;

import org.kframework.kil.Configuration;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;


/**
 * Visitor collecting the names of the sorts with lexical productions (i.e.,
 * Sort ::= Token{..} or Sort ::= Lexical{...}).
 *
 * @author AndreiS
 */
public class TokenSorts extends BasicVisitor {

    private final Set<String> names = new HashSet<String>();

    public TokenSorts(Context context) {
		super(context);
	}

    public Set<String> getNames() {
        return names;
    }

    @Override
    public void visit(Production production) {
        if (production.isLexical()) {
            names.add(production.getSort());
        }
    }

    @Override
    public void visit(Rule node) { }

    @Override
    public void visit(org.kframework.kil.Context node) { }

    @Override
    public void visit(Configuration node) { }

}
