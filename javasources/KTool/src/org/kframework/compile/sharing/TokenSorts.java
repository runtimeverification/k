package org.kframework.compile.sharing;

import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;

import java.util.HashSet;
import java.util.Set;


/**
 * Visitor class collecting the names of the sorts with lexical productions (i.e.,
 * Sort ::= Token{..} or Sort ::= Lexical{...}).
 */
public class TokenSorts extends BasicVisitor {

    public TokenSorts(DefinitionHelper definitionHelper) {
		super(definitionHelper);
	}

	private final Set<String> names = new HashSet<String>();

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
    public void visit(Context node) { }

    @Override
    public void visit(Configuration node) { }

}
