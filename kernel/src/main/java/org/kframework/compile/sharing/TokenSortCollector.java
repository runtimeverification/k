// Copyright (c) 2013-2015 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import java.util.HashSet;
import java.util.Set;

/**
 * Visitor collecting the names of the sorts with lexical productions (i.e.,
 * Sort ::= Token{..} or Sort ::= Lexical{...}).
 *
 * @author AndreiS
 */
public class TokenSortCollector extends BasicVisitor {

    private final Set<Sort> tokenSorts = new HashSet<>();

    private final Set<Sort> nonTokenSorts = new HashSet<>();

    /**
     * Collects the names of all token sorts within a specified
     * {@code Definition}.
     *
     * @param definition
     *            the specified definition
     * @param context
     *            the context
     * @return a set representing the names of all token sorts
     *
     * @see TokenSortCollector
     */
    public static Set<Sort> collectTokenSorts(ASTNode definition, Context context) {
        TokenSortCollector collector = new TokenSortCollector(context);
        collector.visitNode(definition);
        return collector.tokenSorts;
    }

    private KompileOptions kompileOptions;

    private TokenSortCollector(Context context) {
        super(context);
        this.kompileOptions = context.kompileOptions;
    }

    @Override
    public Void visit(Production production, Void _void) {
        if (!kompileOptions.experimental.legacyKast) {
            checkIllegalProduction(production);
        } else {
            if (production.isLexical() && !production.containsAttribute(Constants.VARIABLE)) {
                tokenSorts.add(production.getSort());
            }
        }
        return null;
    }

    /**
     * Checks if a specified production is valid w.r.t. its sort: namely, a
     * lexical production should have a token sort and a non-lexical production
     * should have a non-token sort. Throws a K exception when one of the two
     * restrictions is violated. Currently, this check is only enabled in the
     * Java backend.
     *
     * @param production
     *            the specified production
     */
    private void checkIllegalProduction(Production production) {
        Sort sort = production.getSort();

        if (production.isLexical() && !production.containsAttribute(Constants.VARIABLE)) {
            if (nonTokenSorts.contains(sort)) {
                String msg = "Cannot subsort a lexical production to a non-token sort:\nsyntax "
                        + sort + " ::= " + production;
                throw KExceptionManager.compilerError(msg,
                        this, production);
            }

            tokenSorts.add(sort);
        }

        // (radum) removed since it doesn't comply with the filosophy of the new parser.
        // once the new parser is fully functional, this entire class should be removed at the same time with SDF.
    }

    @Override
    public Void visit(Rule node, Void _void) {
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _void) {
        return null;
    }

    @Override
    public Void visit(Configuration node, Void _void) {
        return null;
    }

}
