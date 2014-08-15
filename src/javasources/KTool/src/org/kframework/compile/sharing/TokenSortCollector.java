// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.sharing;

import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kompile.KompileOptions;
import org.kframework.utils.general.GlobalSettings;

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
    public static Set<Sort> collectTokenSorts(Definition definition, Context context) {
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
    public Void visit(Production production, Void _) {
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
                GlobalSettings.kem.registerCompilerError(msg,
                        this, production);
            }

            tokenSorts.add(sort);
        }

        /*
         * The second and third check above is used to filter out cases such as the following:
         *   syntax Id ::= "Main"
         *   syntax Id ::= "String2Id" "(" String ")"  [function, klabel(String2Id)]
         */
        if (!production.isLexical() && !production.isTerminal()
                && !production.containsAttribute(Constants.FUNCTION))  {
            if (tokenSorts.contains(sort)) {
                String msg = "Cannot subsort a non-lexical production to a token sort:\nsyntax "
                        + sort + " ::= " + production;
                GlobalSettings.kem.registerCompilerError(msg, this, production);
            }

            nonTokenSorts.add(sort);
        }
    }

    @Override
    public Void visit(Rule node, Void _) {
        return null;
    }

    @Override
    public Void visit(org.kframework.kil.Context node, Void _) {
        return null;
    }

    @Override
    public Void visit(Configuration node, Void _) {
        return null;
    }

}
