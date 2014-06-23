// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.kil.loader;

import java.util.HashMap;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cast;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.FreezerHole;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSorts;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.w3c.dom.Element;

/**
 * Factory for creating KIL classes from XML nodes. Must call startConstruction/endConstruction around calls to getTerm, to supply a Context.
 */
public class JavaClassesFactory {
    private static Context context = null;

    /** Set the context to use */
    public static synchronized void startConstruction(Context context) {
        assert JavaClassesFactory.context == null;
        JavaClassesFactory.context = context;
    }

    public static synchronized void endConstruction() {
        assert JavaClassesFactory.context != null;
        JavaClassesFactory.context = null;
    }

    public static ASTNode getTerm(Element element) {
        assert context != null;
        // used for a new feature - loading java classes at first step (Basic Parsing)
        if (Constants.RULE.equals(element.getNodeName()))
            return new Rule(element);
        if (Constants.SENTENCE.equals(element.getNodeName()))
            return new Sentence(element);
        if (Constants.REWRITE.equals(element.getNodeName()))
            return new Rewrite(element, context);
        if (Constants.TERM.equals(element.getNodeName())) {
            assert context != null;
            return new TermCons(element, context);
        }
        if (Constants.BRACKET.equals(element.getNodeName()))
            return new Bracket(element);
        if (Constants.CAST.equals(element.getNodeName()))
            return new Cast(element);
        if (Constants.VAR.equals(element.getNodeName()))
            return new Variable(element);
        if (Constants.CONST.equals(element.getNodeName())) {
            if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.KLABEL)) {
                return new KLabelConstant(element);
            } else {
                // builtin token or lexical token
                return Token.kAppOf(element);
            }
        }
        if (Constants.KAPP.equals(element.getNodeName()))
            return new KApp(element, context);
        if (KSorts.KLIST.equals(element.getNodeName()))
            return new KList(element);
        if (Constants.EMPTY.equals(element.getNodeName())) {
            if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.K)) {
                return KSequence.EMPTY;
            } else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.KLIST)) {
                return KList.EMPTY;
            } else if (element.getAttribute(Constants.SORT_sort_ATTR).equals(KSorts.BAG)) {
                return Bag.EMPTY;
            } else {
                // user defined empty list
                return new ListTerminator(element, null);
            }
        }
        if (Constants.CONFIG.equals(element.getNodeName()))
            return new Configuration(element);
        if (Constants.CELL.equals(element.getNodeName()))
            return new Cell(element);
        if (Constants.BREAK.equals(element.getNodeName()))
            return new TermComment(element);
        if (KSorts.BAG.equals(element.getNodeName()))
            return new Bag(element);
        if (KSorts.BAG_ITEM.equals(element.getNodeName()))
            return new BagItem(element);
        if (Constants.KSEQUENCE.equals(element.getNodeName()))
            return new KSequence(element);
        if (Constants.CONTEXT.equals(element.getNodeName()))
            return new org.kframework.kil.Context(element);
        if (Constants.HOLE.equals(element.getNodeName()))
            return Hole.KITEM_HOLE;
        if (Constants.FREEZERHOLE.equals(element.getNodeName()))
            return new FreezerHole(element);
        if (Constants.DEFINITION.equals(element.getNodeName()))
            return new Definition(element);
        if (Constants.AMB.equals(element.getNodeName()))
            return new Ambiguity(element);
        if (Constants.TAG.equals(element.getNodeName()))
            return new Attribute(element);
        if (Constants.ATTRIBUTES.equals(element.getNodeName()))
            return new Attributes(element);

        System.out.println(">>> " + element.getNodeName() + " <<< - unimplemented yet: org.kframework.kil.loader.JavaClassesFactory");
        return null;
    }

    private static java.util.Map<Integer, ASTNode> cache = new HashMap<Integer, ASTNode>();

    public static void clearCache() {
        cache.clear();
    }
}
