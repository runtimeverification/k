// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import org.kframework.builtin.Labels;
import org.kframework.builtin.Sorts;
import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.Int32Builtin;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.Lexical;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.Location;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.NonTerminal;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.PriorityExtended;
import org.kframework.kil.PriorityExtendedAssoc;
import org.kframework.kil.Production;
import org.kframework.kil.Require;
import org.kframework.kil.Restrictions;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sentence;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kore.*;
import org.kframework.kore.outer.*;
import org.kframework.utils.StringBuilderUtil;

import scala.Enumeration.Value;
import scala.collection.Seq;

import com.google.common.collect.Sets;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;
import static org.kframework.Collections.*;

@SuppressWarnings("unused")
public class KILtoInnerKORE extends KILTransformation<K> {

    private Context context;

    public KILtoInnerKORE(org.kframework.kil.loader.Context context) {
        this.context = context;
    }

    public static final String PRODUCTION_ID = "productionID";
    public static final String LIST_TERMINATOR = "listTerminator";

    public K apply(Bag body) {
        List<K> contents = body.getContents().stream().map(this).collect(Collectors.toList());
        return KApply(Labels.KBag(), (KList(contents)));
    }

    // public K apply(TermComment c) {
    // return KList();
    // }

    private KApply cellMarker = org.kframework.kore.outer.Configuration.cellMarker();

    @SuppressWarnings("unchecked")
    public KApply apply(Cell body) {
        // K x = ;
        // if (x instanceof KApply && ((KApply) x).klabel() == Labels.KBag()
        // && ((KApply) x).size() == 0) {
        return KApply(KLabel(body.getLabel()), KList(apply(body.getContents())),
                Attributes(cellMarker));
        // } else {
        // return KApply(KLabel(body.getLabel()), KList(x),
        // Attributes(cellMarker));
        // }
    }

    public K apply(org.kframework.kil.KLabelConstant c) {
        return InjectedKLabel(KLabel(c.getLabel()));
    }

    public org.kframework.kore.KSequence apply(KSequence seq) {
        return KSequence(apply(seq.getContents()));
    }

    private List<K> apply(List<Term> contents) {
        return contents.stream().map(this).collect(Collectors.toList());
    }

    public KApply apply(TermCons cons) {
        org.kframework.kore.Attributes att = attributesFor(cons);
        return KApply(KLabel(cons.getProduction().getKLabel()), KList(apply(cons.getContents())),
                att);
    }

    public KApply apply(ListTerminator t) {
        Production production = context.listProductions.get(t.getSort());
        String terminatorKLabel = production.getTerminatorKLabel();

        // NOTE: we don't covert it back to ListTerminator because Radu thinks
        // it is not necessary

        return KApply(KLabel(terminatorKLabel), KList(), Attributes().add(LIST_TERMINATOR));
    }

    public K apply(KApp kApp) {
        Term label = kApp.getLabel();

        if (label instanceof Token) {
            return KToken(Sort(((Token) label).tokenSort().getName()), ((Token) label).value());
        } else {
            Term child = kApp.getChild();

            if (child instanceof org.kframework.kil.KList) {
                return KApply(KLabel(((KLabelConstant) label).getLabel()), (KList) apply(child),
                        convertAttributes(kApp));
            } else if (child instanceof org.kframework.kil.Variable) {
                // System.out.println(label.getClass());
                return KApply(null, KList(apply(child)), convertAttributes(kApp));
            } else {
                throw new AssertionError("encountered " + child.getClass() + " in a KApp");
            }
        }
    }

    public KList apply(org.kframework.kil.KList kList) {
        return (KList) kList.getContents().stream().map(this).collect(toKList());
    }

    private org.kframework.kore.Attributes attributesFor(TermCons cons) {
        String uniqueishID = "" + System.identityHashCode(cons.getProduction());
        org.kframework.kore.Attributes att = sortAttributes(cons).add(PRODUCTION_ID, uniqueishID);
        return att;
    }

    private org.kframework.kore.Attributes sortAttributes(Term cons) {

        return convertAttributes(cons).addAll(
                Attributes(KApply(KLabel("sort"),
                        KList(KToken(Sorts.KString(), cons.getSort().toString())))));
    }

    public KApply apply(Hole hole) {
        return KApply(Labels.Hole(), KList(KToken(Sort(hole.getSort().getName()), "")),
                sortAttributes(hole));
    }

    public KVariable apply(Variable v) {
        return KVariable(v.getName(), sortAttributes(v));
    }

    public KRewrite apply(Rewrite r) {
        org.kframework.Term right = apply(r.getRight());
        if (!(right instanceof K))
            right = new InjectedKList((KList) right);

        org.kframework.Term left = apply(r.getLeft());
        if (!(left instanceof K))
            left = new InjectedKList((KList) left);

        return KRewrite((K) left, (K) right, sortAttributes(r));
    }

    public K applyOrTrue(Term t) {
        if (t != null)
            return apply(t);
        else
            return KToken(Sorts.KBoolean(), "true");
    }

    public K apply(TermComment t) {
        return KSequence();
    }

    public org.kframework.kore.Attributes convertAttributes(ASTNode t) {
        Attributes attributes = t.getAttributes();

        Set<K> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String keyString = key.toString();
                    String valueString = attributes.get(key).getValue().toString();

                    return (K) KApply(KLabel(keyString),
                            KList(KToken(Sort("AttributeValue"), valueString)));
                }).collect(Collectors.toSet());

        return Attributes(immutable(attributesSet))
                .addAll(attributesFromLocation(t.getLocation()));
    }

    private org.kframework.kore.Attributes attributesFromLocation(Location location) {
        if (location != null)
            return Attributes(Location(location.lineStart, location.columnStart, location.lineEnd,
                    location.columnEnd));
        else
            return Attributes();
    }
}
