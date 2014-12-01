// Copyright (c) 2014 K Team. All Rights Reserved.

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

import org.kframework.kil.ASTNode;
import org.kframework.kil.AbstractVisitor;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Configuration;
import org.kframework.kil.Definition;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.Lexical;
import org.kframework.kil.LiterateModuleComment;
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
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kore.*;
import org.kframework.kore.outer.*;

import scala.Enumeration.Value;
import scala.collection.Seq;

import com.google.common.collect.Sets;

import static org.kframework.kore.outer.Constructors.*;
import static org.kframework.kore.Constructors.*;

@SuppressWarnings("unused")
public class KILtoInnerKORE extends KILTransformation<K> {

    public static final String PRODUCTION_ID = "productionID";

    public K apply(Bag body) {
        List<K> contents = body.getContents().stream().map(this).collect(Collectors.toList());
        return KBag(KList(contents));
    }

    private KApply cellMarker = org.kframework.kore.outer.Configuration.cellMarker();

    @SuppressWarnings("unchecked")
    public KApply apply(Cell body) {
        K x = apply(body.getContents());
        if (x instanceof KBag && !((KBag) x).isEmpty()) {
            return KApply(KLabel(body.getLabel()), KList(((KBag) x)), Attributes(cellMarker));
        } else {
            return KApply(KLabel(body.getLabel()), KList(x), Attributes(cellMarker));
        }
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

    private org.kframework.kore.Attributes attributesFor(TermCons cons) {
        String uniqueishID = "" + System.identityHashCode(cons.getProduction());
        org.kframework.kore.Attributes att = sortAttributes(cons).add(PRODUCTION_ID, uniqueishID);
        return att;
    }

    private org.kframework.kore.Attributes sortAttributes(Term cons) {

        return apply(cons.getAttributes()).add(
                Attributes(KApply(KLabel("sort"),
                        KList(KToken(Sorts.KString, KString(cons.getSort().toString()))))));
    }

    public KApply apply(Hole hole) {
        return KApply(Hole(), KList(KToken(Sort(hole.getSort().getName()), KString(""))),
                sortAttributes(hole));
    }

    public KVariable apply(Variable v) {
        return KVariable(v.getName(), sortAttributes(v));
    }

    public KRewrite apply(Rewrite r) {
        return KRewrite(apply(r.getLeft()), apply(r.getRight()), sortAttributes(r));
    }

    public K applyOrTrue(Term t) {
        if (t != null)
            return apply(t);
        else
            return new KBoolean(true, Attributes());
    }

    public org.kframework.kore.Attributes apply(Attributes attributes) {
        Set<K> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String keyString = key.toString();
                    String valueString = attributes.get(key).getValue().toString();

                    return (K) KApply(KLabel(keyString),
                            KList(KToken(Sort("AttributeValue"), KString(valueString))));
                }).collect(Collectors.toSet());

        return Attributes(KList(attributesSet));
    }
}
