// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.koreimplementation.convertors;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.builtin.Labels;
import org.kframework.builtin.Sorts;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cell;
import org.kframework.kil.Hole;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Location;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.koreimplementation.*;
import org.kframework.tinyimplementation.Up;

import static org.kframework.koreimplementation.Constructors.*;
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

    private K cellMarker = convert(org.kframework.definition.Configuration.cellMarker());

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
        return InjectedKLabel(KLabel(c.getLabel()), Attributes());
    }

    public org.kframework.koreimplementation.KSequence apply(KSequence seq) {
        return KSequence(apply(seq.getContents()));
    }

    private List<K> apply(List<Term> contents) {
        return contents.stream().map(this).collect(Collectors.toList());
    }

    public org.kframework.koreimplementation.KApply apply(Bracket b) {
        Object content = apply(b.getContent());
        if (content instanceof KList) {
            content = InjectedKList((KList) content);
        }
        return KApply(KLabel("bracket"), KList((K) content));
    }

    public KApply apply(TermCons cons) {
        org.kframework.attributes.Attributes att = attributesFor(cons);
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
                return KApply(applyToLabel(label), (KList) apply(child),
                        convertAttributes(kApp));
            } else if (child instanceof org.kframework.kil.Variable) {
                return KApply(applyToLabel(label), KList(apply(child)), convertAttributes(kApp));
            } else {
                throw new AssertionError("encountered " + child.getClass() + " in a KApp");
            }
        }
    }

    public KLabel applyToLabel(Term label) {
        if (label instanceof KLabelConstant) {
            return KLabel(((KLabelConstant) label).getLabel());
        } else if (label instanceof KApp) {
            throw new RuntimeException(label.toString());
        } else if (label instanceof Variable) {
            return (KLabel) apply(label);
        }
        throw new RuntimeException(label.getClass().toString());
    }

    public KList apply(org.kframework.kil.KList kList) {
        return (KList) kList.getContents().stream().map(this).collect(toKList());
    }

    private org.kframework.attributes.Attributes attributesFor(TermCons cons) {
        String uniqueishID = "" + System.identityHashCode(cons.getProduction());
        org.kframework.attributes.Attributes att = sortAttributes(cons).add(PRODUCTION_ID, uniqueishID);
        return att;
    }

    private org.kframework.attributes.Attributes sortAttributes(Term cons) {

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
        Object right = apply(r.getRight());
        if (right instanceof KList)
            right = InjectedKList((KList) right);

        Object left = apply(r.getLeft());
        if (left instanceof KList)
            left = InjectedKList((KList) left);

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

    public org.kframework.attributes.Attributes convertAttributes(ASTNode t) {
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

    private org.kframework.attributes.Attributes attributesFromLocation(Location location) {
        if (location != null) {
            org.kframework.attributes.Location koreLocation = org.kframework.attributes.Location.apply(location.lineStart, location.columnStart, location.lineEnd, location.columnEnd);
            return org.kframework.attributes.Attributes.apply(Set(Up.apply(koreLocation)));
        } else
            return Attributes();
    }
}
