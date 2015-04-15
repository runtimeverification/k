// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.kframework.attributes.*;
import org.kframework.builtin.Labels;
import org.kframework.builtin.Sorts;
import org.kframework.kil.*;
import org.kframework.kil.KSequence;
import org.kframework.kil.loader.Context;
import org.kframework.kore.*;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.meta.Up;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

@SuppressWarnings("unused")
public class KILtoInnerKORE extends KILTransformation<K> {

    private Context context;
    private final boolean doDropQuote;

    private KLabel KLabel(String name) {
        return KORE.KLabel(dropQuote(name));
    }

    public KILtoInnerKORE(org.kframework.kil.loader.Context context, boolean doDropQuote) {
        this.context = context;
        this.doDropQuote = doDropQuote;
    }

    public static final String PRODUCTION_ID = "productionID";
    public static final String LIST_TERMINATOR = "listTerminator";

    public static final Labels labels = new Labels(KORE.constructor());

    public K apply(Bag body) {
        List<K> contents = body.getContents().stream().map(this).collect(Collectors.toList());
        return KApply(labels.KBag(), (KList(contents)));
    }

    // public K apply(TermComment c) {
    // return KList();
    // }

    private K cellMarker = org.kframework.definition.Configuration.cellMarker();

    @SuppressWarnings("unchecked")
    public KApply apply(Cell body) {
        // K x = ;
        // if (x instanceof KApply && ((KApply) x).klabel() == Labels.KBag()
        // && ((KApply) x).size() == 0) {

        return KApply(KLabel(body.getLabel()), KList(apply(body.getContents())),
                Attributes(cellMarker).addAll(convertCellAttributes(body)));
        // } else {
        // return KApply(KLabel(body.getLabel()), KList(x),
        // Att(cellMarker));
        // }
    }

    public K apply(org.kframework.kil.KLabelConstant c) {
        return InjectedKLabel(KLabel(c.getLabel()), Attributes());
    }

    public org.kframework.kore.KSequence apply(KSequence seq) {
        return KSequence(apply(seq.getContents()));
    }

    private List<K> apply(List<Term> contents) {
        return contents.stream().map(this).collect(Collectors.toList());
    }

    public org.kframework.kore.KApply apply(Bracket b) {
        Object content = apply(b.getContent());
        if (content instanceof KList) {
            content = KApply(KLabel(KORE.injectedKListLabel()), (KList) content);
        }
        return KApply(KLabel("bracket"), KList((K) content));
    }

    public KApply apply(TermCons cons) {
        org.kframework.attributes.Att att = attributesFor(cons);
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

    public String dropQuote(String s) {
        if (doDropQuote && s.startsWith("'"))
            return s.substring(1);
        else
            return s;
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
            return KLabel(dropQuote(((KLabelConstant) label).getLabel()));
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

    private org.kframework.attributes.Att attributesFor(TermCons cons) {
        String uniqueishID = "" + System.identityHashCode(cons.getProduction());
        org.kframework.attributes.Att att = sortAttributes(cons).add(PRODUCTION_ID, uniqueishID);
        return att;
    }

    private org.kframework.attributes.Att sortAttributes(Term cons) {

        return convertAttributes(cons).addAll(
                Attributes(KApply(KLabel("sort"),
                        KList(KToken(Sorts.KString(), cons.getSort().toString())))));
    }

    public KApply apply(Hole hole) {
        return KApply(labels.Hole(), KList(KToken(Sort(hole.getSort().getName()), "")),
                sortAttributes(hole));
    }

    public KVariable apply(Variable v) {
        return KVariable(v.getName(), sortAttributes(v));
    }

    public KRewrite apply(Rewrite r) {
        Object right = apply(r.getRight());
        if (right instanceof KList)
            right = KApply(KLabel(KORE.injectedKListLabel()), (KList) right);

        Object left = apply(r.getLeft());
        if (left instanceof KList)
            left = KApply(KLabel(KORE.injectedKListLabel()), (KList) left);

        return KRewrite((K) left, (K) right, sortAttributes(r));
    }

    public K applyOrTrue(Term t) {
        if (t != null)
            return apply(t);
        else
            return KToken(Sorts.Bool(), "true");
    }

    public K apply(TermComment t) {
        return KSequence();
    }

    public org.kframework.attributes.Att convertAttributes(ASTNode t) {
        Attributes attributes = t.getAttributes();

        Set<K> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String keyString = key.toString();
                    String valueString = attributes.get(key).getValue().toString();
                    if (keyString.equals("klabel")) {
                        return (K) KApply(KLabel("#klabel"),
                                KList(KToken(Sort("AttributeValue"), dropQuote(valueString))));
                    } else {
                        return (K) KApply(KLabel(keyString),
                                KList(KToken(Sort("AttributeValue"), valueString)));
                    }

                }).collect(Collectors.toSet());

        return Attributes(immutable(attributesSet))
                .addAll(attributesFromLocation(t.getLocation()))
                .addAll(attributesFromSource(t.getSource()));
    }

    private Att attributesFromSource(Source source) {
        Up up = new Up(KORE.self(), Set("org.kframework.attributes"));
        if (source != null) {
            return Att.apply(Set(up.apply(source)));
        }
        return Attributes();
    }

    public org.kframework.attributes.Att convertCellAttributes(Cell c) {
        Map<String, String> attributes = c.getCellAttributes();

        Set<K> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String value = attributes.get(key);
                    return (K)KApply(KLabel(key), KList(KToken(Sort("AttributeValue"), value)));
                }).collect(Collectors.toSet());

        return Attributes(immutable(attributesSet));
    }

    private org.kframework.attributes.Att attributesFromLocation(Location location) {
        Up up = new Up(KORE.self(), Set("org.kframework.attributes"));

        if (location != null) {
            return org.kframework.attributes.Att.apply(Set(up.apply(location)));
        } else
            return Attributes();
    }
}
