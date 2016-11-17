// Copyright (c) 2014-2016 K Team. All Rights Reserved.

package org.kframework.kore.convertors;

import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.builtin.Labels;
import org.kframework.builtin.Sorts;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.kore.KORE;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import scala.Tuple2;

import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;

@SuppressWarnings("unused")
public class KILtoInnerKORE extends KILTransformation<K> {

    private Context context;

    private KLabel KLabel(String name) {
        return KORE.KLabel(dropQuote(name));
    }

    public KILtoInnerKORE(org.kframework.kil.loader.Context context) {
        this.context = context;
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

    @SuppressWarnings("unchecked")
    public KApply apply(Cell body) {
        // K x = ;
        // if (x instanceof KApply && ((KApply) x).klabel() == Labels.KBag()
        // && ((KApply) x).size() == 0) {

        return KApply(KLabel(body.getLabel()), KList(apply(body.getContents())),
                Att().add("cell").addAll(convertCellAttributes(body)));
        // } else {
        // return KApply(KLabel(body.getLabel()), KList(x),
        // Att(cellMarker));
        // }
    }

    public K apply(org.kframework.kil.KLabelConstant c) {
        return InjectedKLabel(KLabel(c.getLabel()), Att());
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

        return KApply(KLabel(terminatorKLabel), KList(), Att().add(LIST_TERMINATOR));
    }

    public String dropQuote(String s) {
        return s;
    }

    public K apply(KApp kApp) {
        Term label = kApp.getLabel();

        if (label instanceof Token) {
            return KToken(((Token) label).value(), Sort(((Token) label).tokenSort().getName()));
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

        return convertAttributes(cons).add("sort", cons.getSort().toString());
    }

    public KApply apply(Hole hole) {
        return KApply(labels.Hole(), KList(KToken("", Sort(hole.getSort().getName()))),
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
            return KToken("true", Sorts.Bool());
    }

    public K apply(TermComment t) {
        return KSequence();
    }

    public org.kframework.attributes.Att convertAttributes(ASTNode t) {
        Attributes attributes = t.getAttributes();

        Map<String, String> attributesSet = attributes
                .keySet()
                .stream()
                .map(key -> {
                    String keyString = key.toString();
                    String valueString = attributes.get(key).getValue().toString();
                    if (keyString.equals("klabel")) {
                        return Tuple2.apply("klabel", dropQuote(valueString));
                    } else {
                        return Tuple2.apply(keyString, valueString);
                    }

                }).collect(Collectors.toMap(Tuple2::_1, Tuple2::_2));

        return Att().addAll(attributesSet)
                .addAll(attributesFromLocation(t.getLocation()))
                .addAll(attributesFromSource(t.getSource()));
    }

    private Att attributesFromSource(Source source) {
        if (source != null) {
            return Att().add(Source.class, source);
        }
        return Att();
    }

    public org.kframework.attributes.Att convertCellAttributes(Cell c) {
        Map<String, String> attributes = c.getCellAttributes();

        Map<String, String> attributesSet = attributes
                .keySet()
                .stream()
                .collect(Collectors.toMap(Function.identity(), attributes::get));

        return Att().addAll(attributesSet);
    }

    private org.kframework.attributes.Att attributesFromLocation(Location location) {
        if (location != null) {
            return Att().add(Location.class, location);
        } else
            return Att();
    }
}
