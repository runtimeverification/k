// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.compile;

import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.attributes.Source;
import org.kframework.backend.java.kil.InjectedKLabel;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Rule;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.backend.java.symbolic.ConjunctiveFormula;
import org.kframework.definition.Module;
import org.kframework.kil.Attribute;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.compile.RewriteToTop;
import org.kframework.kore.convertors.KOREtoKIL;

import java.util.Collections;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * KORE to backend KIL
 */
public class KOREtoBackendKIL extends org.kframework.kore.AbstractConstructors<org.kframework.kore.K> {

    private final TermContext context;

    public KOREtoBackendKIL(TermContext context) {
        this.context = context;
    }

    @Override
    public KLabelConstant KLabel(String name) {
        return KLabelConstant.of(name, context.definition());
    }

    @Override
    public Sort Sort(String name) {
        return Sort.of(name);
    }

    @Override
    public <KK extends org.kframework.kore.K> KList KList(List<KK> items) {
        return (KList) KCollection.upKind(
                KList.concatenate(items.stream().map(this::convert).collect(Collectors.toList())),
                Kind.KLIST);
    }

    @Override
    public Token KToken(String s, org.kframework.kore.Sort sort, Att att) {
        return !sort.name().equals("KBoolean") ? Token.of(Sort(sort.name()), s) : Token.of(Sort("Bool"), s);
    }

    @Override
    public KApply KApply(KLabel klabel, org.kframework.kore.KList klist, Att att) {
        throw new AssertionError("Unsupported for now because KVariable is not a KLabel. See KApply1()");
    }

    public Term KApply1(org.kframework.kore.KLabel klabel, org.kframework.kore.KList klist, Att att) {
        return KItem.of(convert(klabel), KList(klist.items()), context);
    }

    @Override
    public <KK extends org.kframework.kore.K> KSequence KSequence(List<KK> items, Att att) {
        KSequence.Builder builder = KSequence.builder();
        items.stream().map(this::convert).forEach(builder::concatenate);
        Term kSequence = KCollection.upKind(builder.build(), Kind.K);
        return kSequence instanceof Variable ? KSequence.frame((Variable) kSequence) : (KSequence) kSequence;
    }

    @Override
    public Variable KVariable(String name, Att att) {
        Variable var = new Variable(name, Sort.of(att.<String>getOptional(Attribute.SORT_KEY).orElse("K")));
        var.setAttributes(new KOREtoKIL().convertAttributes(att));
        return var;
    }

    @Override
    public org.kframework.kore.KRewrite KRewrite(org.kframework.kore.K left, org.kframework.kore.K right, Att att) {
        throw new AssertionError("Should not encounter a KRewrite");
    }

    @Override
    public InjectedKLabel InjectedKLabel(org.kframework.kore.KLabel klabel, Att att) {
        return new InjectedKLabel(convert(klabel));
    }

    private Term convert(KLabel klabel) {
        if (klabel instanceof KVariable) {
            return KVariable(klabel.name(), ((KVariable) klabel).att().add(Attribute.SORT_KEY, "KLabel"));

        } else {
            return KLabel(klabel.name());
        }
    }

    public Term convert(org.kframework.kore.K k) {
        if (k instanceof Term)
            return (Term) k;
        else if (k instanceof org.kframework.kore.KToken)
            return KToken(((org.kframework.kore.KToken) k).s(), ((org.kframework.kore.KToken) k).sort(), k.att());
        else if (k instanceof org.kframework.kore.KApply)
            return KApply1(((KApply) k).klabel(), ((KApply) k).klist(), k.att());
        else if (k instanceof org.kframework.kore.KSequence)
            return KSequence(((org.kframework.kore.KSequence) k).items(), k.att());
        else if (k instanceof org.kframework.kore.KVariable)
            return KVariable(((org.kframework.kore.KVariable) k).name(), k.att());
        else if (k instanceof org.kframework.kore.InjectedKLabel)
            return InjectedKLabel(((org.kframework.kore.InjectedKLabel) k).klabel(), k.att());
        else
            throw new AssertionError("BUM!");
    }

    public Rule convert(Optional<Module> module, org.kframework.definition.Rule rule) {
        K leftHandSide = RewriteToTop.toLeft(rule.body());
        org.kframework.kil.Rule oldRule = new org.kframework.kil.Rule();
        oldRule.setAttributes(new KOREtoKIL().convertAttributes(rule.att()));
        Location loc = rule.att().getOptional(Location.class).orElse(null);
        Source source = rule.att().getOptional(Source.class).orElse(null);
        oldRule.setLocation(loc);
        oldRule.setSource(source);

        if (module.isPresent()) {
            if (leftHandSide instanceof KApply && module.get().attributesFor().apply(((KApply) leftHandSide).klabel()).contains(Attribute.FUNCTION_KEY)) {
                oldRule.putAttribute(Attribute.FUNCTION_KEY, "");
            }
        }


        return new Rule(
                "",
                convert(leftHandSide),
                convert(RewriteToTop.toRight(rule.body())),
                Collections.singletonList(convert(rule.requires())),
                Collections.singletonList(convert(rule.ensures())),
                Collections.emptySet(),
                Collections.emptySet(),
                ConjunctiveFormula.of(context),
                false,
                null,
                null,
                null,
                null,
                oldRule,
                context);

    }
}
