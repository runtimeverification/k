// Copyright (c) 2014-2015 K Team. All Rights Reserved.

package org.kframework.backend.java.compile;

import org.kframework.attributes.Att;
import org.kframework.backend.java.kil.InjectedKLabel;
import org.kframework.backend.java.kil.KCollection;
import org.kframework.backend.java.kil.KItem;
import org.kframework.backend.java.kil.KLabelConstant;
import org.kframework.backend.java.kil.KList;
import org.kframework.backend.java.kil.KSequence;
import org.kframework.backend.java.kil.Kind;
import org.kframework.backend.java.kil.Sort;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.kil.Token;
import org.kframework.backend.java.kil.Variable;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;

import java.util.List;
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
    public Token KToken(org.kframework.kore.Sort sort, String s, Att att) {
        return !sort.name().equals("KBoolean") ? Token.of(Sort(sort.name()), s) : Token.of(Sort("Bool"), s);
    }

    @Override
    public KApply KApply(KLabel klabel, org.kframework.kore.KList klist, Att att) {
        throw new AssertionError("Unsupported for now because KVariable is not a KLabel. See KApply1()");
    }

    public Term KApply1(org.kframework.kore.KLabel klabel, org.kframework.kore.KList klist, Att att) {
        return KItem.of(KLabel(klabel.name()), KList(klist.items()), context);
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
        return new Variable(name, Sort.of(att.<String>getOptional("sort").orElse("K")));
    }

    @Override
    public org.kframework.kore.KRewrite KRewrite(org.kframework.kore.K left, org.kframework.kore.K right, Att att) {
        throw new AssertionError("Should not encounter a KRewrite");
    }

    @Override
    public InjectedKLabel InjectedKLabel(org.kframework.kore.KLabel klabel, Att att) {
        return new InjectedKLabel(KLabel(klabel.name()));
    }


    public Term convert(org.kframework.kore.K k) {
        if (k instanceof Term)
            return (Term) k;
        else if (k instanceof org.kframework.kore.KToken)
            return KToken(((org.kframework.kore.KToken) k).sort(), ((org.kframework.kore.KToken) k).s(), k.att());
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
}
