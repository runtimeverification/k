// Copyright (c) 2019 K Team. All Rights Reserved.
package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.utils.errorsystem.KEMException;

import java.util.HashSet;
import java.util.Set;

public class MarkPreserveDefinedness {

    private final Module mainModule;

    public MarkPreserveDefinedness(Definition d) {
        mainModule = d.mainModule();
    }


    public Sentence resolve(Module m, Sentence s) {
        // temporary code to test out the efficacy of selective application of @Ceil checks
        // https://github.com/runtimeverification/k/issues/2943#issuecomment-1265519499
        if (!(s instanceof Rule)) return s;
        Rule r = (Rule) s;
        if (r.att().contains(Att.SIMPLIFICATION()) || r.att().contains(Att.ANYWHERE())) return r;
        KLabel kl = m.matchKLabel(r);
        Att atts = m.attributesFor().get(kl).getOrElse(Att::empty);
        if (atts.contains(Att.FUNCTION()) || atts.contains(Att.FUNCTIONAL()) || atts.contains("mlOp"))
            return r;

        Set<KEMException> errors = new HashSet<>();
        new RewriteAwareVisitor(true, errors) {
            @Override
            public void apply(KApply k) {
                if (!errors.isEmpty())
                    return;
                Att attributes;
                // special case for when rules are defined in the syntax module, but they don't yet have knowledge of the configuration
                if (m.attributesFor().contains(k.klabel()))
                    attributes = m.attributesFor().apply(k.klabel());
                else
                    attributes = mainModule.attributesFor().apply(k.klabel());
                if (isRHS()) {
                    if (attributes.contains(Att.FUNCTION()) && !attributes.contains(Att.FUNCTIONAL())) // only total functions
                        errors.add(KEMException.compilerError("Not an actual error. Used as a marker for markPreservesDefinedness.", r));
                    else if (attributes.contains(Att.ASSOC()) || attributes.contains(Att.IDEM())) // only constructors
                        errors.add(KEMException.compilerError("Not an actual error. Used as a marker for markPreservesDefinedness.", r));
                }
                super.apply(k);
            }

            @Override
            public void apply(KVariable k) {
                if (k.name().startsWith("@")) // no set variables
                    errors.add(KEMException.compilerError("Not an actual error. Used as a marker for markPreservesDefinedness.", r));
            }
        }.apply(r.body());

        if (errors.isEmpty()) {
            //System.out.println("preserves-definedness: " + r.source().orElse(Source.apply("gen")).source() + ":" + r.location().orElse(Location.apply(0,0,0,0)).startLine());
            return Rule.apply(r.body(), r.requires(), r.ensures(), r.att().add("preserves-definedness"));
        }
        return s;    }

    public static Sentence markPreservesDefinedness(Module m, Sentence s) {
        // temporary code to test out the efficacy of selective application of @Ceil checks
        // https://github.com/runtimeverification/k/issues/2943#issuecomment-1265519499
        if (!(s instanceof Rule)) return s;
        Rule r = (Rule) s;
        if (s.att().contains(Att.SIMPLIFICATION()) || s.att().contains(Att.ANYWHERE())) return s;
        KLabel kl = m.matchKLabel((Rule) s);
        Att atts = m.attributesFor().get(kl).getOrElse(Att::empty);
        if (atts.contains(Att.FUNCTION()) || atts.contains(Att.FUNCTIONAL()) || atts.contains("mlOp"))
            return s;

        Set<KEMException> errors = new HashSet<>();
        new RewriteAwareVisitor(true, errors) {
            @Override
            public void apply(KApply k) {
                if (!errors.isEmpty())
                    return;
                if (!k.klabel().name().equals("<generatedTop>")) { // special case for when rules are defined in the syntax module, but they don't yet have knowledge of the configuration
                    Att attributes = m.attributesFor().apply(k.klabel());
                    if (isRHS()) {
                        if (attributes.contains(Att.FUNCTION()) && !attributes.contains(Att.FUNCTIONAL())) // only total functions
                            errors.add(KEMException.compilerError("Not an actual error. Used as a marker for markPreservesDefinedness.", r));
                        else if (attributes.contains(Att.ASSOC()) || attributes.contains(Att.IDEM())) // only constructors
                            errors.add(KEMException.compilerError("Not an actual error. Used as a marker for markPreservesDefinedness.", r));
                    }
                }
                super.apply(k);
            }

            @Override
            public void apply(KVariable k) {
                if (k.name().startsWith("@")) // no set variables
                    errors.add(KEMException.compilerError("Not an actual error. Used as a marker for markPreservesDefinedness.", r));
            }
        }.apply(r.body());

        if (errors.isEmpty()) {
            //System.out.println("preserves-definedness: " + r.source().orElse(Source.apply("gen")).source() + ":" + r.location().orElse(Location.apply(0,0,0,0)).startLine());
            return Rule.apply(r.body(), r.requires(), r.ensures(), r.att().add("preserves-definedness"));
        }
        return s;
    }
}
