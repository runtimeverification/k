package org.kframework.backend.java.kore.compile;

import org.kframework.backend.java.compile.KOREtoBackendKIL;
import org.kframework.backend.java.kil.Term;
import org.kframework.backend.java.kil.TermContext;
import org.kframework.backend.java.symbolic.InitializeRewriter;
import org.kframework.backend.java.symbolic.JavaExecutionOptions;
import org.kframework.backend.java.symbolic.MacroExpander;
import org.kframework.builtin.BooleanUtils;
import org.kframework.definition.Context;
import org.kframework.definition.Module;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kil.Attribute;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.compile.RewriteToTop;
import org.kframework.kore.compile.TransformKORE;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Created by dwightguth on 5/26/15.
 */
public class ExpandMacros {

    private final InitializeRewriter.SymbolicRewriterGlue rewriter;
    private final KExceptionManager kem;

    public ExpandMacros(Module mod, KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        rewriter = (InitializeRewriter.SymbolicRewriterGlue) new InitializeRewriter(
                new PortableFileSystem(kem, files),
                new JavaExecutionOptions(),
                globalOptions,
                kem,
                kompileOptions.experimental.smt,
                new HashMap<>(),
                kompileOptions,
                new KRunOptions(),
                files,
                new InitializeRewriter.InitializeDefinition()).apply(getMacroModule(mod));
    }

    private static Module getMacroModule(Module mod) {
        Set<Sentence> sentences = new HashSet<>();
        sentences.addAll(mutable(mod.productions()));
        sentences.addAll(mutable(mod.sortDeclarations()));
        Set<Rule> macroRules = stream(mod.rules())
                .filter(r -> r.att().contains(Attribute.MACRO_KEY))
                .collect(Collectors.toSet());
        for (Rule r : macroRules) {
            if (!r.requires().equals(BooleanUtils.TRUE) || !r.ensures().equals(BooleanUtils.TRUE)) {
                throw KEMException.compilerError("Side conditions are not allowed in macro rules. If you are typing a variable, use ::.", r);
            }
        }
        sentences.addAll(macroRules);
        return Module(mod.name(), Set(), immutable(sentences), mod.att());
    }

    private Rule expand(Rule rule) {
        return Rule(
                KRewrite(expand(RewriteToTop.toLeft(rule.body())), expand(RewriteToTop.toRight(rule.body()))),
                expand(rule.requires()),
                expand(rule.ensures()),
                rule.att());
    }

    private Context expand(Context context) {
        return Context(
                expand(context.body()),
                expand(context.requires()),
                context.att());
    }

    public K expand(K term) {
        TermContext tc = TermContext.of(rewriter.rewritingContext);
        //Term t = new KOREtoBackendKIL(tc).convert(term).evaluate(tc);
        Term t = new MacroExpander(tc, kem).processTerm(new KOREtoBackendKIL(tc).convert(term));
        return new TransformKORE() {
            @Override
            public K apply(KApply k) {
                k = (KApply)super.apply(k);
                return KApply(apply(k.klabel()), k.klist(), k.att());
            }

            private KLabel apply(KLabel klabel) {
                if (klabel instanceof KVariable)
                    return apply((KVariable)klabel);
                return KLabel(klabel.name());
            }

            @Override
            public K apply(KRewrite k) {
                k = (KRewrite) super.apply(k);
                return KRewrite(k.left(), k.right(), k.att());
            }

            @Override
            public K apply(KToken k) {
                return KToken(k.s(), Sort(k.sort().name()), k.att());
            }

            @Override
            public KVariable apply(KVariable k) {
                return KVariable(k.name(), k.att());
            }

            @Override
            public K apply(KSequence k) {
                k = (KSequence) super.apply(k);
                return KSequence(k.items(), k.att());
            }

            @Override
            public K apply(InjectedKLabel k) {
                return InjectedKLabel(apply(k.klabel()), k.att());
            }
        }.apply(t);
    }

    public synchronized Sentence expand(Sentence s) {
        if (s instanceof Rule) {
            return expand((Rule) s);
        } else if (s instanceof Context) {
            return expand((Context) s);
        } else {
            return s;
        }
    }
}
