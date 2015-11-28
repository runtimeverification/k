// Copyright (c) 2015 K Team. All Rights Reserved.
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
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.compile.KtoKORE;
import org.kframework.krun.KRunOptions;
import org.kframework.krun.ioserver.filesystem.portable.PortableFileSystem;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static scala.compat.java8.JFunction.func;
import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Uses the Java backend to expand all the macros in a particular module. A macro is a rule (without a side condition)
 * which is tagged with the "macro" attribute. This class creates a Java Backend rewriter and uses it to reach
 * a fixed point on such rules.
 *
 * Note that this class is somewhat expensive to construct, and so copies of it should be kept around as long
 * as possible and reused where they can be.
 */
public class ExpandMacros {

    private final InitializeRewriter.SymbolicRewriterGlue rewriter;
    private final KExceptionManager kem;
    private final boolean noMacros;

    public ExpandMacros(Module mod, KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        Optional<Module> macroModule = getMacroModule(mod);
        if (macroModule.isPresent()) {
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
                    new InitializeRewriter.InitializeDefinition()).apply(macroModule.get());
            noMacros = false;
        } else {
            noMacros = true;
            rewriter = null;
        }
    }

    private static boolean isSortPredicates(K term, Module mod) {
        if (term.equals(BooleanUtils.TRUE)) {
            return true;
        }
        if (term instanceof KApply) {
            KApply app = (KApply)term;
            KLabel l = app.klabel();
            if (l.equals(KLabel("_andBool_"))) {
                return app.klist().stream().allMatch(t -> isSortPredicates(t,mod));
            } else {
                return isSortPredicate(l, mod);
            }
        } else {
            return false;
        }
    }

    private static boolean isSortPredicate(KLabel label, Module mod) {
        return mod.attributesFor().get(label).exists(func(atts ->
                atts.get(Attribute.PREDICATE_KEY).exists(func(s -> !s.equals("")))));
    }

    private static Optional<Module> getMacroModule(Module mod) {
        Set<Sentence> sentences = new HashSet<>();
        sentences.addAll(mutable(mod.productions()));
        sentences.addAll(mutable(mod.sortDeclarations()));
        Set<Rule> macroRules = stream(mod.rules())
                .filter(r -> r.att().contains(Attribute.MACRO_KEY))
                .map(r -> {
                    if (!r.ensures().equals(BooleanUtils.TRUE) || !isSortPredicates(r.requires(),mod)) {
                        throw KEMException.compilerError("Side conditions are not allowed in macro rules. If you are typing a variable, use ::.", r);
                    }
                    if (!r.requires().equals(BooleanUtils.TRUE)) {
                        return Rule(r.body(), BooleanUtils.TRUE, r.ensures(), r.att());
                    } else {
                        return r;
                    }
                })
                .collect(Collectors.toSet());
        sentences.addAll(macroRules);
        if (macroRules.isEmpty()) {
            return Optional.empty();
        }
        return Optional.of(Module(mod.name(), Set(), immutable(sentences), mod.att()));
    }

    private Rule expand(Rule rule) {
        return Rule(expand(rule.body()),
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
        if (noMacros) {
            return term;
        }
        TermContext tc = TermContext.builder(rewriter.rewritingContext).build();
        //Term t = new KOREtoBackendKIL(tc).convert(term).evaluate(tc);
        Term t = new MacroExpander(tc, kem).processTerm(new KOREtoBackendKIL(rewriter.module, rewriter.definition, tc.global(), false, false).convert(term));
        return new KtoKORE().apply(t);
    }

    public Sentence expand(Sentence s) {
        if (s instanceof Rule && !s.att().contains("macro")) {
            return expand((Rule) s);
        } else if (s instanceof Context) {
            return expand((Context) s);
        } else {
            return s;
        }
    }

}
