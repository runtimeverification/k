// Copyright (c) 2016-2019 K Team. All Rights Reserved.
package org.kframework.compile.checks;

import com.google.common.collect.ImmutableSet;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.Source;
import org.kframework.definition.Context;
import org.kframework.definition.ContextAlias;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.Sort;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.VisitK;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import java.io.File;
import java.io.IOException;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import scala.Tuple2;

import static org.kframework.kore.KORE.*;
import static org.kframework.Collections.*;

/**
 * Checks to ensure that KLabels in the definition obey rules relating to their use. First, klabels used in rules must
 * be defined by a production in one of the modules imported by the module the rule is in. Second, any given klabel
 * can only be defined in one module. This ensures that klabels don't mix across modules without strictly enforcing
 * the requirement that all klabels be unique, or that all klabels be qualified by their module name.
 */
public class CheckKLabels {
    private final Set<KEMException> errors;
    private final boolean kore;
    private final KExceptionManager kem;
    private final FileUtil files;

    public CheckKLabels(Set<KEMException> errors, KExceptionManager kem, boolean kore, FileUtil files) {
        this.errors = errors;
        this.kore = kore;
        this.kem = kem;
        this.files = files;
    }

    private final Map<String, Module> klabels = new HashMap<>();
    private final Map<String, Production> klabelProds = new HashMap<>();
    private final Set<String> usedLabels = new HashSet<>();

    public void check(Sentence sentence, Module m) {
        VisitK checkKLabels = new VisitK() {
            @Override
            public void apply(InjectedKLabel k) {
                apply(k.klabel(), k);
                super.apply(k);
            }

            @Override
            public void apply(KApply k) {
                apply(k.klabel(), k);
                super.apply(k);
            }

            private void apply(KLabel klabel, K k) {
                if (klabel instanceof KVariable)
                    return;
                Optional<Source> s = k.att().getOptional(Source.class);
                if (s.isPresent()) {
                    usedLabels.add(klabel.name());
                    if (m.definedKLabels().apply(klabel)) {
                        for (Production prod : iterable(m.productionsFor().apply(klabel.head()))) {
                          if (prod.source().isPresent() && prod.location().isPresent()) {
                              usedLabels.addAll(stream(m.productionsForLoc().apply(Tuple2.apply(prod.source().get(), prod.location().get())))
                                  .filter(p -> p.klabel().isDefined()).map(p -> p.klabel().get().name()).collect(Collectors.toSet()));
                          }
                        }
                    }
                }
                if (!m.definedKLabels().apply(klabel) && !isInternalKLabel(klabel.name(), m)) {
                    errors.add(KEMException.compilerError("Found klabel " + klabel.name() + " not defined in any production.", k));
                }
            }
        };
        if (sentence instanceof Rule) {
            Rule rl = (Rule) sentence;
            checkKLabels.apply(rl.body());
            checkKLabels.apply(rl.requires());
            checkKLabels.apply(rl.ensures());
        } else if (sentence instanceof Context) {
            Context ctx = (Context) sentence;
            checkKLabels.apply(ctx.body());
            checkKLabels.apply(ctx.requires());
        } else if (sentence instanceof ContextAlias) {
            ContextAlias ctx = (ContextAlias) sentence;
            checkKLabels.apply(ctx.body());
            checkKLabels.apply(ctx.requires());
        } else if (sentence instanceof Production) {
            Production prod = (Production) sentence;
            if (prod.klabel().isDefined()) {
                KLabel klabel = prod.klabel().get();
                if (klabels.containsKey(klabel.name()) && !m.equals(klabels.get(klabel.name())) && !kore) {
                    errors.add(KEMException.compilerError("KLabel " + klabel.name() + " defined in multiple modules: " + klabels.get(klabel.name()).name() + " and " + m.name() + ".", prod));
                }
                if (klabelProds.containsKey(klabel.name()) && kore && !internalDuplicates.contains(klabel.name())) {
                    errors.add(KEMException.compilerError("Symbol " + klabel.name() + " is not unique. Previously defined as: " + klabelProds.get(klabel.name()), prod));
                }
                klabels.put(klabel.name(), m);
                klabelProds.put(klabel.name(), prod);
            }
        }
    }

    private boolean hasAttWithNoArg(Att att, String attName) {
      return att.contains(attName) && att.get(attName).equals("");
    }

    public void check(Module mainMod) {
        Set<String> definedButNotUsed = new HashSet<>(klabelProds.keySet());
        definedButNotUsed.removeAll(usedLabels);
        File includeDir = files.resolveKInclude(".");
        String canonicalPath;
        try {
            canonicalPath = includeDir.getCanonicalPath();
            if (!canonicalPath.endsWith(File.separator)) {
              canonicalPath = canonicalPath + File.separator;
            }
        } catch (IOException e) {
            canonicalPath = null;
        }
        for (String symbol : definedButNotUsed) {
            Production prod = klabelProds.get(symbol);
            Optional<Source> s = prod.source();
            if (prod.att().contains(Att.MAINCELL()) ||
                prod.att().contains("unused") ||
                symbol.equals("<generatedTop>") ||
                !s.isPresent() ||
                (prod.att().contains(Att.CELL()) && stream(prod.nonterminals()).filter(nt -> klabels.get(symbol).sortAttributesFor().get(nt.sort().head()).getOrElse(() -> Att.empty()).contains("cellCollection")).findAny().isPresent())) {
                continue;
            }
            if (canonicalPath == null || !s.get().source().contains(canonicalPath)) {
                kem.registerCompilerWarning(ExceptionType.UNUSED_SYMBOL, errors, "Symbol '" + symbol + "' defined but not used. Add the 'unused' attribute if this is intentional.", klabelProds.get(symbol));
            }
        }
        for (KLabel function : iterable(mainMod.functions())) {
            boolean allConcrete = true;
            boolean allSymbolic = true;
            for (Rule rule : iterable(mainMod.rulesFor().get(function).getOrElse(() -> Collections.<Rule>Set()))) {
                if ((hasAttWithNoArg(rule.att(), Att.CONCRETE()) &&
                    rule.att().contains(Att.SYMBOLIC())) ||
                    (hasAttWithNoArg(rule.att(), Att.SYMBOLIC()) &&
                    rule.att().contains(Att.CONCRETE()))) {
                    errors.add(KEMException.compilerError("Rule cannot be both concrete and symbolic in the same variable.", rule));
                }
                if (!hasAttWithNoArg(rule.att(), Att.CONCRETE()) && !rule.att().contains(Att.SIMPLIFICATION())) {
                    allConcrete = false;
                }
                if (!hasAttWithNoArg(rule.att(), Att.SYMBOLIC()) && !rule.att().contains(Att.SIMPLIFICATION())) {
                    allSymbolic = false;
                }
            }
            for (Rule rule : iterable(mainMod.rulesFor().get(function).getOrElse(() -> Collections.<Rule>Set()))) {
                if (rule.att().contains(Att.CONCRETE()) && !allConcrete && !rule.att().contains(Att.SIMPLIFICATION())) {
                    errors.add(KEMException.compilerError("Found concrete attribute without simplification attribute on function with one or more non-concrete rules.", rule));
                }
                if (rule.att().contains(Att.SYMBOLIC()) && !allSymbolic && !rule.att().contains(Att.SIMPLIFICATION())) {
                    errors.add(KEMException.compilerError("Found symbolic attribute without simplification attribute on function with one or more non-symbolic rules.", rule));
                }
            }
        }
    }

    private static final ImmutableSet<String> internalDuplicates = ImmutableSet.of("#EmptyKList", "#EmptyK", "#ruleRequires", "#ruleRequiresEnsures", "#Top", "#Bottom");

    private static final ImmutableSet<String> internalNames = ImmutableSet.of("#cells", "#dots", "#noDots", "#Or", "#fun2", "#fun3", "#let", "#withConfig", "<generatedTop>", "#SemanticCastToBag", "_:=K_", "_:/=K_");

    public static boolean isInternalKLabel(String name, Module m) {
        return m.semanticCasts().apply(name) || internalNames.contains(name)|| m.recordProjections().apply(name) || m.sortPredicates().apply(name) || m.sortProjections().apply(name);
    }
}
