// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import org.kframework.backend.java.kore.compile.ExpandMacros;
import org.kframework.backend.java.kore.compile.ExpandMacrosDefinitionTransformer;
import org.kframework.compile.CleanKSeq;
import org.kframework.definition.Constructors;
import org.kframework.definition.Definition;
import org.kframework.definition.DefinitionTransformer;
import org.kframework.definition.ModuleTransformer;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.ADT;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KORE;
import org.kframework.kore.KSequence;
import org.kframework.kore.KVariable;
import org.kframework.kore.SortedADT;
import org.kframework.kore.compile.Backend;
import org.kframework.kore.compile.ConvertDataStructureToLookup;
import org.kframework.kore.compile.MergeRules;
import org.kframework.kore.compile.RewriteToTop;
import org.kframework.kore.compile.TransformKORE;
import org.kframework.kore.compile.VisitKORE;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;

import static scala.compat.java8.JFunction.*;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

import static org.kframework.definition.Constructors.Att;

public class JavaBackend implements Backend {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final GlobalOptions globalOptions;
    private final KompileOptions kompileOptions;

    @Override
    public void accept(CompiledDefinition def) {
    }

    @Inject
    public JavaBackend(KExceptionManager kem, FileUtil files, GlobalOptions globalOptions, KompileOptions kompileOptions) {
        this.kem = kem;
        this.files = files;
        this.globalOptions = globalOptions;
        this.kompileOptions = kompileOptions;
    }

    @Override
    public Function<Definition, Definition> steps(Kompile kompile) {
        DefinitionTransformer convertDataStructureToLookup = DefinitionTransformer.fromSentenceTransformer(func((m, s) -> new ConvertDataStructureToLookup(m, false).convert(s)), "convert data structures to lookups");
        ExpandMacrosDefinitionTransformer expandMacrosDefinitionTransformer = new ExpandMacrosDefinitionTransformer(kem, files, globalOptions, kompileOptions);

        if (kompile.kompileOptions.experimental.koreProve) {
            return kompile.defaultSteps()
                    .andThen(expandMacrosDefinitionTransformer::apply)
                    .andThen(convertDataStructureToLookup::apply);
        }

        return d -> (func((Definition dd) -> kompile.defaultSteps().apply(dd)))
                .andThen(DefinitionTransformer.fromRuleBodyTranformer(RewriteToTop::bubbleRewriteToTopInsideCells, "bubble out rewrites below cells"))
                        //.andThen(DefinitionTransformer.fromRuleBodyTranformer(RewriteToTop::bubbleRewriteOutOfKSeq, "bubble rewrites out of kseq"))
                .andThen(func(dd -> expandMacrosDefinitionTransformer.apply(dd)))
                .andThen(convertDataStructureToLookup)
                .andThen(DefinitionTransformer.fromRuleBodyTranformer(JavaBackend::ADTKVariableToSortedVariable, "ADT.KVariable to SortedVariable"))
                .andThen(DefinitionTransformer.fromRuleBodyTranformer(JavaBackend::convertKSeqToKApply, "kseq to kapply"))
                .andThen(DefinitionTransformer.fromRuleBodyTranformer(CleanKSeq.self(), "normalize kseq"))
                .andThen(DefinitionTransformer.fromSentenceTransformer(JavaBackend::markSingleVariables, "mark single variables"))
                .andThen(new DefinitionTransformer(new MergeRules(KORE.c())))
                .apply(d);
    }

    private static K ADTKVariableToSortedVariable(K ruleBody) {
        return new TransformKORE() {
            public K apply(KVariable kvar) {
                return new SortedADT.SortedKVariable(kvar.name(), kvar.att());
            }
        }.apply(ruleBody);
    }

    private static K convertKSeqToKApply(K ruleBody) {
        return new TransformKORE() {
            public K apply(KSequence kseq) {
                return ((ADT.KSequence) kseq).kApply();
            }
        }.apply(ruleBody);
    }

    private static Sentence markSingleVariables(Sentence s) {
        if (s instanceof Rule) {
            Rule r = (Rule) s;

            if (!(r.body() instanceof KApply) || !((KApply) r.body()).klabel().name().equals("<T>"))
                return r;

            Map<KVariable, Integer> varCount = new HashMap<>();
            VisitKORE markerVisitor = new VisitKORE() {
                public Void apply(KVariable kvar) {
                    varCount.put(kvar, varCount.getOrDefault(kvar, 0) + 1);
                    return null;
                }
            };
            markerVisitor.apply(r.body());
            markerVisitor.apply(r.requires());
            markerVisitor.apply(r.ensures());

            TransformKORE markerAdder = new TransformKORE() {
                public K apply(KVariable kvar) {
                    if (kvar instanceof SortedADT.SortedKVariable && ((SortedADT.SortedKVariable) kvar).sort().equals(KORE.Sort("K")) && varCount.get(kvar) == 1) {
                        return new SortedADT.SortedKVariable("THE_VARIABLE", Att());
                    } else {
                        return kvar;
                    }
                }
            };

            return Constructors.Rule(markerAdder.apply(r.body()), markerAdder.apply(r.requires()), markerAdder.apply(r.ensures()), r.att());
        } else {
            return s;
        }
    }
}
