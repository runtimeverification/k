// Copyright (c) 2015-2018 K Team. All Rights Reserved.
package org.kframework.backend.java.symbolic;

import com.google.inject.Inject;
import org.kframework.AddConfigurationRecoveryFlags;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.backend.Backends;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.*;
import org.kframework.definition.*;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.Kompile;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.ADT;
import org.kframework.kore.KSequence;
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.kore.SortedADT;
import org.kframework.backend.java.compile.ConvertDataStructureToLookup;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Option;

import static org.kframework.definition.Constructors.*;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Function;

public class JavaBackend implements Backend {

    private final KExceptionManager kem;
    private final FileUtil files;
    private final GlobalOptions globalOptions;
    private final KompileOptions kompileOptions;

    /**
     * In the Java backend, {@link KSequence}s are treated like {@link KApply}s, so tranform them.
     */
    public static K convertKSeqToKApply(K ruleBody) {
        return new TransformK() {
            public K apply(KSequence kseq) {
                return super.apply(((ADT.KSequence) kseq).kApply());
            }
        }.apply(ruleBody);
    }

    public static Sentence convertListItemToNonFunction(Module mod, Sentence sentence) {
        if (!(sentence instanceof Production)) {
            return sentence;
        }
        Production prod = (Production)sentence;
        if (prod.klabel().isDefined() && KLabels.ListItem.equals(prod.klabel().get())) {
            return Production(prod.sort(), prod.items(), prod.att().remove("function"));
        }
        return prod;
    }

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

    /**
     * @param the generic {@link Kompile}
     * @return the special steps for the Java backend
     */
    @Override
    public Function<Definition, Definition> steps() {
        DefinitionTransformer convertDataStructureToLookup = DefinitionTransformer.fromSentenceTransformer((m, s) -> new ConvertDataStructureToLookup(m, false).convert(s), "convert data structures to lookups");

        return d -> DefinitionTransformer.fromRuleBodyTransformer(RewriteToTop::bubbleRewriteToTopInsideCells, "bubble out rewrites below cells")
                .andThen(DefinitionTransformer.fromSentenceTransformer(JavaBackend::convertListItemToNonFunction, "remove function attribute from ListItem production"))
                .andThen(DefinitionTransformer.fromSentenceTransformer(new NormalizeAssoc(KORE.c()), "normalize assoc"))
                .andThen(DefinitionTransformer.from(AddBottomSortForListsWithIdenticalLabels.singleton(), "add bottom sorts for lists"))
                .andThen(DefinitionTransformer.fromSentenceTransformer((m, s) -> new ExpandMacros(m, kem, files, globalOptions, kompileOptions).expand(s), "expand macros"))
                .andThen(DefinitionTransformer.fromSentenceTransformer(new NormalizeAssoc(KORE.c()), "normalize assoc"))
                .andThen(convertDataStructureToLookup)
                .andThen(DefinitionTransformer.fromRuleBodyTransformer(JavaBackend::ADTKVariableToSortedVariable, "ADT.KVariable to SortedVariable"))
                .andThen(DefinitionTransformer.fromRuleBodyTransformer(JavaBackend::convertKSeqToKApply, "kseq to kapply"))
                .andThen(DefinitionTransformer.fromRuleBodyTransformer(NormalizeKSeq.self()::apply, "normalize kseq"))
                .andThen(JavaBackend::markRegularRules)
                .andThen(DefinitionTransformer.fromSentenceTransformer(new AddConfigurationRecoveryFlags(), "add refers_THIS_CONFIGURATION_marker"))
                .andThen(DefinitionTransformer.fromSentenceTransformer(JavaBackend::markSingleVariables, "mark single variables"))
                .andThen(DefinitionTransformer.from(new AssocCommToAssoc(), "convert AC matching to A matching"))
                .andThen(DefinitionTransformer.from(new MergeRules(), "merge rules into one rule with or clauses"))
                .apply(Kompile.defaultSteps(kompileOptions, kem, files, excludedModuleTags()).apply(d));
             // .andThen(KoreToMiniToKore::apply) // for serialization/deserialization test
    }

    @Override
    public Function<Module, Module> specificationSteps(Definition def) {
        BiFunction<Module, K, K> convertCellCollections = (Module m, K k) -> new ConvertDataStructureToLookup(m, false).convert(k);
        return m -> ModuleTransformer.fromSentenceTransformer(new ResolveAnonVar()::resolve, "resolve anonymous varaibles")
                .andThen(ModuleTransformer.fromSentenceTransformer(s -> new ResolveSemanticCasts(kompileOptions.backend.equals(Backends.JAVA)).resolve(s), "resolve semantic casts"))
                .andThen(AddImplicitComputationCell::transformModule)
                .andThen(ConcretizeCells::transformModule)
                .andThen(ModuleTransformer.fromRuleBodyTransformer(RewriteToTop::bubbleRewriteToTopInsideCells, "bubble out rewrites below cells"))
                .andThen(AddBottomSortForListsWithIdenticalLabels.singleton())
                .andThen(ModuleTransformer.fromSentenceTransformer((mod, s) -> new ExpandMacros(mod, kem, files, globalOptions, kompileOptions).expand(s), "expand macros"))
                .andThen(ModuleTransformer.fromKTransformerWithModuleInfo(convertCellCollections::apply, "convert cell to the underlying collections"))
                .andThen(ModuleTransformer.fromRuleBodyTransformer(JavaBackend::ADTKVariableToSortedVariable, "ADT.KVariable to SortedVariable"))
                .andThen(ModuleTransformer.fromRuleBodyTransformer(JavaBackend::convertKSeqToKApply, "kseq to kapply"))
                .andThen(ModuleTransformer.fromRuleBodyTransformer(NormalizeKSeq.self(), "normalize kseq"))
                .andThen(mod -> JavaBackend.markRegularRules(def, mod))
                .andThen(ModuleTransformer.fromSentenceTransformer(new AddConfigurationRecoveryFlags()::apply, "add refers_THIS_CONFIGURATION_marker"))
                .apply(m);
    }

    private static Sentence markRegularRules(Definition d, ConfigurationInfoFromModule configInfo, Sentence s, String att) {
        if (s instanceof org.kframework.definition.Rule) {
            org.kframework.definition.Rule r = (org.kframework.definition.Rule) s;
            if (r.body() instanceof KApply && d.mainModule().sortFor().apply(((KApply) r.body()).klabel()).equals(configInfo.topCell())) {
                return org.kframework.definition.Rule.apply(r.body(), r.requires(), r.ensures(), r.att().add(att));
            } else
                return r;
        } else
            return s;
    }

    private static Module markRegularRules(Definition d, Module mod) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(d.mainModule());
        return ModuleTransformer.fromSentenceTransformer(s -> markRegularRules(d, configInfo, s, "specification"), "mark regular rules").apply(mod);
    }

        /**
         * Put a marker on the "regular" (i.e. non function/macro/etc.) rules that we can use later.
         */
    private static Definition markRegularRules(Definition d) {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(d.mainModule());
        return DefinitionTransformer.fromSentenceTransformer((mod, s) -> markRegularRules(d, configInfo, s, Att.topRule()), "mark regular rules").apply(d);
    }

    /**
     * The Java backend expects sorted variables, so transform them to the sorted flavor.
     */
    public static K ADTKVariableToSortedVariable(K ruleBody) {
        return new TransformK() {
            public K apply(KVariable kvar) {
                return new SortedADT.SortedKVariable(kvar.name(), kvar.att());
            }
        }.apply(ruleBody);
    }

    /**
     * Replace variables which only appear once in the pattern and have no side condition on them (including no sorting),
     * with a special marker called THE_VARIABLE which the backend uses for special speed optimisations.
     */
    private static Sentence markSingleVariables(Sentence s) {
        if (s instanceof Rule) {
            Rule r = (Rule) s;

            if (!r.att().contains(Att.topRule()))
                return r;

            Map<KVariable, Integer> varCount = new HashMap<>();
            VisitK markerVisitor = new VisitK() {
                public void apply(KVariable kvar) {
                    varCount.put(kvar, varCount.getOrDefault(kvar, 0) + 1);
                }
            };
            markerVisitor.apply(r.body());
            markerVisitor.apply(r.requires());
            markerVisitor.apply(r.ensures());

            TransformK markerAdder = new TransformK() {
                public K apply(KVariable kvar) {
                    if (kvar instanceof SortedADT.SortedKVariable && ((SortedADT.SortedKVariable) kvar).sort().equals(Sorts.K()) && varCount.get(kvar) == 1
                            && !kvar.name().equals(KLabels.THIS_CONFIGURATION)) {
                        return new SortedADT.SortedKVariable("THE_VARIABLE", Att.empty());
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

    @Override
    public Set<String> excludedModuleTags() {
        return java.util.Collections.singleton("concrete");
    }
}
