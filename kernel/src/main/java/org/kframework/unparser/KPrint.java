// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import com.davekoelle.AlphanumComparator;
import com.google.inject.Inject;
import com.google.common.collect.Multiset;
import com.google.common.collect.HashMultiset;
import javax.annotation.Nullable;
import org.kframework.attributes.Att;
import org.kframework.backend.kore.ModuleToKORE;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.AddSortInjections;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.CompiledDefinition;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.Term;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import org.kframework.utils.inject.RequestScoped;
import scala.Option;
import scala.Tuple2;

import java.io.IOException;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;

/**
 * Class for printing information and outputting to files using various serializers.
 */
@RequestScoped
public class KPrint {

    private final KExceptionManager kem;
    private final FileUtil          files;
    private final TTYInfo           tty;
    private final KompileOptions    kompileOptions;

    public final PrintOptions options;

    @Nullable
    private final CompiledDefinition compiledDefinition;
    private final Module executionModule;
    private final AddSortInjections addSortInjections;

    public KPrint() {
        this(new KExceptionManager(new GlobalOptions()), FileUtil.testFileUtil(), new TTYInfo(false, false, false),
                new PrintOptions(), null, new KompileOptions());
    }

    @Inject
    public KPrint(KExceptionManager kem, FileUtil files, TTYInfo tty, PrintOptions options,
                  CompiledDefinition compiledDefinition, KompileOptions kompileOptions) {
        this.kem = kem;
        this.files = files;
        this.tty = tty;
        this.options = options;
        this.compiledDefinition = compiledDefinition;
        if (compiledDefinition != null) {
            this.executionModule = compiledDefinition.executionModule();
            this.addSortInjections = new AddSortInjections(executionModule);
        } else {
            this.executionModule = null;
            this.addSortInjections = null;
        }

        this.kompileOptions = kompileOptions;
    }

    //TODO(dwightguth): use Writer
    public void outputFile(String output) {
        outputFile(output.getBytes());
    }

    public void outputFile(byte[] output) {
        outputFile(output, System.out);
    }

    public void outputFile(byte[] output, OutputStream out) {
        if (options.outputFile == null) {
            try {
                out.write(output);
                out.flush();
            } catch (IOException e) {
                throw KEMException.internalError(e.getMessage(), e);
            }
        } else {
            files.saveToWorkingDirectory(options.outputFile, output);
        }
    }

    public void prettyPrint(Definition def, Module module, Consumer<byte[]> print, K result) {
        prettyPrint(def, module, print, result, Sorts.GeneratedTopCell());
    }

    public void prettyPrint(Definition def, Module module, Consumer<byte[]> print, K result, Sort s) {
        print.accept(prettyPrint(def, module, result, s, options.color(tty.stdout, files.getEnv()), options.output));
    }

    public byte[] prettyPrint(Definition def, Module module, K result) {
        return prettyPrint(def, module, result, Sorts.GeneratedTopCell(), options.color(tty.stdout, files.getEnv()), options.output);
    }

    public byte[] prettyPrint(Definition def, Module module, K orig, Sort s, ColorSetting colorize, OutputModes outputMode) {
        K result = abstractTerm(module, orig);
        switch (outputMode) {
            case KAST:
            case NONE:
            case BINARY:
            case JSON:
            case LATEX:
                return serialize(result, outputMode);
            case PRETTY:
                Module prettyUnparsingModule = RuleGrammarGenerator.getCombinedGrammar(module, false, files).getExtensionModule();
                return (unparseTerm(result, prettyUnparsingModule, colorize) + "\n").getBytes();
            case PROGRAM: {
                RuleGrammarGenerator gen = new RuleGrammarGenerator(def);
                Module programUnparsingModule = RuleGrammarGenerator.getCombinedGrammar(gen.getProgramsGrammar(module), false, files).getParsingModule();
                return (unparseTerm(result, programUnparsingModule, colorize) + "\n").getBytes();
            }
            case KORE:
                if (compiledDefinition == null) {
                    throw KEMException.criticalError("KORE output requires a compiled definition.");
                }
                ModuleToKORE converter = new ModuleToKORE(module, compiledDefinition.topCellInitializer, kompileOptions);
                result = ExpandMacros.forNonSentences(executionModule, files, kompileOptions, false).expand(result);
                result = addSortInjections.addSortInjections(result, s);
                StringBuilder sb = new StringBuilder();
                converter.convert(result, sb);
                return sb.toString().getBytes();
            default:
                throw KEMException.criticalError("Unsupported output mode without a CompiledDefinition: " + outputMode);
        }
    }

    public byte[] serialize(K term) {
        return KPrint.serialize(term, options.output);
    }

    public static byte[] serialize(K term, OutputModes outputMode) {
        switch (outputMode) {
            case KAST:
                return (ToKast.apply(term) + "\n").getBytes();
            case NONE:
                return "".getBytes();
            case BINARY:
                return ToBinary.apply(term);
            case JSON:
                return ToJson.apply(term);
            case LATEX:
                return ToLatex.apply(term);
            default:
                throw KEMException.criticalError("Unsupported serialization mode: " + outputMode);
        }
    }

    public String unparseTerm(K input, Module test) {
        return unparseTerm(input, test, options.color(tty.stdout, files.getEnv()));
    }

    public String unparseTerm(K input, Module test, ColorSetting colorize) {
        return unparseInternal(test, input, colorize);
    }

    private Term disambiguateForUnparse(Module mod, Term t) {
        if (kompileOptions.isKore()) {
            return t;
        } else {
            return ParseInModule.disambiguateForUnparse(mod, t);
        }
    }

    private String unparseInternal(Module mod, K input, ColorSetting colorize) {
        ExpandMacros expandMacros = ExpandMacros.forNonSentences(mod, files, kompileOptions, true);
        return Formatter.format(
                new AddBrackets(mod).addBrackets((ProductionReference) disambiguateForUnparse(mod, KOREToTreeNodes.apply(KOREToTreeNodes.up(mod, expandMacros.expand(input)), mod, kompileOptions.isKore()))), options.color(tty.stdout, files.getEnv()));
    }

    public K abstractTerm(Module mod, K term) {
        K filteredSubst     = options.noFilterSubstitution || !kompileOptions.isKore() ? term : filterSubst(term, mod);
        K origNames         = options.restoreOriginalNames ? restoreOriginalNameIfPresent(filteredSubst) : filteredSubst;
        K collectionsSorted = options.noSortCollections    ? origNames : sortCollections(mod, origNames);
        //non-determinism is still possible if associative/commutative collection terms start with anonymous vars
        K alphaRenamed      = options.noAlphaRenaming      ? collectionsSorted : alphaRename(collectionsSorted);
        K squashedTerm      = squashTerms(mod, alphaRenamed);
        K flattenedTerm     = flattenTerms(mod, squashedTerm);

        return flattenedTerm;
    }

    private Set<KVariable> vars(K term) {
      return new HashSet<>(multivars(term));
    }

    private Multiset<KVariable> multivars(K term) {
      Multiset<KVariable> vars = HashMultiset.create();
      new VisitK() {
        @Override
        public void apply(KVariable var) {
          vars.add(var);
        }
      }.apply(term);
      return vars;
    }

    private K filterSubst(K term, Module mod) {
      if (!(term instanceof KApply)) {
        return term;
      }
      KApply kapp = (KApply)term;
      if (kapp.klabel().head().equals(KLabels.ML_AND)) {
        return filterConjunction(kapp, mod);
      } else if (kapp.klabel().head().equals(KLabels.ML_OR)) {
        KLabel unit = KLabel(KLabels.ML_FALSE.name(), kapp.klabel().params().apply(0));
        List<K> disjuncts = Assoc.flatten(kapp.klabel(), kapp.items(), unit);
        return disjuncts.stream()
                .map(d -> filterConjunction(d, mod))
                .distinct()
                .reduce((k1, k2) -> KApply(kapp.klabel(), k1, k2))
                .orElse(KApply(unit));
      } else if (kapp.klabel().head().equals(KLabels.ML_EQUALS)) {
        KLabel unit = KLabel(KLabels.ML_TRUE.name(), kapp.klabel().params().apply(0));
        return filterEquality(kapp, multivars(kapp), mod).orElse(KApply(unit));
      } else {
        return term;
      }
    }

    private K filterConjunction(K term, Module mod) {
      if (!(term instanceof KApply)) {
        return term;
      }
      KApply kapp = (KApply)term;
      if (kapp.klabel().head().equals(KLabels.ML_AND)) {
        KLabel unit = KLabel(KLabels.ML_TRUE.name(), kapp.klabel().params().apply(0));
        List<K> conjuncts = Assoc.flatten(kapp.klabel(), kapp.items(), unit);
        return conjuncts.stream()
                .map(d -> filterEquality(d, multivars(kapp), mod))
                .filter(Optional::isPresent)
                .map(Optional::get)
                .reduce((k1, k2) -> KApply(kapp.klabel(), k1, k2))
                .orElse(KApply(unit));
      } else if (kapp.klabel().head().equals(KLabels.ML_EQUALS)) {
        KLabel unit = KLabel(KLabels.ML_TRUE.name(), kapp.klabel().params().apply(0));
        return filterEquality(kapp, multivars(kapp), mod).orElse(KApply(unit));
      } else {
        return term;
      }
    }

    public Optional<K> filterEquality(K term, Multiset<KVariable> vars, Module mod) {
      if (!(term instanceof KApply)) {
        return Optional.of(term);
      }
      KApply kapp = (KApply)term;
      if (kapp.klabel().head().equals(KLabels.ML_EQUALS)) {
        if (!(kapp.items().get(0) instanceof KVariable) &&
            (!(kapp.items().get(0) instanceof KApply) ||
             !mod.attributesFor().apply(((KApply)kapp.items().get(0)).klabel()).contains(Att.FUNCTION()))) {
          return Optional.of(term);
        }
        Set<KVariable> leftVars = vars(kapp.items().get(0));
        if (leftVars.stream().filter(v -> !v.att().contains("anonymous")).findAny().isPresent()) {
          return Optional.of(term);
        }
        for (KVariable var : leftVars) {
          if (vars.count(var) != 1) {
            return Optional.of(term);
          }
        }
        return Optional.empty();
      } else {
        return Optional.of(term);
      }
    }

    private K sortCollections(Module mod, K input) {
        Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(mod, false, files).getExtensionModule();
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                if (k.klabel() instanceof KVariable) {
                    return super.apply(k);
                }
                Att att = unparsingModule.attributesFor().apply(KLabel(k.klabel().name()));
                if (att.contains("comm") && att.contains("assoc") && att.contains("unit")) {
                    List<K> items = new ArrayList<>(Assoc.flatten(k.klabel(), k.klist().items(), KLabel(att.get("unit"))));
                    List<Tuple2<String, K>> printed = new ArrayList<>();
                    for (K item : items) {
                        String s = unparseInternal(unparsingModule, apply(item), ColorSetting.OFF);
                        printed.add(Tuple2.apply(s, item));
                    }
                    printed.sort(Comparator.comparing(Tuple2::_1, new AlphanumComparator()));
                    items = printed.stream().map(Tuple2::_2).map(this::apply).collect(Collectors.toList());
                    return items.stream().reduce((k1, k2) -> KApply(k.klabel(), k1, k2)).orElse(KApply(KLabel(att.get("unit"))));
                }
                return super.apply(k);
            }
        }.apply(input);
    }

    private K alphaRename(K input) {
        return new TransformK() {
            Map<KVariable, KVariable> renames = new HashMap<>();
            int newCount = 0;

            @Override
            public K apply(KVariable k) {
                if (k.att().contains("anonymous")) {
                    return renames.computeIfAbsent(k, k2 -> KVariable("V" + newCount++, k.att()));
                }
                return k;
            }
        }.apply(input);
    }

    private K restoreOriginalNameIfPresent(K input) {
        return new TransformK() {
            @Override
            public K apply(KVariable k) {
                if (k.att().contains("originalName")) {
                    return KVariable(k.att().get("originalName"), k.att());
                }
                return k;
            }
        }.apply(input);
    }

    private K squashTerms(Module mod, K input) {
        return new TransformK() {
            @Override
            public K apply(KApply orig) {
                String name = orig.klabel().name();
                return options.omittedKLabels.contains(name)   ? omitTerm(mod, orig)
                     : options.tokenizedKLabels.contains(name) ? tokenizeTerm(mod, orig)
                     : options.tokastKLabels.contains(name)    ? toKASTTerm(mod, orig)
                     : super.apply(orig) ;
            }
        }.apply(input);
    }

    private static K omitTerm(Module mod, KApply kapp) {
        Sort finalSort = Sorts.K();
        Option<Sort> termSort = mod.sortFor().get(kapp.klabel());
        if (! termSort.isEmpty()) {
            finalSort = termSort.get();
        }
        return KApply(kapp.klabel(), KToken(kapp.klabel().name(), finalSort));
    }

    private K tokenizeTerm(Module mod, KApply kapp) {
        Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(mod, false, files).getExtensionModule();
        String tokenizedTerm   = unparseTerm(kapp, unparsingModule, ColorSetting.OFF);
        Sort   finalSort       = Sorts.K();
        Option<Sort> termSort  = mod.sortFor().get(kapp.klabel());
        if (! termSort.isEmpty()) {
            finalSort = termSort.get();
        }
        return KApply(kapp.klabel(), KToken(tokenizedTerm, finalSort));
    }

    private static K toKASTTerm(Module mod, KApply kapp) {
        String       kastTerm  = ToKast.apply(kapp);
        Sort         finalSort = Sorts.K();
        Option<Sort> termSort  = mod.sortFor().get(kapp.klabel());
        if (! termSort.isEmpty()) {
            finalSort = termSort.get();
        }
        return KToken(kastTerm, finalSort);
    }

    private K flattenTerms(Module mod, K input) {
        return new TransformK() {
            @Override
            public K apply(KApply orig) {
                K newK = super.apply(orig);
                if (! (newK instanceof KApply)) {
                    return newK;
                }
                KApply kapp = (KApply) newK;
                String name = orig.klabel().name();
                return options.flattenedKLabels.contains(name) ? flattenTerm(mod, kapp)
                     : kapp ;
            }
        }.apply(input);
    }

    private static K flattenTerm(Module mod, KApply kapp) {
        List<K> items = new ArrayList<>();
        Att att = mod.attributesFor().apply(KLabel(kapp.klabel().name()));
        if (att.contains("assoc") && att.contains("unit")) {
            items = Assoc.flatten(kapp.klabel(), kapp.klist().items(), KLabel(att.get("unit")));
        } else {
            items = kapp.klist().items();
        }
        return KApply(kapp.klabel(), KList(items), kapp.att());
    }
}
