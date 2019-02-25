// Copyright (c) 2018-2019 K Team. All Rights Reserved.
package org.kframework.unparser;

import com.google.inject.Inject;
import com.davekoelle.AlphanumComparator;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.main.GlobalOptions;
import org.kframework.parser.ProductionReference;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.parser.concrete2kore.ParseInModule;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import scala.Tuple2;

import java.io.IOException;
import java.io.OutputStream;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import scala.Option;

import static org.kframework.kore.KORE.*;

/**
 * Class for printing information and outputting to files using various serializers.
 */
public class KPrint {

    private final KExceptionManager kem;
    private final FileUtil          files;
    private final TTYInfo           tty;
    private final KompileOptions    kompileOptions;

    public final PrintOptions options;

    public KPrint() {
        this(new KExceptionManager(new GlobalOptions()), FileUtil.testFileUtil(), new TTYInfo(false, false, false), new PrintOptions(), new KompileOptions());
    }

    public KPrint(KompileOptions kompileOptions) {
        this(new KExceptionManager(kompileOptions.global), FileUtil.testFileUtil(), new TTYInfo(false, false, false), new PrintOptions(), kompileOptions);
    }

    @Inject
    public KPrint(KExceptionManager kem, FileUtil files, TTYInfo tty, PrintOptions options, KompileOptions kompileOptions) {
        this.kem            = kem;
        this.files          = files;
        this.tty            = tty;
        this.options        = options;
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
            } catch (IOException e) {
                throw KEMException.internalError(e.getMessage(), e);
            }
        } else {
            files.saveToWorkingDirectory(options.outputFile, output);
        }
    }

    public void prettyPrint(Definition def, Module module, Consumer<byte[]> print, K result, ColorSetting colorize) {
        print.accept(prettyPrint(def, module, result, colorize));
    }

    public void prettyPrint(Definition def, Module module, Consumer<byte[]> print, K result) {
        print.accept(prettyPrint(def, module, result, options.color(tty.stdout, files.getEnv())));
    }

    public byte[] prettyPrint(Definition def, Module module, K result) {
        return prettyPrint(def, module, result, options.color(tty.stdout, files.getEnv()));
    }

    public byte[] prettyPrint(Definition def, Module module, K orig, ColorSetting colorize) {
        return prettyPrint(def, module, orig, colorize, options.output);
    }

    public byte[] prettyPrint(Definition def, Module module, K orig, ColorSetting colorize, OutputModes outputMode) {
        K result = abstractTerm(module, orig);
        switch (outputMode) {
            case KAST:
            case NONE:
            case BINARY:
            case JSON:
            case PRETTY:
                return prettyPrint(module, orig, colorize, outputMode);
            case PROGRAM: {
                RuleGrammarGenerator gen = new RuleGrammarGenerator(def);
                Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(gen.getProgramsGrammar(module), false).getParsingModule();
                return (unparseTerm(result, unparsingModule, colorize) + "\n").getBytes();
            } default:
                throw KEMException.criticalError("Unsupported output mode: " + outputMode);
        }
    }

    public byte[] prettyPrint(Module module, K orig, ColorSetting colorize, OutputModes outputMode) {
        K result = abstractTerm(module, orig);
        switch (outputMode) {
            case KAST:
            case NONE:
            case BINARY:
            case JSON:
                return serialize(result, outputMode);
            case PRETTY: {
                Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(module, false).getExtensionModule();
                return (unparseTerm(result, unparsingModule, colorize) + "\n").getBytes();
            } default:
                throw KEMException.criticalError("Unsupported output mode without a Definition: " + outputMode);
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

    private String unparseInternal(Module mod, K input, ColorSetting colorize) {
        ExpandMacros expandMacros = new ExpandMacros(mod, files, kompileOptions, true);
        return Formatter.format(
                new AddBrackets(mod).addBrackets((ProductionReference) ParseInModule.disambiguateForUnparse(mod, KOREToTreeNodes.apply(KOREToTreeNodes.up(mod, expandMacros.expand(input)), mod))), options.color(tty.stdout, files.getEnv()));
    }

    public K abstractTerm(Module mod, K term) {
        K collectionsSorted = options.noSortCollections ? term              : sortCollections(mod, term);
        K alphaRenamed      = options.noAlphaRenaming   ? collectionsSorted : alphaRename(collectionsSorted);
        K squashedTerm      = squashTerms(mod, alphaRenamed);
        K flattenedTerm     = flattenTerms(mod, squashedTerm);

        return flattenedTerm;
    }

    private K sortCollections(Module mod, K input) {
        Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(mod, false).getExtensionModule();
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
        Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(mod, false).getExtensionModule();
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
                String name = orig.klabel().name();
                return options.flattenedKLabels.contains(name) ? flattenTerm(mod, orig)
                     : super.apply(orig) ;
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
