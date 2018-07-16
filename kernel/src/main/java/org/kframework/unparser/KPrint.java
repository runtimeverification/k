// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.unparser;

import com.davekoelle.AlphanumComparator;
import org.kframework.attributes.Att;
import org.kframework.compile.ExpandMacros;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
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
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import static org.kframework.kore.KORE.*;

/**
 * Class for printing information and outputting to files using various serializers.
 */
public class KPrint {

    private static KExceptionManager kem;
    private static FileUtil          files;
    private static TTYInfo           tty;

    public static PrintOptions options;

    public KPrint() {
        this(new KExceptionManager(new GlobalOptions()), FileUtil.testFileUtil(), new TTYInfo(false, false, false), new PrintOptions());
    }

    public KPrint(KExceptionManager kem, FileUtil files, TTYInfo tty, PrintOptions options) {
        this.kem     = kem;
        this.files   = files;
        this.tty     = tty;
        this.options = options;
    }

    //TODO(dwightguth): use Writer
    public static void outputFile(String output) {
        outputFile(output.getBytes());
    }

    public static void outputFile(byte[] output) {
        if (options.outputFile == null) {
            try {
                System.out.write(output);
            } catch (IOException e) {
                throw KEMException.internalError(e.getMessage(), e);
            }
        } else {
            files.saveToWorkingDirectory(options.outputFile, output);
        }
    }

    public static void prettyPrint(Definition def, Module module, KompileOptions kompile, Consumer<byte[]> print, K result, ColorSetting colorize) {
        print.accept(prettyPrint(def, module, kompile, result, colorize));
    }

    public static void prettyPrint(Definition def, Module module, KompileOptions kompile, Consumer<byte[]> print, K result) {
        print.accept(prettyPrint(def, module, kompile, result, options.color(tty.stdout, files.getEnv())));
    }

    public static byte[] prettyPrint(Definition def, Module module, KompileOptions kompile, K result, ColorSetting colorize) {
        switch (options.output) {
        case KAST:
            return (ToKast.apply(result) + "\n").getBytes();
        case NONE:
            return "".getBytes();
        case PRETTY: {
            Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(module, false).getExtensionModule();
            return (unparseTerm(result, unparsingModule, kompile, colorize) + "\n").getBytes();
        } case PROGRAM: {
            RuleGrammarGenerator gen = new RuleGrammarGenerator(def);
            Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(gen.getProgramsGrammar(module), false).getParsingModule();
            return (unparseTerm(result, unparsingModule, kompile, colorize) + "\n").getBytes();
        } case BINARY:
            return ToBinary.apply(result);
        default:
            throw KEMException.criticalError("Unsupported output mode: " + options.output);
        }
    }

    public static String unparseTerm(K input, Module test, KompileOptions kompile) {
        return unparseTerm(input, test, kompile, options.color(tty.stdout, files.getEnv()));
    }

    public static String unparseTerm(K input, Module test, KompileOptions kompile, ColorSetting colorize) {
        K sortedComm = new TransformK() {
            @Override
            public K apply(KApply k) {
                if (k.klabel() instanceof KVariable) {
                    return super.apply(k);
                }
                Att att = test.attributesFor().apply(KLabel(k.klabel().name()));
                if (att.contains("comm") && att.contains("assoc") && att.contains("unit")) {
                    List<K> items = new ArrayList<>(Assoc.flatten(k.klabel(), k.klist().items(), KLabel(att.get("unit"))));
                    List<Tuple2<String, K>> printed = new ArrayList<>();
                    for (K item : items) {
                        String s = unparseInternal(test, apply(item), kompile, ColorSetting.OFF);
                        printed.add(Tuple2.apply(s, item));
                    }
                    printed.sort(Comparator.comparing(Tuple2::_1, new AlphanumComparator()));
                    items = printed.stream().map(Tuple2::_2).map(this::apply).collect(Collectors.toList());
                    return items.stream().reduce((k1, k2) -> KApply(k.klabel(), k1, k2)).orElse(KApply(KLabel(att.get("unit"))));
                }
                return super.apply(k);
            }
        }.apply(input);
        K alphaRenamed = new TransformK() {
            Map<KVariable, KVariable> renames = new HashMap<>();
            int newCount = 0;

            @Override
            public K apply(KVariable k) {
                if (k.att().contains("anonymous")) {
                    return renames.computeIfAbsent(k, k2 -> KVariable("V" + newCount++, k.att()));
                }
                return k;
            }
        }.apply(sortedComm);
        return unparseInternal(test, alphaRenamed, kompile, colorize);
    }

    private static String unparseInternal(Module mod, K input, KompileOptions kompile, ColorSetting colorize) {
        ExpandMacros expandMacros = new ExpandMacros(mod, files, kompile, true);
        return Formatter.format(
                new AddBrackets(mod).addBrackets((ProductionReference) ParseInModule.disambiguateForUnparse(mod, KOREToTreeNodes.apply(KOREToTreeNodes.up(mod, expandMacros.expand(input)), mod))), options.color(tty.stdout, files.getEnv()));
    }
}
