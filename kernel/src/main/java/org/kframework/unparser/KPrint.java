// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.unparser;

import com.davekoelle.AlphanumComparator;
import org.apache.commons.lang3.tuple.Pair;
import org.kframework.attributes.Att;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Module;
import org.kframework.kore.Assoc;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.file.TTYInfo;
import scala.Tuple2;

import java.io.BufferedReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import java.util.stream.Collectors;

import scala.Option;

import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

/**
 * Class for printing information and outputting to files using various serializers.
 */
public class KPrint {

    private static KExceptionManager kem;
    private static FileUtil          files;
    private static TTYInfo           tty;

    public static PrintOptions options;

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

    public static void prettyPrint(Module module, Consumer<byte[]> print, K result) {
        print.accept(prettyPrint(module, result));
    }

    public static byte[] prettyPrint(Module module, K result) {
        K abstracted = abstractionPass(module, result);
        switch (options.output) {
        case KAST:
            return (ToKast.apply(abstracted) + "\n").getBytes();
        case NONE:
            return "".getBytes();
        case PRETTY:
            Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(module, false).getExtensionModule();
            return (unparseTerm(abstracted, unparsingModule) + "\n").getBytes();
        case BINARY:
            return ToBinary.apply(abstracted);
        case JSON:
            return ToJson.apply(abstracted);
        default:
            throw KEMException.criticalError("Unsupported output mode: " + options.output);
        }
    }

    private static K abstractionPass(Module unparsingModule, K contents) {
        K omitted    = KPrint.omitKLabels    (unparsingModule, contents);
        K flattened  = KPrint.flattenKLabels (unparsingModule, omitted);
        K tokenized  = KPrint.tokenizeKLabels(unparsingModule, flattened);
        K tostringed = KPrint.tostringKLabels(unparsingModule, tokenized);
        return tostringed;
    }

    /**
     * Methods `{omit,tokenize,flatten}KLabels` allows the user to specify some KLabels below which they do not care for accurate term representation.
     * For example, a user-interface level tool (eg. state explorer) may not need accurate term representation to work, but handling huge Json terms may be a hindrance.
     */
    public static K omitTerm(Module module, K k) {
        if (! (k instanceof KApply)) return k;
        KApply kapp           = (KApply) k;
        Sort   finalSort      = Sorts.K();
        Option<Sort> termSort = module.sortFor().get(kapp.klabel());
        if (! termSort.isEmpty()) {
            finalSort = termSort.get();
        }
        return KToken(kapp.klabel().name(), finalSort);
    }

    public static K omitKLabels(Module module, K result) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                if (options.omittedKLabels.contains(k.klabel().name())) {
                    List<K> newArgs = k.klist().items().stream().map(arg -> omitTerm(module, arg)).collect(Collectors.toList());
                    return KApply(k.klabel(), KList(newArgs), k.att());
                } else {
                    return super.apply(k);
                }
            }
        }.apply(result);
    }

    public static K tokenizeTerm(Module module, K k) {
        if (! (k instanceof KApply)) return k;
        KApply kapp            = (KApply) k;
        Module unparsingModule = RuleGrammarGenerator.getCombinedGrammar(module, false).getExtensionModule();
        String tokenizedTerm   = unparseTerm(kapp, unparsingModule);
        Sort   finalSort       = Sorts.K();
        Option<Sort> termSort  = module.sortFor().get(kapp.klabel());
        if (! termSort.isEmpty()) {
            finalSort = termSort.get();
        }
        return KToken(tokenizedTerm, finalSort);
    }

    public static K tokenizeKLabels(Module module, K result) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                if (options.tokenizedKLabels.contains(k.klabel().name())) {
                    List<K> newArgs = k.klist().items().stream().map(arg -> tokenizeTerm(module, arg)).collect(Collectors.toList());
                    return KApply(k.klabel(), KList(newArgs), k.att());
                } else {
                    return super.apply(k);
                }
            }
        }.apply(result);
    }

    public static K tostringTerm(Module module, K k) {
        if (! (k instanceof KApply)) return k;
        KApply       kapp         = (KApply) k;
        String       tostringTerm = kapp.toString();
        Sort         finalSort    = Sorts.K();
        Option<Sort> termSort     = module.sortFor().get(kapp.klabel());
        if (! termSort.isEmpty()) {
            finalSort = termSort.get();
        }
        return KToken(tostringTerm, finalSort);
    }

    public static K tostringKLabels(Module module, K result) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                if (options.tostringKLabels.contains(k.klabel().name())) {
                    List<K> newArgs = k.klist().items().stream().map(arg -> tostringTerm(module, arg)).collect(Collectors.toList());
                    return KApply(k.klabel(), KList(newArgs), k.att());
                } else {
                    return super.apply(k);
                }
            }
        }.apply(result);
    }

    public static K flattenKLabels(Module module, K result) {
        return new TransformK() {
            @Override
            public K apply(KApply k) {
                if (options.flattenedKLabels.contains(k.klabel().name())) {
                    List<K> items = new ArrayList<>();
                    Att att = module.attributesFor().apply(KLabel(k.klabel().name()));
                    if (att.contains("assoc") && att.contains("unit")) {
                        items = Assoc.flatten(k.klabel(), k.klist().items(), KLabel(att.get("unit")));
                    } else {
                        items = k.klist().items();
                    }
                    return KApply(k.klabel(), KList(items), k.att());
                } else {
                    return super.apply(k);
                }
            }
        }.apply(result);
    }

    private static String unparseTerm(K input, Module test) {
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
                        String s = Formatter.format(new AddBrackets(test).addBrackets(KOREToTreeNodes.apply(KOREToTreeNodes.up(test, apply(item)), test)), ColorSetting.OFF);
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
                    return renames.computeIfAbsent(k, k2 -> KVariable(k.toString(), k.att()));
                }
                return k;
            }
        }.apply(sortedComm);
        return Formatter.format(
                new AddBrackets(test).addBrackets(KOREToTreeNodes.apply(KOREToTreeNodes.up(test, alphaRenamed), test)), KPrint.options.color(KPrint.tty.stdout, KPrint.files.getEnv()));
    }
}
