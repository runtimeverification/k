// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.kore.compile;

import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;
import scala.Tuple2;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

/**
 * Created by daejunpark on 9/6/15.
 */
public class ResolveIOStreams {

    private final Definition definition;

    public ResolveIOStreams(Definition definition) {
        this.definition = definition;
    }

    /**
     * Update modules that declare stream cells in configuration,
     * by using builtin *-STREAM modules.
     *
     * Steps:
     * 1. Update the init rules of the stream cells.
     * 2. Update rules that refer to 'stdin' stream.
     * 3. Import rules from *-STREAM modules (with modification of cell names).
     */
    public Module resolve(Module m) {
        java.util.Set<Production> streamProductions = getStreamProductions(m);
        if (streamProductions.isEmpty()) {
            return m;
        } else {
            java.util.Set<Sentence> sentences = mutable(m.localSentences());
            // Step 1.
            for (Production p : streamProductions) {
                sentences = sentences.stream().map(s -> resolveInitRule(p,s)).collect(Collectors.toSet());
            }
            // Step 2.
            for (Production p : streamProductions) {
                if (p.att().<String>get("stream").get().equals("stdin")) {
                    sentences.addAll(getStdinStreamUnblockingRules(p,sentences));
                }
            }
            // Step 3.
            for (Production p : streamProductions) {
                sentences.addAll(getStreamModuleSentences(p));
            }
            return Module(m.name(), m.imports(), immutable(sentences), m.att());
        }
    }

    // Collect productions that have 'stream' attribute
    private java.util.Set<Production> getStreamProductions(Module m) {
        java.util.Set<Production> productions = new HashSet<>();
        for (Sentence s : mutable(m.localSentences())) {
            if (s instanceof Production) {
                Production p = (Production) s;
                if (p.att().<String>get("stream").isDefined()) {
                    productions.add(p);
                }
            }
        }
        return productions;
    }

    private Sentence resolveInitRule(Production p, Sentence s) {
        if (s instanceof Rule) {
            return resolveInitRule(p, (Rule) s);
        } else {
            return s;
        }
    }

    // Step 1.
    private Rule resolveInitRule(Production streamProduction, Rule rule) {
        Sort streamSort = streamProduction.sort(); // InCell, OutCell
        String initLabel = GenerateSentencesFromConfigDecl.getInitLabel(streamSort); // initInCell, initOutCell
        KLabel cellLabel = streamProduction.klabel().get(); // <in>, <out>

        // rule initInCell(Init) => <in> ... </in>
        if (isInitRule(initLabel, cellLabel.name(), rule)) {
            KRewrite body = (KRewrite) rule.body();
            KApply right = (KApply) body.right();
            KList klist = getContentsOfInitRule(streamProduction);
            right = KApply(right.klabel(), klist, right.att());
            body = KRewrite(body.left(), right, body.att());
            return Rule(body, rule.requires(), rule.ensures(), rule.att());
        }
        return rule;
    }

    // TODO(Daejun): rule should have contained an initializer attribute.
    private boolean isInitRule(String initLabel, String cellLabel, Sentence s) {
        try {
            // rule initXCell(Init) => <x> ... </x>
            KRewrite body = (KRewrite) ((Rule) s).body();
            KApply left = (KApply) body.left();
            KApply right = (KApply) body.right();
            return left.klabel().name().equals(initLabel) // initXCell
                    && right.klabel().name().equals(cellLabel); // <x>
        } catch (ClassCastException ignored) {
            return false;
        }
    }

    // Get an initializer rule from the built-in *-STREAM module
    private KList getContentsOfInitRule(Production streamProduction) {
        String streamName = streamProduction.att().<String>get("stream").get(); // stdin, stdout
        String initLabel = GenerateSentencesFromConfigDecl.getInitLabel(
                Sort(GenerateSentencesFromConfigDecl.getSortOfCell(streamName))); // initStdinCell, initStdoutCell
        String cellLabel = "<" + streamName + ">"; // <stdin>, <stdout>

        java.util.List<Sentence> initRules =
                stream(getStreamModule(streamName).localSentences())
                        .filter(s -> isInitRule(initLabel, cellLabel, s))
                        .collect(Collectors.toList());
        assert initRules.size() == 1;
        Sentence initRule = initRules.get(0);

        // rule initXCell(Init) => <x> ... </x>
        KRewrite body = (KRewrite) ((Rule) initRule).body();
        KApply right = (KApply) body.right();
        return right.klist();
    }

    // Step 3.
    // get sentences from stream module:
    // - productions whose sort is `Stream`
    // - rules that have `stream` attribute, but changing cell names according to user-defined one.
    private java.util.Set<Sentence> getStreamModuleSentences(Production streamProduction) {
        String streamName = streamProduction.att().<String>get("stream").get(); // stdin, stdout
        String builtinCellLabel = "<" + streamName + ">"; // <stdin>, <stdout>
        KLabel userCellLabel = streamProduction.klabel().get(); // <in>, <out>

        java.util.Set<Sentence> sentences = new HashSet<>();
        for (Sentence s : mutable(getStreamModule(streamName).localSentences())) {
            if (s instanceof Rule) {
                Rule rule = (Rule) s;
                if (rule.att().contains("stream")) {
                    // Update cell names
                    K body = new TransformKORE() {
                        @Override
                        public K apply(KApply k) {
                            k = (KApply) super.apply(k);
                            return KApply(apply(k.klabel()), k.klist(), k.att());
                        }
                        private KLabel apply(KLabel klabel) {
                            if (klabel.name().equals(builtinCellLabel)) {
                                return userCellLabel;
                            } else {
                                return klabel;
                            }
                        }
                    }.apply(rule.body());

                    rule = Rule(body, rule.requires(), rule.ensures(), rule.att());
                    sentences.add(rule);
                }
            } else if (s instanceof Production) {
                Production production = (Production) s;
                if (production.sort().name().equals("Stream")) {
                    sentences.add(production);
                }
            }
        }
        return sentences;
    }

    private Module getStreamModule(String streamName) {
        // TODO(Daejun): fix hard-coded stream module naming convention
        String moduleName = streamName.toUpperCase() + "-STREAM";
        Option<Module> module = definition.getModule(moduleName);
        if (module.isDefined()) {
            return module.get();
        } else {
            throw KEMException.compilerError("no such module: " + moduleName);
        }
    }

    // Step 2.
    /*
     * From the following stdin stream reference rule:
     * rule <k> read() => V ... </k>
     *      <in>
     *        ListItem(V:Int) => .List
     *        ...
     *      </in>
     *
     * Generate the following auxiliary rule:
     * rule <k> read() ... </k>
     *      <in>
     *        `.List => ListItem(#parseInput("Int", " \n\t\r"))`
     *        ListItem(#buffer(_:String))
     *        ...
     *      </in>
     */
    private java.util.Set<Sentence> getStdinStreamUnblockingRules(Production streamProduction,
                                                                  java.util.Set<Sentence> sentences) {
        KLabel streamCellLabel = streamProduction.klabel().get(); // <in>

        java.util.List<String> sorts = new ArrayList<>();
        VisitKORE visitor = new VisitKORE() {
            @Override
            public Void apply(KApply k) {
                if (k.klabel().name().equals(streamCellLabel.name())) {
                    String sort = wellformedAndGetSortNameOfCast(k.klist());
                    if (!sort.isEmpty()) {
                        sorts.add(sort);
                  //} else {
                  //    throw KEMException.compilerError("Unsupported matching pattern in stdin stream cell." +
                  //        " Currently the supported pattern is: e.g., <in> ListItem(V:Sort) => .List ... </in>", k);
                    }
                    return null;
                }
                return super.apply(k);
            }

            // TODO(Daejun): it support only pattern matching on the top of stream.
            //               more patterns need to be supported as well.
            /*
             * Return cast sort name if well formed, otherwise empty string.
             *
             * klist is well formed if it consists of:
             *   #noDots(.KList)
             *   ListItem(#SemanticCastToInt(V)) => .List
             *   #dots(.KList)
             *
             * which comes from, e.g.,:
             *   <in> ListItem(V:Int) => .List ... </in>
             */
            private String wellformedAndGetSortNameOfCast(KList klist) {
                try {
                    if (klist.size() == 3) {
                        KApply k1 = (KApply) klist.items().get(0);
                        KApply k3 = (KApply) klist.items().get(2);
                        if (k1.klabel().name().equals("#noDots") && k1.klist().size() == 0 &&
                                k3.klabel().name().equals("#dots") && k3.klist().size() == 0) {

                            KRewrite k2 = (KRewrite) klist.items().get(1);
                            KApply k2l = (KApply) k2.left();
                            KApply k2r = (KApply) k2.right();
                            if (k2l.klabel().name().equals("ListItem") && k2l.klist().size() == 1 &&
                                    k2r.klabel().name().equals(".List") && k2r.klist().size() == 0) {

                                KApply k2li = (KApply) k2l.klist().items().get(0);
                                if (k2li.klabel().name().startsWith("#SemanticCastTo") && k2li.klist().size() == 1 &&
                                        k2li.klist().items().get(0) instanceof KVariable) {
                                    return ResolveSemanticCasts.getSortNameOfCast(k2li); // k2li.klabel().name().substring("#SemanticCastTo".length());
                                }
                            }
                        }
                    }
                } catch (ClassCastException ignored) {
                }
                return "";
            }
        };

        java.util.Set<Tuple2<Rule,String>> rules = new HashSet<>();
        for (Sentence s : sentences) {
            if (s instanceof Rule) {
                Rule rule = (Rule) s;
                sorts.clear();
                visitor.apply(rule.body());
                assert sorts.size() <= 1;
                if (sorts.size() == 1) {
                    rules.add(Tuple2.apply(rule,sorts.get(0)));
                }
            }
        }

        java.util.Set<Sentence> newSentences = new HashSet<>();
        for (Tuple2<Rule,String> r : rules) {
            Rule rule = r._1();
            String sort = r._2();

            // TODO(Daejun): generalize it by using additional annotations in STDIN-STREAM module
            // Generate:
            // rule <k> read() ... </k>
            //      <in>
            //        `.List => ListItem(#parseInput("Int", " \n\t\r"))`
            //        ListItem(#buffer(_:String))
            //        ...
            //      </in>
            K body = new TransformKORE() {
                @Override
                public K apply(KApply k) {
                    if (k.klabel().name().equals(streamCellLabel.name())) {
                        KApply content = KApply(KLabel("_List_"), KList(
                            // .List => ListItem(#parseInput(sort, " \n\t\r"))
                            KRewrite(
                                KApply(KLabel(".List"), KList()),
                                KApply(KLabel("ListItem"), KList(
                                    KApply(KLabel("#parseInput"), KList(
                                        KToken("\"" + sort + "\"", Sort("String")),
                                        KToken("\" \\n\\t\\r\"", Sort("String"))
                                    ))
                                ))
                            ),
                            // ListItem(#buffer(_:String))
                            KApply(KLabel("ListItem"), KList(
                                KApply(KLabel("#buffer"), KList(
                                    KApply(KLabel("#SemanticCastTo" + "String"), KList(KVariable("_")))
                                ))
                            ))
                        ));
                        KList klist = KList(
                            KApply(KLabel("#noDots"), KList()),
                            content,
                            KApply(KLabel("#dots"), KList())
                        );
                        return KApply(k.klabel(), klist, k.att());
                    } else {
                        return super.apply(k);
                    }
                }
                @Override
                public K apply(KRewrite k) {
                    // drop rhs
                    return apply(k.left());
                }
            }.apply(rule.body());

            rule = Rule(body, rule.requires(), rule.ensures(), rule.att());
            newSentences.add(rule);
        }

        return newSentences;
    }

}
