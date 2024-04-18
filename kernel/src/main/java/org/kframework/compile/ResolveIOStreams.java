// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.attributes.Location;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Definition;
import org.kframework.definition.Import;
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
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import scala.Option;
import scala.Tuple2;
import scala.collection.Set;

/** Created by daejunpark on 9/6/15. */
public record ResolveIOStreams(Definition definition, KExceptionManager kem) {

  /**
   * Update modules that declare stream cells in configuration, by using builtin *-STREAM modules.
   * Steps:
   *
   * <ol type="1">
   *   <li>Update the init rules of the stream cells.
   *   <li>Update rules that refer to 'stdin' stream.
   *   <li>Import rules from *-STREAM modules (with modification of cell names).
   * </ol>
   */
  public Module resolve(Module m) {
    java.util.Set<Production> streamProductions = getStreamProductions(m.sentences());
    if (streamProductions.isEmpty()) {
      return m;
    } else {
      java.util.Set<Sentence> sentences = mutable(m.localSentences());
      // NOTE: it may seem inefficient to have duplicated for-loops here,
      //      but such a duplication makes each step much simpler;
      //      moreover the number of `streamProductions` is at most two (or possibly three later
      // on),
      //      so that the duplication effect is not that much.
      // Step 1.
      for (Production p : streamProductions) {
        sentences = sentences.stream().map(s -> resolveInitRule(p, s)).collect(Collectors.toSet());
      }
      // Step 2.
      for (Production p : streamProductions) {
        if (p.att().get(Att.STREAM()).equals("stdin")) {
          sentences.addAll(getStdinStreamUnblockingRules(p, sentences));
        }
      }
      // Step 3.
      if (!getStreamProductions(m.localSentences()).isEmpty()) {
        for (Production p : streamProductions) {
          sentences.addAll(getStreamModuleSentences(p));
        }
      }
      return Module(
          m.name(),
          m.imports()
              .$bar(Set(Import(definition.getModule("K-IO").get(), true)))
              .$bar(Set(Import(definition.getModule("K-REFLECTION").get(), true)))
              .toSet(),
          immutable(sentences),
          m.att());
    }
  }

  // Collect productions that have 'stream' attribute
  private java.util.Set<Production> getStreamProductions(Set<Sentence> sentences) {
    java.util.Set<Production> productions = new HashSet<>();
    for (Sentence s : mutable(sentences)) {
      if (s instanceof Production p) {
        if (p.att().getOption(Att.STREAM()).isDefined()) {
          checkStreamName(p.att().get(Att.STREAM()));
          productions.add(p);
        }
      }
    }
    return productions;
  }

  private void checkStreamName(String streamName) {
    ArrayList<String> streams = new ArrayList<String>();
    streams.add("stdin");
    streams.add("stdout");

    if (!streams.contains(streamName)) {
      throw KEMException.compilerError(
          "Make sure you give the correct stream names: "
              + streamName
              + "\nIt should be one of "
              + streams);
    }
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
    String initLabel =
        GenerateSentencesFromConfigDecl.getInitLabel(streamSort); // initInCell, initOutCell
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
    String streamName = streamProduction.att().get(Att.STREAM()); // stdin, stdout
    String initLabel =
        GenerateSentencesFromConfigDecl.getInitLabel(
            Sort(
                GenerateSentencesFromConfigDecl.getSortOfCell(
                    streamName))); // initStdinCell, initStdoutCell
    String cellLabel = "<" + streamName + ">"; // <stdin>, <stdout>

    java.util.List<Sentence> initRules =
        stream(getStreamModule(streamName).localSentences())
            .filter(s -> isInitRule(initLabel, cellLabel, s))
            .toList();
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
    String streamName = streamProduction.att().get(Att.STREAM()); // stdin, stdout
    String builtinCellLabel = "<" + streamName + ">"; // <stdin>, <stdout>
    KLabel userCellLabel = streamProduction.klabel().get(); // <in>, <out>

    java.util.Set<Sentence> sentences = new HashSet<>();
    for (Sentence s : mutable(getStreamModule(streamName).localSentences())) {
      if (s instanceof Rule rule) {
        if (rule.att().contains(Att.STREAM())) {
          // Update cell names
          K body =
              new TransformK() {
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
        } else if (rule.att().contains(Att.PROJECTION())) {
          sentences.add(rule);
        }
      } else if (s instanceof Production production) {
        if (production.sort().toString().equals("Stream")
            || production.att().contains(Att.PROJECTION())) {
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
  private java.util.Set<Sentence> getStdinStreamUnblockingRules(
      Production streamProduction, java.util.Set<Sentence> sentences) {
    KLabel userCellLabel = streamProduction.klabel().get(); // <in>

    // find rules with currently supported matching patterns
    java.util.Set<Tuple2<Rule, String>> rules = new HashSet<>();
    for (Sentence s : sentences) {
      if (s instanceof Rule rule) {
        java.util.List<String> sorts =
            isSupportingRulePatternAndGetSortNameOfCast(streamProduction, rule);
        assert sorts.size() <= 1;
        if (sorts.size() == 1) {
          rules.add(Tuple2.apply(rule, sorts.get(0)));
        }
      }
    }

    // generate additional unblocking rules for each of the above rules
    java.util.Set<Sentence> newSentences = new HashSet<>();
    for (Tuple2<Rule, String> r : rules) {
      Rule rule = r._1();
      String sort = r._2();

      K body =
          new TransformK() {
            @Override
            public K apply(KApply k) {
              if (k.klabel().name().equals(userCellLabel.name())) {
                return getUnblockRuleBody(streamProduction, sort);
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

  // return (a list of) sort names of cast if the given rule has the supported pattern matching over
  // input stream cell,
  // otherwise return empty.
  // currently, the list of sort names of cast should be a singleton.
  /*
   * Currently supported rule pattern is:
   * rule <k> read() => V ... </k>
   *      <in>
   *        ListItem(V:Int) => .List
   *        ...
   *      </in>
   */
  private java.util.List<String> isSupportingRulePatternAndGetSortNameOfCast(
      Production streamProduction, Rule rule) {
    KLabel userCellLabel = streamProduction.klabel().get(); // <in>

    java.util.List<String> sorts = new ArrayList<>();
    new VisitK() {
      @Override
      public void apply(KApply k) {
        if (k.klabel().name().equals(userCellLabel.name())) {
          String sort = wellformedAndGetSortNameOfCast(k.klist());
          if (!sort.isEmpty()) {
            sorts.add(sort);
          } else {
            if (k.att()
                .getOption(Att.LOCATION(), Location.class)
                .isDefined()) { // warning only for user-provided rules
              throw KEMException.compilerError(
                  "Unsupported matching pattern in stdin stream cell.\n"
                      + "The currently supported pattern is: <in> ListItem(V:Sort) => .List ..."
                      + " </in>",
                  k);
            }
          }
        }
        super.apply(k);
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
            if (KLabels.NO_DOTS.equals(k1.klabel())
                && k1.klist().size() == 0
                && KLabels.DOTS.equals(k3.klabel())
                && k3.klist().size() == 0) {

              KRewrite k2 = (KRewrite) klist.items().get(1);
              KApply k2l = (KApply) k2.left();
              KApply k2r = (KApply) k2.right();
              if (k2l.klabel().name().equals("ListItem")
                  && k2l.klist().size() == 1
                  && k2r.klabel().name().equals(".List")
                  && k2r.klist().size() == 0) {

                KApply k2li = (KApply) k2l.klist().items().get(0);
                if (k2li.klabel().name().startsWith("#SemanticCastTo")
                    && k2li.klist().size() == 1
                    && k2li.klist().items().get(0) instanceof KVariable) {
                  return ResolveSemanticCasts.getSortNameOfCast(
                      k2li); // k2li.klabel().name().substring("#SemanticCastTo".length());
                }
              }
            }
          }
        } catch (ClassCastException ignored) {
        }
        return "";
      }
    }.apply(rule.body());

    return sorts;
  }

  // get rule body of the `[unblock]` rule (it should exist an unique one),
  // instantiating with proper `Sort` and `Delimiters` values.
  // this method should be called with stdin stream production, not with stdout stream.
  /*
   * Currently supporting generated rule would be:
   * rule <k> read() ... </k>
   *      <in>
   *        `.List => ListItem(#parseInput("Int", " \n\t\r"))`
   *        ListItem(#buffer(_:String))
   *        ...
   *      </in>
   */
  private K getUnblockRuleBody(Production streamProduction, String sort) {
    String streamName = streamProduction.att().get(Att.STREAM());
    assert streamName.equals("stdin"); // stdin
    String builtinCellLabel = "<" + streamName + ">"; // <stdin>
    KLabel userCellLabel = streamProduction.klabel().get(); // <in>

    java.util.List<Sentence> unblockRules =
        stream(getStreamModule(streamName).localSentences())
            .filter(
                s ->
                    s instanceof Rule
                        && s.att()
                            .getOptional(Att.LABEL())
                            .map(lbl -> lbl.equals("STDIN-STREAM.stdinUnblock"))
                            .orElse(false))
            .toList();
    assert unblockRules.size() == 1;
    Rule unblockRule = (Rule) unblockRules.get(0);

    return new TransformK() {
      @Override
      public K apply(KApply k) {
        if (k.klabel().name().equals("#SemanticCastToString") && k.klist().size() == 1) {
          K i = k.klist().items().get(0);
          if (i instanceof KVariable x) {
            switch (x.name()) {
              case "?Sort":
                return KToken("\"" + sort + "\"", Sorts.String());
              case "?Delimiters":
                // TODO(Daejun): support `delimiter` attribute in stream cell
                return KToken("\" \\n\\t\\r\"", Sorts.String());
              default:
                // fall through
            }
          }
        }
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
    }.apply(unblockRule.body());
  }
}
