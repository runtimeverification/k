// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
package org.kframework.compile;

import static org.kframework.Collections.*;
import static org.kframework.definition.Constructors.*;
import static org.kframework.kore.KORE.*;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Context;
import org.kframework.definition.Definition;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KLabel;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.TransformK;
import org.kframework.kore.VisitK;
import org.kframework.parser.inner.ParseInModule;
import org.kframework.parser.inner.RuleGrammarGenerator;
import org.kframework.parser.outer.Outer;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.errorsystem.KExceptionManager;
import org.kframework.utils.file.FileUtil;
import scala.Option;
import scala.collection.JavaConverters;
import scala.collection.Set;

public class ResolveFreshConstants {

  private final KExceptionManager kem;
  private final Definition def;
  private final FileUtil files;
  private Module m;
  private final java.util.Set<KVariable> freshVars = new HashSet<>();
  private final Map<KVariable, Integer> offsets = new HashMap<>();
  private final String manualTopCell;
  private final int initialFresh;

  private void reset() {
    freshVars.clear();
    offsets.clear();
  }

  private Rule resolve(Rule rule) {
    reset();
    analyze(rule.body());
    analyze(rule.requires());
    analyze(rule.ensures());
    finishAnalysis();
    Rule withFresh =
        Rule(
            addFreshCell(transform(rule.body())),
            transform(rule.requires()),
            transform(rule.ensures()),
            rule.att());
    if (rule.att().contains(Att.INITIALIZER())) {
      K left = RewriteToTop.toLeft(withFresh.body());
      if (left instanceof KApply kapp) {
        if (kapp.klabel().equals(KLabels.INIT_GENERATED_TOP_CELL)) {
          KApply right = (KApply) RewriteToTop.toRight(withFresh.body());
          KApply cells = (KApply) right.items().get(1);
          List<K> items = new ArrayList<>(cells.items());
          items.add(KApply(KLabels.INIT_GENERATED_COUNTER_CELL));
          KApply newCells = KApply(cells.klabel(), immutable(items));
          List<K> rightItems = new ArrayList<>(right.items());
          rightItems.set(1, newCells);
          return Rule(
              KRewrite(left, KApply(right.klabel(), immutable(rightItems))),
              withFresh.requires(),
              withFresh.ensures(),
              withFresh.att());
        }
      }
    }
    K left = RewriteToTop.toLeft(rule.body());
    if (left instanceof KApply kapp) {
      if (kapp.klabel().name().equals("#withConfig")) {
        left = kapp.items().get(0);
      }
      if (left instanceof KApply) {
        kapp = (KApply) left;
        if (m.attributesFor()
            .get(kapp.klabel())
            .getOrElse(() -> Att.empty())
            .contains(Att.FUNCTION())) {
          return rule;
        }
      }
    }
    return withFresh;
  }

  public static boolean isFreshVar(KVariable kvar) {
    return kvar.name().startsWith("!");
  }

  private void analyze(K term) {
    new VisitK() {
      @Override
      public void apply(KVariable k) {
        if (isFreshVar(k)) {
          freshVars.add(k);
        }
        super.apply(k);
      }
    }.apply(term);
  }

  private void finishAnalysis() {
    int i = 0;
    for (KVariable v : freshVars) {
      offsets.put(v, i++);
    }
  }

  private static final KVariable FRESH =
      KVariable("#Fresh", Att.empty().add(Att.SORT(), Sort.class, Sorts.Int()));

  private K transform(K term) {
    return new TransformK() {
      @Override
      public K apply(KVariable k) {
        if (freshVars.contains(k)) {
          Optional<Sort> s = k.att().getOptional(Att.SORT(), Sort.class);
          if (s.isEmpty()) {
            throw KEMException.compilerError("Fresh constant used without a declared sort.", k);
          }
          Option<KLabel> lbl = m.freshFunctionFor().get(s.get());
          if (!lbl.isDefined()) {
            throw KEMException.compilerError("No fresh generator defined for sort " + s, k);
          }
          return KApply(
              lbl.get(),
              KApply(KLabel("_+Int_"), FRESH, KToken(offsets.get(k).toString(), Sorts.Int())));
        }
        return super.apply(k);
      }
    }.apply(term);
  }

  private K addFreshCell(K body) {
    if (freshVars.size() == 0) {
      return body;
    }
    KApply cellTerm =
        IncompleteCellUtils.make(
            KLabels.GENERATED_COUNTER_CELL,
            false,
            KRewrite(
                FRESH,
                KApply(
                    KLabel("_+Int_"),
                    FRESH,
                    KToken(Integer.toString(freshVars.size()), Sorts.Int()))),
            false);
    return KApply(KLabels.CELLS, body, cellTerm);
  }

  private Context resolve(Context context) {
    reset();
    analyze(context.body());
    analyze(context.requires());
    finishAnalysis();
    return new Context(
        addFreshCell(transform(context.body())), transform(context.requires()), context.att());
  }

  private Production resolve(Production prod) {
    if (prod.klabel().isDefined() && prod.klabel().get().equals(KLabels.GENERATED_TOP_CELL)) {
      List<ProductionItem> pis =
          stream(prod.items()).collect(Collectors.toCollection(ArrayList::new));
      // expecting a production of the form <generatedTop> C1 C2 Cx.. </generatedTop>
      // insert the GeneratedCounterCell as the last cell
      pis.add(prod.items().size() - 1, NonTerminal(Sorts.GeneratedCounterCell()));
      return Production(prod.klabel().get(), prod.sort(), immutable(pis), prod.att());
    }
    return prod;
  }

  private Sentence resolve(Sentence s) {
    if (s instanceof Rule) {
      return resolve((Rule) s);
    } else if (s instanceof Context) {
      return resolve((Context) s);
    } else if (s instanceof Production) {
      return resolve((Production) s);
    }
    return s;
  }

  public ResolveFreshConstants(
      KExceptionManager kem, Definition def, String manualTopCell, FileUtil files) {
    this(kem, def, manualTopCell, files, 0);
  }

  public ResolveFreshConstants(
      KExceptionManager kem,
      Definition def,
      String manualTopCell,
      FileUtil files,
      int initialFresh) {
    this.kem = kem;
    this.def = def;
    this.manualTopCell = manualTopCell;
    this.files = files;
    this.initialFresh = initialFresh;
  }

  public Module resolve(Module m) {
    this.m = m;
    scala.collection.immutable.Set<Sentence> sentences = map(this::resolve, m.localSentences());
    KToken counterCellLabel = KToken("generatedCounter", Sort("#CellName"));
    KApply freshCell =
        KApply(
            KLabel("#configCell"),
            counterCellLabel,
            KApply(KLabel("#cellPropertyListTerminator")),
            KToken(Integer.toString(initialFresh), Sorts.Int()),
            counterCellLabel);

    java.util.Set<Sentence> counterSentences = new HashSet<>();
    counterSentences.add(
        Production(
            KLabel("getGeneratedCounterCell"),
            Sorts.GeneratedCounterCell(),
            Seq(
                Terminal("getGeneratedCounterCell"),
                Terminal("("),
                NonTerminal(Sorts.GeneratedTopCell()),
                Terminal(")")),
            Att.empty().add(Att.FUNCTION())));
    counterSentences.add(
        Rule(
            KRewrite(
                KApply(
                    KLabel("getGeneratedCounterCell"),
                    IncompleteCellUtils.make(
                        KLabels.GENERATED_TOP_CELL,
                        true,
                        KVariable(
                            "Cell",
                            Att.empty().add(Att.SORT(), Sort.class, Sorts.GeneratedCounterCell())),
                        true)),
                KVariable(
                    "Cell", Att.empty().add(Att.SORT(), Sort.class, Sorts.GeneratedCounterCell()))),
            BooleanUtils.TRUE,
            BooleanUtils.TRUE));

    if (m.name().equals(def.mainModule().name())) {
      if (!m.definedKLabels().contains(KLabels.GENERATED_TOP_CELL)) {
        RuleGrammarGenerator gen = new RuleGrammarGenerator(def);
        ParseInModule mod = RuleGrammarGenerator.getCombinedGrammar(gen.getConfigGrammar(m), files);
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(m);
        Sort topCellSort;
        try {
          topCellSort = configInfo.getRootCell();
        } catch (KEMException e) {
          if (manualTopCell != null) {
            topCellSort = Outer.parseSort(manualTopCell);
          } else {
            throw e;
          }
        }
        KLabel topCellLabel = configInfo.getCellLabel(topCellSort);
        Production prod = m.productionsFor().apply(topCellLabel).head();
        KToken cellName = KToken(prod.att().get(Att.CELL_NAME()), Sort("#CellName"));

        KToken topCellToken = KToken(KLabels.GENERATED_TOP_CELL_NAME, Sort("#CellName"));
        K generatedTop =
            KApply(
                KLabel("#configCell"),
                topCellToken,
                KApply(KLabel("#cellPropertyListTerminator")),
                KApply(KLabels.CELLS, KApply(KLabel("#externalCell"), cellName), freshCell),
                topCellToken);
        Set<Sentence> newSentences =
            GenerateSentencesFromConfigDecl.gen(
                kem, generatedTop, BooleanUtils.TRUE, Att.empty(), mod.getExtensionModule());
        sentences = sentences.$bar(newSentences).toSet();
        sentences = sentences.$bar(immutable(counterSentences)).toSet();
      }
    }
    if (m.localKLabels().contains(KLabels.GENERATED_TOP_CELL)) {
      RuleGrammarGenerator gen = new RuleGrammarGenerator(def);
      ParseInModule mod = RuleGrammarGenerator.getCombinedGrammar(gen.getConfigGrammar(m), files);
      Set<Sentence> newSentences =
          GenerateSentencesFromConfigDecl.gen(
              kem, freshCell, BooleanUtils.TRUE, Att.empty(), mod.getExtensionModule());
      sentences = sentences.$bar(newSentences).toSet();
      sentences = sentences.$bar(immutable(counterSentences)).toSet();
    }
    if (sentences.equals(m.localSentences())) {
      return m;
    }
    // fix the format after inserting the GeneratedCounterCell
    sentences =
        immutable(
            stream(sentences)
                .map(s -> s instanceof Production ? fixFormat((Production) s) : s)
                .collect(Collectors.toSet()));
    return Module(m.name(), m.imports(), sentences, m.att());
  }

  private static Production fixFormat(Production prod) {
    if (prod.klabel().isDefined() && prod.klabel().get().equals(KLabels.GENERATED_TOP_CELL)) {
      List<Integer> cellPositions = new ArrayList<Integer>();
      int i = 1;
      for (ProductionItem p : JavaConverters.seqAsJavaList(prod.items())) {
        if (p instanceof NonTerminal nt) {
          if (!nt.sort().equals(Sorts.GeneratedCounterCell())) {
            cellPositions.add(i);
          }
        }
        i++;
      }
      StringBuilder format = new StringBuilder();
      if (cellPositions.size() == 1) {
        format.append("%").append(cellPositions.get(0));
      } else {
        format.append("%1%i");
        int j;
        for (j = 0; j < cellPositions.size(); j++) {
          format.append("%n%").append(cellPositions.get(j));
        }
        format.append("%d%n%").append(cellPositions.get(j - 1) + 2);
      }
      return prod.withAtt(prod.att().add(Att.FORMAT(), format.toString()));
    }
    return prod;
  }
}
