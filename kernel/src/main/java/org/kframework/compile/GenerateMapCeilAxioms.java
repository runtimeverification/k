package org.kframework.compile;

import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Constructors;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.Rule;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.K;
import org.kframework.kore.KLabel;
import org.kframework.kore.KORE;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import scala.Option;
import scala.collection.JavaConverters;
import scala.collection.Seq;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static org.kframework.kore.KORE.*;

public class GenerateMapCeilAxioms {

    private final Module module;
    private final KompileOptions options;
    public GenerateMapCeilAxioms(Module m, KompileOptions kompileOptions) {
        this.module = m;
        this.options = kompileOptions;
    }

    public Module gen(Module m) {
        return m.replaceSortedRules(genRule());
    }

    private Seq<Rule> genRule() {
        List<Rule> sortedRules = new ArrayList<>(JavaConverters.seqAsJavaList(module.sortedRules()));
        if (options.backend.equals("haskell")) {
            module.sortedProductions().toStream().filter(this::isGeneratedInKeysOp).toStream().foreach(
                    p -> {
                        if (!options.disableCeilSimplificationRules) {
                            genMapCeilAxioms(p, sortedRules);
                        }
                        return p;
                    }
            );
        }
        return JavaConverters.asScalaBuffer(sortedRules).toSeq();
    }

    private boolean isGeneratedInKeysOp(Production prod) {
        Option<String> hook = prod.att().getOption(Att.HOOK());
        if (hook.isEmpty()) return false;
        if (!hook.get().equals("MAP.in_keys")) return false;
        return (!prod.klabel().isEmpty());
    }

    private void genMapCeilAxioms(Production prod, Collection<Rule> rules) {
        Sort mapSort = prod.nonterminal(1).sort();
        scala.collection.Set<Production> mapProds = module.productionsForSort().apply(mapSort.head());
        Production concatProd = mapProds.find(p -> hasHookValue(p.att(), "MAP.concat")).get();
        Production elementProd = mapProds.find(p -> hasHookValue(p.att(), "MAP.element")).get();
        Seq<NonTerminal> nonterminals = elementProd.nonterminals();
        Sort sortParam = KORE.Sort(AddSortInjections.SORTPARAM_NAME, KORE.Sort("Q"));

        // rule
        //   #Ceil(MapItem(K1, K2, ..., Kn) Rest:Map)
        // =>
        //  {(@K1 in_keys(@Rest)) #Equals false} #And #Ceil(@K2) #And ... #And #Ceil(@Kn)
        // Note: The {_ in_keys(_) #Equals false} condition implies
        // #Ceil(@K1) and #Ceil(@Rest).
        // [simplification]

        K restMapSet = KVariable("@Rest", Att.empty().add(Sort.class, mapSort));
        KLabel ceilMapLabel = KORE.KLabel(KLabels.ML_CEIL.name(), mapSort, sortParam);
        KLabel andLabel = KORE.KLabel(KLabels.ML_AND.name(), sortParam);

        // arguments of MapItem and their #Ceils
        List<K> setArgs = new ArrayList<>();
        K setArgsCeil = KApply(KORE.KLabel(KLabels.ML_TRUE.name(), sortParam));
        for (int i = 0; i < nonterminals.length(); i++) {
            Sort sort = nonterminals.apply(i).sort();
            KVariable setVar = KORE.KVariable("@K" + i, Att.empty().add(Sort.class, sort));
            setArgs.add(setVar);
            if (i > 0) {
                KLabel ceil = KORE.KLabel(KLabels.ML_CEIL.name(), sort, sortParam);
                setArgsCeil = KApply(andLabel, setArgsCeil, KApply(ceil, setVar));
            }
        }
        Seq<K> setArgsSeq = JavaConverters.iterableAsScalaIterable(setArgs).toSeq();

        KLabel equalsLabel = KORE.KLabel(KLabels.ML_EQUALS.name(), Sorts.Bool(), sortParam);
        Rule ceilMapRule = Constructors.Rule(
                KRewrite(
                        KApply(ceilMapLabel,
                                KApply(concatProd.klabel().get(),
                                        KApply(elementProd.klabel().get(),
                                                setArgsSeq,
                                                Att.empty()
                                        ),
                                        restMapSet
                                )
                        )
                        ,
                        KApply(andLabel,
                                KApply(equalsLabel,
                                        KApply(prod.klabel().get(),
                                                setArgs.get(0),
                                                restMapSet
                                        ),
                                        BooleanUtils.FALSE
                                ),
                                setArgsCeil
                        )
                )
                , BooleanUtils.TRUE
                , BooleanUtils.TRUE
                , Att.empty().add(Att.SIMPLIFICATION())
        );
        rules.add(ceilMapRule);
    }

    static boolean hasHookValue(Att atts, String value) {
        return atts.contains(Att.HOOK()) &&
                atts.get(Att.HOOK()).equals(value);
    }

}
