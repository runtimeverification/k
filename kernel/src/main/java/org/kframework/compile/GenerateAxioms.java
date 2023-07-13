package org.kframework.compile;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import org.kframework.Collections;
import org.kframework.attributes.Att;
import org.kframework.attributes.HasLocation;
import org.kframework.backend.kore.ConstructorChecks;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.Hooks;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.definition.Constructors;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.definition.Sentence;
import org.kframework.definition.Tag;
import org.kframework.definition.Terminal;
import org.kframework.kompile.KompileOptions;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KList;
import org.kframework.kore.KORE;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.SortHead;
import org.kframework.kore.SortHead;
import org.kframework.kore.VisitK;
import org.kframework.unparser.Formatter;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import scala.Option;
import scala.Tuple2;
import scala.collection.JavaConverters;
import scala.collection.Seq;
import scala.collection.Set;
import scala.collection.immutable.Stream;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.kframework.Collections.*;
import static org.kframework.backend.kore.ModuleToKORE.*;
import static org.kframework.kore.KORE.*;

public class GenerateAxioms {
    private String mainModuleName;
    Module module;
    KompileOptions options;

    private final java.util.Set<String> mlBinders = new HashSet<>();

    private static final Pattern identChar = Pattern.compile("[A-Za-z0-9\\-]");

    public GenerateAxioms(String mainModule, KompileOptions kompileOptions) {
        mainModuleName = mainModule;
        options = kompileOptions;
    }

    public Module gen(Module m) {
        if (!m.name().equals(mainModuleName)) {
            return m;
        }
        module = m;
        java.lang.StringBuilder syntax = new java.lang.StringBuilder();
        java.lang.StringBuilder semantics = new java.lang.StringBuilder();

        List<Rule> sortedRules = new ArrayList<>(JavaConverters.seqAsJavaList(module.sortedRules()));
        if (options.backend.equals("haskell")) {
            module.sortedProductions().toStream().filter(this::isGeneratedInKeysOp).foreach(
                    prod -> {
                        if (!options.disableCeilSimplificationRules) {
                            genMapCeilAxioms(prod, sortedRules);
                        }
                        return prod;
                    });
        }
        SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
        for (Rule rule : sortedRules) {
            K left = RewriteToTop.toLeft(rule.body());
            if (left instanceof KApply) {
                KApply kapp = (KApply) left;
                Production prod = production(kapp);
                if (prod.att().contains(Att.FUNCTION()) || rule.att().contains(Att.ANYWHERE())
                        || ExpandMacros.isMacro(rule)) {
                    functionRules.put(kapp.klabel(), rule);
                }
            }
        }

        for (Production prod : iterable(module.sortedProductions())) {
            if (isBuiltinProduction(prod)) {
                continue;
            }
            if (prod.isSubsort() && !prod.sort().equals(Sorts.K())) {
                genSubsortAxiom(prod, syntax);
                continue;
            }
        }

        for (Production lesser : iterable(module.overloads().elements())) {
            for (Production greater : iterable(
                    module.overloads().relations().get(lesser).getOrElse(() -> Collections.<Production>Set()))) {
                genOverloadedAxiom(lesser, greater, syntax);
            }
        }

        syntax.append("endmodule []\n");

        semantics.append("\n// generated axioms\n");
        java.util.Set<Tuple2<Production, Production>> noConfusion = new HashSet<>();
        for (Production prod : iterable(m.sortedProductions())) {
            if (isBuiltinProduction(prod)) {
                continue;
            }
            if (prod.isSubsort() && !prod.sort().equals(Sorts.K())) {
                genSubsortAxiom(prod, semantics);
                continue;
            }
            if (prod.klabel().isEmpty()) {
                continue;
            }
            if (prod.att().contains(Att.ASSOC())) {
                genAssocAxiom(prod, semantics, m);
            }
            // if (prod.att().contains(Att.COMM())) {
            // genCommAxiom(prod, semantics);
            // }
            if (prod.att().contains(Att.IDEM())) {
                genIdemAxiom(prod, semantics);
            }
            if (isFunction(prod) && prod.att().contains(Att.UNIT())) {
                genUnitAxiom(prod, semantics);
            }
            if (isFunctional(prod, functionRules)) {
                genFunctionalAxiom(prod, semantics);
            }
            if (isConstructor(prod, functionRules)) {
                genNoConfusionAxioms(prod, noConfusion, functionRules, semantics);
            }
        }

        for (Sort sort : iterable(m.sortedAllSorts())) {
            genNoJunkAxiom(sort, semantics);
        }

        for (Production lesser : iterable(m.overloads().elements())) {
            for (Production greater : iterable(
                    m.overloads().relations().get(lesser).getOrElse(() -> Collections.<Production>Set()))) {
                genOverloadedAxiom(lesser, greater, semantics);
            }
        }

        m.addAxiom(semantics.toString());
        return m;
    }

    static boolean hasHookValue(Att atts, String value) {
        return atts.contains(Att.HOOK()) &&
                atts.get(Att.HOOK()).equals(value);
    }

    private void genMapCeilAxioms(Production prod, Collection<Rule> rules) {
        Sort mapSort = prod.nonterminal(1).sort();
        scala.collection.Set<Production> mapProds = module.productionsForSort().apply(mapSort.head());
        Production concatProd = mapProds.find(p -> hasHookValue(p.att(), "MAP.concat")).get();
        Production elementProd = mapProds.find(p -> hasHookValue(p.att(), "MAP.element")).get();
        Seq<NonTerminal> nonterminals = elementProd.nonterminals();
        Sort sortParam = Sort(AddSortInjections.SORTPARAM_NAME, Sort("Q"));

        // rule
        // #Ceil(MapItem(K1, K2, ..., Kn) Rest:Map)
        // =>
        // {(@K1 in_keys(@Rest)) #Equals false} #And #Ceil(@K2) #And ... #And #Ceil(@Kn)
        // Note: The {_ in_keys(_) #Equals false} condition implies
        // #Ceil(@K1) and #Ceil(@Rest).
        // [simplification]

        K restMapSet = KVariable("@Rest", Att.empty().add(Sort.class, mapSort));
        KLabel ceilMapLabel = KLabel(KLabels.ML_CEIL.name(), mapSort, sortParam);
        KLabel andLabel = KLabel(KLabels.ML_AND.name(), sortParam);

        // arguments of MapItem and their #Ceils
        List<K> setArgs = new ArrayList<>();
        K setArgsCeil = KApply(KLabel(KLabels.ML_TRUE.name(), sortParam));
        for (int i = 0; i < nonterminals.length(); i++) {
            Sort sort = nonterminals.apply(i).sort();
            KVariable setVar = KVariable("@K" + i, Att.empty().add(Sort.class, sort));
            setArgs.add(setVar);
            if (i > 0) {
                KLabel ceil = KLabel(KLabels.ML_CEIL.name(), sort, sortParam);
                setArgsCeil = KApply(andLabel, setArgsCeil, KApply(ceil, setVar));
            }
        }
        Seq<K> setArgsSeq = JavaConverters.iterableAsScalaIterable(setArgs).toSeq();

        KLabel equalsLabel = KLabel(KLabels.ML_EQUALS.name(), Sorts.Bool(), sortParam);
        Rule ceilMapRule = Constructors.Rule(
                KRewrite(
                        KApply(ceilMapLabel,
                                KApply(concatProd.klabel().get(),
                                        KApply(elementProd.klabel().get(),
                                                setArgsSeq,
                                                Att.empty()),
                                        restMapSet)),
                        KApply(andLabel,
                                KApply(equalsLabel,
                                        KApply(prod.klabel().get(),
                                                setArgs.get(0),
                                                restMapSet),
                                        BooleanUtils.FALSE),
                                setArgsCeil)),
                BooleanUtils.TRUE, BooleanUtils.TRUE, Att.empty().add(Att.SIMPLIFICATION()));
        rules.add(ceilMapRule);
    }

    private boolean isGeneratedInKeysOp(Production prod) {
        Option<String> hook = prod.att().getOption(Att.HOOK());
        if (hook.isEmpty())
            return false;
        if (!hook.get().equals("MAP.in_keys"))
            return false;
        return (!prod.klabel().isEmpty());
    }

    private static final boolean METAVAR = false;

    private void convertTokenProd(Sort sort, StringBuilder sb) {
        if (METAVAR) {
            sb.append("\\exists{");
            convert(sort, sb);
            sb.append("} (#Str:#String{}, \\dv{");
            convert(sort, sb);
            sb.append("}(#Str:#String{}))");
        } else {
            sb.append("\\top{");
            convert(sort, sb);
            sb.append("}()");
        }
    }

    private void genNoJunkAxiom(Sort sort, StringBuilder sb) {
        StringBuilder sbTemp = new StringBuilder();
        sbTemp.append("  axiom{} ");
        boolean hasToken = false;
        int numTerms = 0;
        for (Production prod : iterable(mutable(module.productionsForSort()).getOrDefault(sort.head(), Set()).toSeq()
                .sorted(Production.ord()))) {
            if (isFunction(prod) || prod.isSubsort() || isBuiltinProduction(prod)) {
                continue;
            }
            if (prod.klabel().isEmpty() && !((prod.att().contains(Att.TOKEN()) && !hasToken) || prod.isSubsort())) {
                continue;
            }
            numTerms++;
            sbTemp.append("\\or{");
            convert(sort, sbTemp);
            sbTemp.append("} (");
            if (prod.att().contains(Att.TOKEN()) && !hasToken) {
                convertTokenProd(sort, sbTemp);
                hasToken = true;
            } else if (prod.klabel().isDefined()) {
                for (int i = 0; i < prod.arity(); i++) {
                    sbTemp.append("\\exists{");
                    convert(sort, sbTemp);
                    sbTemp.append("} (X").append(i).append(":");
                    convert(prod.nonterminal(i).sort(), prod, sbTemp);
                    sbTemp.append(", ");
                }
                convert(prod.klabel().get(), prod, sbTemp);
                sbTemp.append("(");
                String conn = "";
                for (int i = 0; i < prod.arity(); i++) {
                    sbTemp.append(conn).append("X").append(i).append(":");
                    convert(prod.nonterminal(i).sort(), prod, sbTemp);
                    conn = ", ";
                }
                sbTemp.append(")");
                for (int i = 0; i < prod.arity(); i++) {
                    sbTemp.append(")");
                }
            }
            sbTemp.append(", ");
        }
        for (Sort s : iterable(module.sortedAllSorts())) {
            if (module.subsorts().lessThan(s, sort) && !sort.equals(Sorts.K())) {
                numTerms++;
                sbTemp.append("\\or{");
                convert(sort, sbTemp);
                sbTemp.append("} (");
                sbTemp.append("\\exists{");
                convert(sort, sbTemp);
                sbTemp.append("} (Val:");
                convert(s, sbTemp);
                sbTemp.append(", inj{");
                convert(s, sbTemp);
                sbTemp.append(", ");
                convert(sort, sbTemp);
                sbTemp.append("} (Val:");
                convert(s, sbTemp);
                sbTemp.append("))");
                sbTemp.append(", ");
            }
        }
        Att sortAtt = module.sortAttributesFor().get(sort.head()).getOrElse(() -> KORE.Att());
        if (!hasToken && sortAtt.contains(Att.TOKEN())) {
            numTerms++;
            sbTemp.append("\\or{");
            convert(sort, sbTemp);
            sbTemp.append("} (");
            convertTokenProd(sort, sbTemp);
            sbTemp.append(", ");
            hasToken = true;
        }
        sbTemp.append("\\bottom{");
        convert(sort, sbTemp);
        sbTemp.append("}()");
        for (int i = 0; i < numTerms; i++) {
            sbTemp.append(")");
        }
        sbTemp.append(" [constructor{}()] // no junk");
        if (hasToken && !METAVAR) {
            sbTemp.append(" (TODO: fix bug with \\dv)");
        }
        sbTemp.append("\n");

        // If there are no terms, then we don't need to generate the axiom.
        if (numTerms != 0) {
            sb.append(sbTemp);
        }
    }

    private void genOverloadedAxiom(Production lesser, Production greater, StringBuilder sb) {
        sb.append("  axiom{R} \\equals{");
        convert(greater.sort(), greater, sb);
        sb.append(", R} (");
        convert(greater.klabel().get(), greater, sb);
        sb.append("(");
        String conn = "";
        for (int i = 0; i < greater.nonterminals().size(); i++) {
            sb.append(conn);
            if (greater.nonterminal(i).sort().equals(lesser.nonterminal(i).sort())) {
                sb.append("K").append(i).append(":");
                convert(greater.nonterminal(i).sort(), greater, sb);
            } else {
                sb.append("inj{");
                convert(lesser.nonterminal(i).sort(), lesser, sb);
                sb.append(", ");
                convert(greater.nonterminal(i).sort(), greater, sb);
                sb.append("} (K").append(i).append(":");
                convert(lesser.nonterminal(i).sort(), lesser, sb);
                sb.append(")");
            }
            conn = ",";
        }
        sb.append("), inj{");
        convert(lesser.sort(), lesser, sb);
        sb.append(", ");
        convert(greater.sort(), greater, sb);
        sb.append("} (");
        convert(lesser.klabel().get(), lesser, sb);
        sb.append("(");
        conn = "";
        for (int i = 0; i < lesser.nonterminals().size(); i++) {
            sb.append(conn);
            sb.append("K").append(i).append(":");
            convert(lesser.nonterminal(i).sort(), lesser, sb);
            conn = ",";
        }
        sb.append("))) [overload{}(");
        convert(greater.klabel().get(), greater, sb);
        sb.append("(), ");
        convert(lesser.klabel().get(), lesser, sb);
        sb.append("())] // overloaded production\n");
    }

    private static boolean isBuiltinProduction(Production prod) {
        return prod.klabel().nonEmpty() && ConstructorChecks.isBuiltinLabel(prod.klabel().get());
    }

    private void genSubsortAxiom(Production prod, java.lang.StringBuilder sb) {
        Production finalProd = prod;
        functionalPattern(prod, () -> {
            sb.append("inj{");
            convert(finalProd.getSubsortSort(), finalProd, sb);
            sb.append(", ");
            convert(finalProd.sort(), finalProd, sb);
            sb.append("} (From:");
            convert(finalProd.getSubsortSort(), finalProd, sb);
            sb.append(")");
        }, sb);
        sb.append(" [subsort{");
        convert(prod.getSubsortSort(), prod, sb);
        sb.append(", ");
        convert(prod.sort(), prod, sb);
        sb.append("}()] // subsort\n");
    }

    private void functionalPattern(Production prod, Runnable functionPattern, java.lang.StringBuilder sb) {
        sb.append("  axiom");
        convertParams(prod.klabel(), true, sb);
        sb.append(" \\exists{R} (Val:");
        convert(prod.sort(), prod, sb);
        sb.append(", \\equals{");
        convert(prod.sort(), prod, sb);
        sb.append(", R} (");
        sb.append("Val:");
        convert(prod.sort(), prod, sb);
        sb.append(", ");
        functionPattern.run();
        sb.append("))");
    }

    private void convertParams(Option<KLabel> maybeKLabel, boolean hasR, java.lang.StringBuilder sb) {
        sb.append("{");
        String conn = "";
        if (hasR) {
            sb.append("R");
            if (maybeKLabel.isDefined()) {
                conn = ", ";
            }
        }
        if (maybeKLabel.isDefined()) {
            for (Sort param : iterable(maybeKLabel.get().params())) {
                sb.append(conn);
                convert(param, Seq(param), sb);
                conn = ", ";
            }
        }
        sb.append("}");
    }

    private void genAssocAxiom(Production prod, java.lang.StringBuilder sb, Module m) {
        // s(s(K1,K2),K3) = s(K1,s(K2,K3))
        if (prod.arity() != 2) {
            throw KEMException.compilerError("Found a non-binary production with the assoc attribute", prod);
        }
        if (!(m.subsorts().lessThanEq(prod.sort(), prod.nonterminal(0).sort()) &&
                m.subsorts().lessThanEq(prod.sort(), prod.nonterminal(1).sort()))) {
            throw KEMException.compilerError("Found an associative production with ill formed sorts", prod);
        }
        sb.append("  axiom");
        convertParams(prod.klabel(), true, sb);
        sb.append(" \\equals{");
        convert(prod.sort(), prod, sb);
        sb.append(", R} (");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(K1:");
        convert(prod.sort(), prod, sb);
        sb.append(",K2:");
        convert(prod.sort(), prod, sb);
        sb.append("),K3:");
        convert(prod.sort(), prod, sb);
        sb.append("),");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(K1:");
        convert(prod.sort(), prod, sb);
        sb.append(",");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(K2:");
        convert(prod.sort(), prod, sb);
        sb.append(",K3:");
        convert(prod.sort(), prod, sb);
        sb.append("))) [assoc{}()] // associativity\n");
    }

    private void genIdemAxiom(Production prod, java.lang.StringBuilder sb) {
        // s(K, K) = K
        if (prod.arity() != 2) {
            throw KEMException.compilerError("Found a non-binary production with the assoc attribute", prod);
        }
        if (!(prod.sort().equals(prod.nonterminal(0).sort()) && prod.sort().equals(prod.nonterminal(1).sort()))) {
            throw KEMException.compilerError("Found an associative production with ill formed sorts", prod);
        }
        sb.append("  axiom");
        convertParams(prod.klabel(), true, sb);
        sb.append(" \\equals{");
        convert(prod.sort(), prod, sb);
        sb.append(", R} (");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(K:");
        convert(prod.sort(), prod, sb);
        sb.append(",K:");
        convert(prod.sort(), prod, sb);
        sb.append("),K:");
        convert(prod.sort(), prod, sb);
        sb.append(") [idem{}()] // idempotency\n");
    }

    private void genUnitAxiom(Production prod, StringBuilder sb) {
        // s(K, unit) = K
        // s(unit, K) = K
        if (prod.arity() != 2) {
            throw KEMException.compilerError("Found a non-binary production with the assoc attribute", prod);
        }
        if (!(prod.sort().equals(prod.nonterminal(0).sort()) && prod.sort().equals(prod.nonterminal(1).sort()))) {
            throw KEMException.compilerError("Found an associative production with ill formed sorts", prod);
        }
        KLabel unit = KORE.KLabel(prod.att().get(Att.UNIT()));
        sb.append("  axiom");
        convertParams(prod.klabel(), true, sb);
        sb.append("\\equals{");
        convert(prod.sort(), prod, sb);
        sb.append(", R} (");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(K:");
        convert(prod.sort(), prod, sb);
        sb.append(",");
        convert(unit, sb);
        sb.append("()),K:");
        convert(prod.sort(), prod, sb);
        sb.append(") [unit{}()] // right unit\n");

        sb.append("  axiom");
        convertParams(prod.klabel(), true, sb);
        sb.append("\\equals{");
        convert(prod.sort(), prod, sb);
        sb.append(", R} (");
        convert(prod.klabel().get(), prod, sb);
        sb.append("(");
        convert(unit, sb);
        sb.append("(),K:");
        convert(prod.sort(), prod, sb);
        sb.append("),K:");
        convert(prod.sort(), prod, sb);
        sb.append(") [unit{}()] // left unit\n");
    }

    private void genFunctionalAxiom(Production prod, StringBuilder sb) {
        // exists y . f(...) = y
        Production finalProd = prod;
        functionalPattern(prod, () -> applyPattern(finalProd, "K", sb), sb);
        sb.append(" [functional{}()] // functional\n");
    }

    private void applyPattern(Production prod, String varName, StringBuilder sb) {
        convert(prod.klabel().get(), prod, sb);
        sb.append("(");
        String conn = "";
        for (int i = 0; i < prod.arity(); i++) {
            sb.append(conn);
            sb.append(varName).append(i).append(":");
            convert(prod.nonterminal(i).sort(), prod, sb);
            conn = ", ";
        }
        sb.append(')');
    }

    private boolean isFunction(Production prod) {
        if (!prod.att().contains(Att.FUNCTION())) {
            return false;
        }
        return true;
    }

    private boolean isFunctional(Production prod, SetMultimap<KLabel, Rule> functionRules) {
        Att att = addKoreAttributes(prod, functionRules, java.util.Collections.emptySet());
        return att.contains(Att.FUNCTIONAL());
    }

    private Att addKoreAttributes(Production prod, SetMultimap<KLabel, Rule> functionRules,
            java.util.Set<Production> overloads) {
        boolean isFunctional = !isFunction(prod) || prod.att().contains(Att.TOTAL());
        boolean isConstructor = !isFunction(prod);
        isConstructor &= !prod.att().contains(Att.ASSOC());
        isConstructor &= !prod.att().contains(Att.COMM());
        isConstructor &= !prod.att().contains(Att.IDEM());
        isConstructor &= !(prod.att().contains(Att.FUNCTION()) && prod.att().contains(Att.UNIT()));

        // Later we might set !isConstructor because there are anywhere rules,
        // but if a symbol is a constructor at this point, then it is still
        // injective.
        boolean isInjective = isConstructor;

        boolean isMacro = false;
        boolean isAnywhere = overloads.contains(prod);
        if (prod.klabel().isDefined()) {
            for (Rule r : functionRules.get(prod.klabel().get())) {
                isMacro |= ExpandMacros.isMacro(r);
                isAnywhere |= r.att().contains(Att.ANYWHERE());
            }
        }
        isConstructor &= !isMacro;
        isConstructor &= !isAnywhere;

        Att att = prod.att().remove(Att.CONSTRUCTOR());
        if (att.contains(Att.HOOK()) && !isRealHook(att, options)) {
            att = att.remove(Att.HOOK());
        }
        if (isConstructor) {
            att = att.add(Att.CONSTRUCTOR());
        }
        if (isFunctional) {
            att = att.add(Att.FUNCTIONAL());
        }
        if (isAnywhere) {
            att = att.add(Att.ANYWHERE());
        }
        if (isInjective) {
            att = att.add(Att.INJECTIVE());
        }
        if (isMacro) {
            att = att.add(Att.MACRO());
        }
        // update format attribute with structure expected by backend
        String format = att.getOptional(Att.FORMAT()).orElse(Formatter.defaultFormat(prod.items().size()));
        int nt = 1;
        boolean hasFormat = true;
        boolean printName = stream(prod.items())
                .noneMatch(pi -> pi instanceof NonTerminal && ((NonTerminal) pi).name().isEmpty());
        boolean printEllipses = false;

        for (int i = 0; i < prod.items().size(); i++) {
            if (prod.items().apply(i) instanceof NonTerminal) {
                String replacement;
                if (printName && prod.isPrefixProduction()) {
                    replacement = ((NonTerminal) prod.items().apply(i)).name().get() + ": %" + (nt++);
                    printEllipses = true;
                } else {
                    replacement = "%" + (nt++);
                }
                format = format.replaceAll("%" + (i + 1) + "(?![0-9])", replacement);
            } else if (prod.items().apply(i) instanceof Terminal) {
                format = format.replaceAll("%" + (i + 1) + "(?![0-9])", "%c" + ((Terminal) prod.items().apply(i))
                        .value().replace("\\", "\\\\").replace("$", "\\$").replace("%", "%%") + "%r");
            } else {
                hasFormat = false;
            }
        }
        if (printEllipses && format.contains("(")) {
            int idxLParam = format.indexOf("(") + 1;
            format = format.substring(0, idxLParam) + "... " + format.substring(idxLParam);
        }
        if (hasFormat) {
            att = att.add(Att.FORMAT(), format);
            if (att.contains(Att.COLOR())) {
                boolean escape = false;
                StringBuilder colors = new StringBuilder();
                String conn = "";
                for (int i = 0; i < format.length(); i++) {
                    if (escape && format.charAt(i) == 'c') {
                        colors.append(conn).append(att.get(Att.COLOR()));
                        conn = ",";
                    }
                    if (format.charAt(i) == '%') {
                        escape = true;
                    } else {
                        escape = false;
                    }
                }
                att = att.add(Att.COLORS(), colors.toString());
            }
            StringBuilder sb = new StringBuilder();
            for (ProductionItem pi : iterable(prod.items())) {
                if (pi instanceof NonTerminal) {
                    sb.append('0');
                } else {
                    sb.append('1');
                }
            }
            att = att.add(Att.TERMINALS(), sb.toString());
            if (prod.klabel().isDefined()) {
                List<K> lessThanK = new ArrayList<>();
                Option<scala.collection.Set<Tag>> lessThan = module.priorities().relations()
                        .get(Constructors.Tag(prod.klabel().get().name()));
                if (lessThan.isDefined()) {
                    for (Tag t : iterable(lessThan.get())) {
                        if (ConstructorChecks.isBuiltinLabel(KORE.KLabel(t.name()))) {
                            continue;
                        }
                        lessThanK.add(KApply(KORE.KLabel(t.name())));
                    }
                }
                att = att.add(Att.PRIORITIES(), KList.class, KORE.KList(lessThanK));
                att = att.remove(Att.LEFT());
                att = att.remove(Att.RIGHT());
                att = att.add(Att.LEFT(), KList.class, getAssoc(module.leftAssoc(), prod.klabel().get()));
                att = att.add(Att.RIGHT(), KList.class, getAssoc(module.rightAssoc(), prod.klabel().get()));
            }
        } else {
            att = att.remove(Att.FORMAT());
        }
        // This attribute is a frontend attribute only and is removed from the kore
        // Since it has no meaning outside the frontend
        return att.remove(Att.ORIGINAL_PRD(), Production.class);
    }

    private boolean isRealHook(Att att, KompileOptions options) {
        String hook = att.get(Att.HOOK());
        if (hook.startsWith("ARRAY.")) {
            return false;
        }
        if (options.hookNamespaces.stream().anyMatch(ns -> hook.startsWith(ns + "."))) {
            return true;
        }
        return Hooks.namespaces.stream().anyMatch(ns -> hook.startsWith(ns + "."));
    }

    private KList getAssoc(scala.collection.Set<Tuple2<Tag, Tag>> assoc, KLabel klabel) {
        return KList(stream(assoc).filter(t -> t._1().name().equals(klabel.name()))
                .map(t -> KApply(KLabel(t._2().name()))).collect(Collectors.toList()));
    }

    private boolean isConstructor(Production prod, SetMultimap<KLabel, Rule> functionRules) {
        Att att = addKoreAttributes(prod, functionRules, java.util.Collections.emptySet());
        return att.contains(Att.CONSTRUCTOR());
    }

    private void genNoConfusionAxioms(Production prod, java.util.Set<Tuple2<Production, Production>> noConfusion,
            SetMultimap<KLabel, Rule> functionRulesMap, StringBuilder sb) {
        // c(x1,x2,...) /\ c(y1,y2,...) -> c(x1/\y2,x2/\y2,...)
        if (prod.arity() > 0) {
            sb.append("  axiom");
            convertParams(prod.klabel(), false, sb);
            sb.append("\\implies{");
            convert(prod.sort(), prod, sb);
            sb.append("} (\\and{");
            convert(prod.sort(), prod, sb);
            sb.append("} (");
            applyPattern(prod, "X", sb);
            sb.append(", ");
            applyPattern(prod, "Y", sb);
            sb.append("), ");
            convert(prod.klabel().get(), prod, sb);
            sb.append("(");
            String conn = "";
            for (int i = 0; i < prod.arity(); i++) {
                sb.append(conn);
                sb.append("\\and{");
                convert(prod.nonterminal(i).sort(), prod, sb);
                sb.append("} (X").append(i).append(":");
                convert(prod.nonterminal(i).sort(), prod, sb);
                sb.append(", Y").append(i).append(":");
                convert(prod.nonterminal(i).sort(), prod, sb);
                sb.append(")");
                conn = ", ";
            }
            sb.append(")) [constructor{}()] // no confusion same constructor\n");
        }
        for (Production prod2 : iterable(
                module.productionsForSort().apply(prod.sort().head()).toSeq().sorted(Production.ord()))) {
            // !(cx(x1,x2,...) /\ cy(y1,y2,...))
            if (prod2.klabel().isEmpty() || noConfusion.contains(Tuple2.apply(prod, prod2)) || prod.equals(prod2)
                    || !isConstructor(prod2, functionRulesMap) || isBuiltinProduction(prod2)) {
                // TODO (traiansf): add no confusion axioms for constructor vs inj.
                continue;
            }
            noConfusion.add(Tuple2.apply(prod, prod2));
            noConfusion.add(Tuple2.apply(prod2, prod));
            sb.append("  axiom");
            convertParams(prod.klabel(), false, sb);
            sb.append("\\not{");
            convert(prod.sort(), prod, sb);
            sb.append("} (\\and{");
            convert(prod.sort(), prod, sb);
            sb.append("} (");
            applyPattern(prod, "X", sb);
            sb.append(", ");
            applyPattern(prod2, "Y", sb);
            sb.append(")) [constructor{}()] // no confusion different constructors\n");
        }
    }

    public static void convert(KLabel klabel, StringBuilder sb) {
        convert(klabel, java.util.Collections.emptySet(), sb);
    }

    private void convert(KLabel klabel, Seq<Sort> params, StringBuilder sb) {
        convert(klabel, mutable(params), sb);
    }

    private static void convert(KLabel klabel, Collection<Sort> params, StringBuilder sb) {
        if (klabel.name().equals(KLabels.INJ)) {
            sb.append(klabel.name());
        } else if (ConstructorChecks.isBuiltinLabel(klabel)) {
            sb.append(convertBuiltinLabel(klabel.name()));
        } else {
            sb.append("Lbl");
            convert(klabel.name(), sb);
        }
        sb.append("{");
        String conn = "";
        for (Sort param : iterable(klabel.params())) {
            sb.append(conn);
            convert(param, params, sb);
            conn = ", ";
        }
        sb.append("}");
    }

    private static String convertBuiltinLabel(String klabel) {
        switch (klabel) {
            case "#Bottom":
                return "\\bottom";
            case "#Top":
                return "\\top";
            case "#Or":
                return "\\or";
            case "#And":
                return "\\and";
            case "#Not":
                return "\\not";
            case "#Floor":
                return "\\floor";
            case "#Ceil":
                return "\\ceil";
            case "#Equals":
                return "\\equals";
            case "#Implies":
                return "\\implies";
            case "#Exists":
                return "\\exists";
            case "#Forall":
                return "\\forall";
            case "#AG":
                return "allPathGlobally";
            case "weakExistsFinally":
                return ONE_PATH_OP;
            case "weakAlwaysFinally":
                return ALL_PATH_OP;
            default:
                throw KEMException.compilerError("Unsuppored kore connective in rule: " + klabel);
        }
    }

    private void convert(KLabel klabel, Production prod, StringBuilder sb) {
        if (klabel.name().equals(KLabels.INJ)) {
            sb.append(klabel.name());
        } else {
            sb.append("Lbl");
            convert(klabel.name(), sb);
        }
        sb.append("{");
        String conn = "";
        for (Sort param : iterable(klabel.params())) {
            sb.append(conn);
            convert(param, prod, sb);
            conn = ", ";
        }
        sb.append("}");
    }

    private void convert(Sort sort, Production prod, StringBuilder sb) {
        convert(sort, prod.params(), sb);
    }

    public static void convert(Sort sort, StringBuilder sb) {
        convert(sort, java.util.Collections.emptySet(), sb);
    }

    private void convert(SortHead sort, StringBuilder sb) {
        List<Sort> params = new ArrayList<>();
        for (int i = 0; i < sort.params(); i++) {
            params.add(Sort("S" + i));
        }
        convert(Sort(sort.name(), immutable(params)), params, sb);
    }

    private void convert(Sort sort, Seq<Sort> params, StringBuilder sb) {
        convert(sort, mutable(params), sb);
    }

    private static void convert(Sort sort, Collection<Sort> params, StringBuilder sb) {
        if (sort.name().equals(AddSortInjections.SORTPARAM_NAME)) {
            String sortVar = sort.params().headOption().get().name();
            sb.append(sortVar);
            return;
        }
        sb.append("Sort");
        convert(sort.name(), sb);
        if (!params.contains(sort)) {
            sb.append("{");
            String conn = "";
            for (Sort param : iterable(sort.params())) {
                sb.append(conn);
                convert(param, params, sb);
                conn = ", ";
            }
            sb.append("}");
        }
    }

    private void convert(Map<Att.Key, Boolean> attributes, Att att, StringBuilder sb,
            Map<String, KVariable> freeVarsMap, HasLocation location) {
        sb.append("[");
        String conn = "";

        // Emit user groups as group(_) to prevent conflicts between user groups and
        // internals
        att = att.withUserGroupsAsGroupAtt();

        for (Tuple2<Tuple2<Att.Key, String>, ?> attribute :
        // Sort to stabilize error messages
        stream(att.att()).sorted(Comparator.comparing(Tuple2::toString)).collect(Collectors.toList())) {
            Att.Key key = attribute._1._1;
            String strKey = key.key();
            String clsName = attribute._1._2;
            Object val = attribute._2;
            String strVal = val.toString();
            sb.append(conn);
            if (clsName.equals(K.class.getName())) {
                convert(strKey, sb);
                sb.append("{}(");
                convert((K) val, sb);
                sb.append(")");
            } else if (clsName.equals(KList.class.getName())) {
                convert(strKey, sb);
                sb.append("{}(");
                String conn2 = "";
                for (K item : ((KList) val).items()) {
                    sb.append(conn2);
                    convert(item, sb);
                    conn2 = ",";
                }
                sb.append(")");
            } else if (attributes.get(key) != null && attributes.get(key)) {
                convert(strKey, sb);
                sb.append("{}(");
                if (isListOfVarsAttribute(key)) {
                    convertStringVarList(location, freeVarsMap, strVal, sb);
                } else {
                    switch (strKey) {
                        case "unit":
                        case "element":
                            Production prod = production(KApply(KLabel(strVal)));
                            convert(prod.klabel().get(), prod.params(), sb);
                            sb.append("()");
                            break;
                        default:
                            sb.append(StringUtil.enquoteKString(strVal));
                    }
                }
                sb.append(")");
            } else {
                convert(strKey, sb);
                sb.append("{}()");
            }
            conn = ", ";
        }
        sb.append("]");
    }

    private static void convert(String name, StringBuilder sb) {
        switch (name) {
            case "module":
            case "endmodule":
            case "sort":
            case "hooked-sort":
            case "symbol":
            case "hooked-symbol":
            case "alias":
            case "axiom":
                sb.append(name).append("'Kywd'");
                return;
            default:
                break;
        }
        StringBuilder buffer = new StringBuilder();
        StringUtil.encodeStringToAlphanumeric(buffer, name, asciiReadableEncodingKore, identChar, "'");
        sb.append(buffer);
    }

    private boolean isListOfVarsAttribute(Att.Key name) {
        return name.equals(Att.CONCRETE()) || name.equals(Att.SYMBOLIC());
    }

    private void convertStringVarList(HasLocation location, Map<String, KVariable> freeVarsMap, String strVal,
            StringBuilder sb) {
        if (strVal.trim().isEmpty())
            return;
        Collection<KVariable> variables = Arrays.stream(strVal.split(",")).map(String::trim)
                .map(s -> {
                    if (freeVarsMap.containsKey(s))
                        return freeVarsMap.get(s);
                    else
                        throw KEMException.criticalError("No free variable found for " + s, location);
                }).collect(Collectors.toList());
        String conn = "";
        for (KVariable var : variables) {
            sb.append(conn);
            convert((K) var, sb);
            conn = ",";
        }
    }

    private static final Production INJ_PROD = Constructors.Production(KLabel(KLabels.INJ, Sort("S1"), Sort("S2")),
            Sort("S2"), Seq(Constructors.NonTerminal(Sort("S1"))), Att());

    private Production production(KApply term) {
        return production(term, false);
    }

    private Production production(KApply term, boolean instantiatePolySorts) {
        KLabel klabel = term.klabel();
        if (klabel.name().equals(KLabels.INJ))
            return instantiatePolySorts ? INJ_PROD.substitute(term.klabel().params()) : INJ_PROD;
        Option<scala.collection.Set<Production>> prods = module.productionsFor().get(klabel.head());
        if (!(prods.nonEmpty() && prods.get().size() == 1))
            throw KEMException.compilerError("Expected to find exactly one production for KLabel: " + klabel
                    + " found: " + prods.getOrElse(Collections::Set).size());
        return instantiatePolySorts ? prods.get().head().substitute(term.klabel().params()) : prods.get().head();
    }

    private KLabel computePolyKLabel(KApply k) {
        String labelName = k.klabel().name();
        if (mlBinders.contains(labelName)) { // ML binders are not parametric in the variable so we remove it
            List<Sort> params = mutable(k.klabel().params());
            if (!params.isEmpty()) {
                params.remove(0);
            }
            return KLabel(labelName, immutable(params));
        } else {
            return k.klabel();
        }
    }

    public java.util.Set<K> collectAnonymousVariables(K k) {
        java.util.Set<K> anonymousVariables = new HashSet<>();
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (mlBinders.contains(k.klabel().name()) && k.items().get(0).att().contains(Att.ANONYMOUS())) {
                    throw KEMException.internalError("Nested quantifier over anonymous variables.");
                }
                for (K item : k.items()) {
                    apply(item);
                }
            }

            @Override
            public void apply(KVariable k) {
                if (k.att().contains(Att.ANONYMOUS())) {
                    anonymousVariables.add(k);
                }
            }

        }.apply(k);
        return anonymousVariables;
    }

    public void convert(K k, StringBuilder sb) {
        new VisitK() {
            @Override
            public void apply(KApply k) {
                KLabel label = computePolyKLabel(k);
                String conn = "";
                if (mlBinders.contains(k.klabel().name()) && k.items().get(0).att().contains(Att.ANONYMOUS())) {
                    // Handle #Forall _ / #Exists _
                    java.util.Set<K> anonymousVariables = collectAnonymousVariables(k.items().get(1));

                    // Quantify over all anonymous variables.
                    for (K variable : anonymousVariables) {
                        sb.append(conn);
                        convert(label, sb);
                        sb.append("(");
                        apply(variable);
                        conn = ",";
                    }

                    // We assume that mlBinder only has two children.
                    sb.append(conn);
                    apply(k.items().get(1));

                    for (int i = 0; i < anonymousVariables.size(); i++) {
                        sb.append(")");
                    }
                } else {
                    convert(label, sb);
                    sb.append("(");
                    for (K item : k.items()) {
                        sb.append(conn);
                        apply(item);
                        conn = ",";
                    }
                    sb.append(")");
                }
            }

            @Override
            public void apply(KToken k) {
                sb.append("\\dv{");
                convert(k.sort(), sb);
                sb.append("}(");
                if (module.sortAttributesFor().get(k.sort().head()).getOrElse(Att::empty).getOptional(Att.HOOK())
                        .orElse("").equals("STRING.String")) {
                    sb.append(StringUtil.escapeNonASCII(k.s()));
                } else if (module.sortAttributesFor().get(k.sort().head()).getOrElse(Att::empty).getOptional(Att.HOOK())
                        .orElse("").equals("BYTES.Bytes")) {
                    sb.append(StringUtil.escapeNonASCII(k.s().substring(1))); // remove the leading `b`
                } else {
                    sb.append(StringUtil.enquoteKString(k.s()));
                }
                sb.append(")");
            }

            @Override
            public void apply(KSequence k) {
                for (int i = 0; i < k.items().size(); i++) {
                    K item = k.items().get(i);
                    boolean isList = item.att().get(Sort.class).equals(Sorts.K());
                    if (i == k.items().size() - 1) {
                        if (isList) {
                            apply(item);
                        } else {
                            sb.append("kseq{}(");
                            apply(item);
                            sb.append(",dotk{}())");
                        }
                    } else {
                        if (item.att().get(Sort.class).equals(Sorts.K())) {
                            sb.append("append{}(");
                        } else {
                            sb.append("kseq{}(");
                        }
                        apply(item);
                        sb.append(",");
                    }
                }
                if (k.items().size() == 0) {
                    sb.append("dotk{}()");
                }
                for (int i = 0; i < k.items().size() - 1; i++) {
                    sb.append(")");
                }
            }

            @Override
            public void apply(KVariable k) {
                boolean setVar = k.name().startsWith("@");
                if (setVar) {
                    sb.append('@');
                }
                sb.append("Var");
                String name = setVar ? k.name().substring(1) : k.name();
                convert(name, sb);
                sb.append(":");
                convert(k.att().getOptional(Sort.class).orElse(Sorts.K()), sb);
            }

            @Override
            public void apply(KRewrite k) {
                sb.append("\\rewrites{");
                convert(k.att().get(Sort.class), sb);
                sb.append("}(");
                apply(k.left());
                sb.append(",");
                apply(k.right());
                sb.append(")");
            }

            @Override
            public void apply(KAs k) {
                Sort sort = k.att().get(Sort.class);
                sb.append("\\and{");
                convert(sort, sb);
                sb.append("}(");
                apply(k.pattern());
                sb.append(",");
                apply(k.alias());
                sb.append(")");
            }

            @Override
            public void apply(InjectedKLabel k) {
                throw KEMException.internalError("Cannot yet translate #klabel to kore", k);
            }
        }.apply(k);
    }
}
