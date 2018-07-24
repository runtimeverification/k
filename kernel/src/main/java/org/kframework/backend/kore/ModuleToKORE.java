// Copyright (c) 2018 K Team. All Rights Reserved.
package org.kframework.backend.kore;

import com.google.common.collect.BiMap;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;
import com.sun.org.apache.xpath.internal.operations.Bool;
import edu.uci.ics.jung.graph.DirectedGraph;
import edu.uci.ics.jung.graph.DirectedSparseGraph;
import org.kframework.attributes.Att;
import org.kframework.builtin.BooleanUtils;
import org.kframework.builtin.KLabels;
import org.kframework.builtin.Sorts;
import org.kframework.compile.ConfigurationInfoFromModule;
import org.kframework.compile.RewriteToTop;
import org.kframework.definition.Module;
import org.kframework.definition.NonTerminal;
import org.kframework.definition.Production;
import org.kframework.definition.ProductionItem;
import org.kframework.definition.Rule;
import org.kframework.kil.Attribute;
import org.kframework.kore.FoldK;
import org.kframework.kore.InjectedKLabel;
import org.kframework.kore.K;
import org.kframework.kore.KApply;
import org.kframework.kore.KAs;
import org.kframework.kore.KLabel;
import org.kframework.kore.KORE;
import org.kframework.kore.KRewrite;
import org.kframework.kore.KSequence;
import org.kframework.kore.KToken;
import org.kframework.kore.KVariable;
import org.kframework.kore.Sort;
import org.kframework.kore.VisitK;
import org.kframework.parser.concrete2kore.generator.RuleGrammarGenerator;
import org.kframework.utils.StringUtil;
import org.kframework.utils.errorsystem.KEMException;
import org.kframework.utils.file.FileUtil;
import scala.Tuple2;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.kframework.definition.Constructors.*;
import static org.kframework.Collections.*;
import static org.kframework.kore.KORE.*;

public class ModuleToKORE {
    private final Module module;
    private final FileUtil files;
    private final StringBuilder sb = new StringBuilder();
    private final Set<String> impureFunctions = new HashSet<>();
    private final Map<String, List<Set<Integer>>> polyKLabels = new HashMap<>();

    public ModuleToKORE(Module module, FileUtil files) {
        this.module = module;
        this.files = files;
    }
    private static final boolean ATTRIBUTES = false;
    private static final boolean METAVAR = false;

    public String convert() {
        ConfigurationInfoFromModule configInfo = new ConfigurationInfoFromModule(module);
        Sort topCell = configInfo.getRootCell();
        String prelude = files.loadFromKBase("include/kore/prelude.kore");
        sb.append("[]\n\n");
        sb.append(prelude);
        Map<String, Boolean> attributes = new HashMap<>();
        sb.append("\n");
        if (ATTRIBUTES) {
            sb.append("module ATTRIBUTES\n\n  sort Attribute{} []\n");
            for (Sort sort : iterable(module.definedSorts())) {
                Att att = module.sortAttributesFor().get(sort).getOrElse(() -> KORE.Att());
                collectAttributes(attributes, att);
            }
            for (Production prod : iterable(module.productions())) {
                Att att = prod.att();
                collectAttributes(attributes, att);
            }
            for (Rule r : iterable(module.rules())) {
                Att att = r.att();
                collectAttributes(attributes, att);
            }
            for (Map.Entry<String, Boolean> entry : attributes.entrySet()) {
                if (entry.getValue()) {
                    sb.append("  sort Att");
                    convert(entry.getKey());
                    sb.append("{} []\n");
                    sb.append("  symbol ");
                    convert(entry.getKey());
                    sb.append("{}(Att");
                    convert(entry.getKey());
                    sb.append("{}):Attribute{}[]\n");
                } else {
                    sb.append("  symbol ");
                    convert(entry.getKey());
                    sb.append("{}():Attribute{}[]\n");
                }
            }
            sb.append("endmodule []\n\n");
        }
        sb.append("module ");
        convert(module.name());
        sb.append("\n\n// imports\n");
        if (ATTRIBUTES) {
            sb.append("  import ATTRIBUTES []\n");
        }
        sb.append("  import K []\n\n// sorts\n");
        Set<String> dummyHookedSorts = new HashSet<>();
        dummyHookedSorts.add("SET.Set");
        dummyHookedSorts.add("MAP.Map");
        dummyHookedSorts.add("LIST.List");
        for (Sort sort : iterable(module.definedSorts())) {
            if (sort.equals(Sorts.K()) || sort.equals(Sorts.KItem())) {
                continue;
            }
            sb.append("  ");
            Att att = module.sortAttributesFor().get(sort).getOrElse(() -> KORE.Att());
            if (att.contains(Attribute.HOOK_KEY) && !dummyHookedSorts.contains(att.get(Attribute.HOOK_KEY))) {
                sb.append("hooked-");
            }
            sb.append("sort ");
            convert(sort, false);
            sb.append(" ");
            convert(attributes, att);
            sb.append("\n");
        }

        SetMultimap<KLabel, Rule> functionRules = HashMultimap.create();
        for (Rule rule : iterable(module.rules())) {
            K left = RewriteToTop.toLeft(rule.body());
            if (left instanceof KApply) {
                KApply kapp = (KApply) left;
                Production prod = production(kapp);
                if (prod.att().contains(Attribute.FUNCTION_KEY)) {
                    functionRules.put(kapp.klabel(), rule);
                }
            }
        }
        computeDependencies(functionRules);
        Set<KLabel> impurities = functionRules.keySet().stream().filter(lbl -> module.attributesFor().apply(lbl).contains(Attribute.IMPURE_KEY)).collect(Collectors.toSet());
        impurities.addAll(ancestors(impurities, dependencies));

        sb.append("\n// symbols\n");
        for (Production prod : iterable(module.productions())) {
            prod = computePolyProd(prod);
            if (prod.klabel().isEmpty()) {
                continue;
            }
            if (impurities.contains(prod.klabel().get())) {
                impureFunctions.add(prod.klabel().get().name());
            }
            sb.append("  ");
            if (isFunction(prod) && prod.att().contains(Attribute.HOOK_KEY)) {
                sb.append("hooked-");
            }
            sb.append("symbol ");
            convert(prod.klabel().get(), true);
            String conn;
            sb.append("(");
            conn = "";
            for (NonTerminal nt : iterable(prod.nonterminals())) {
                Sort sort = nt.sort();
                sb.append(conn);
                convert(sort, prod);
                conn = ", ";
            }
            sb.append(") : ");
            convert(prod.sort(), prod);
            sb.append(" ");
            convert(attributes, addKoreAttributes(prod, functionRules, impurities));
            sb.append("\n");
        }
        sb.append("\n// generated axioms\n");
        Set<Tuple2<Production, Production>> noConfusion = new HashSet<>();
        for (Production prod : iterable(module.productions())) {
            prod = computePolyProd(prod);
            if (prod.klabel().isEmpty()) {
                continue;
            }
            if (prod.att().contains(Attribute.ASSOCIATIVE_KEY)) {
                // s(s(K1,K2),K3) = s(K1,s(K2,K3))
                if (prod.arity() != 2) {
                    throw KEMException.compilerError("Found a non-binary production with the assoc attribute", prod);
                }
                if (!(prod.sort().equals(prod.nonterminal(0).sort()) && prod.sort().equals(prod.nonterminal(1).sort()))) {
                    throw KEMException.compilerError("Found an associative production with ill formed sorts", prod);
                }
                sb.append("  axiom");
                convertParams(prod.klabel().get(), true);
                sb.append(" \\equals{");
                convert(prod.sort(), prod);
                sb.append(", R} (");
                convert(prod.klabel().get(), prod);
                sb.append("(");
                convert(prod.klabel().get(), prod);
                sb.append("(K1:");
                convert(prod.sort(), prod);
                sb.append(",K2:");
                convert(prod.sort(), prod);
                sb.append("),K3:");
                convert(prod.sort(), prod);
                sb.append("),");
                convert(prod.klabel().get(), prod);
                sb.append("(K1:");
                convert(prod.sort(), prod);
                sb.append(",");
                convert(prod.klabel().get(), prod);
                sb.append("(K2:");
                convert(prod.sort(), prod);
                sb.append(",K3:");
                convert(prod.sort(), prod);
                sb.append("))) [] // associativity\n");
            }
            if (prod.att().contains(Attribute.COMMUTATIVE_KEY)) {
                // s(K1, K2) = s(K2, K1)
                if (prod.arity() != 2) {
                    throw KEMException.compilerError("Found a non-binary production with the comm attribute", prod);
                }
                if (!(prod.nonterminal(0).sort().equals(prod.nonterminal(1).sort()))) {
                    throw KEMException.compilerError("Found a commutative production with ill formed sorts", prod);
                }
                Sort childSort = prod.nonterminal(0).sort();
                sb.append("  axiom");
                convertParams(prod.klabel().get(), true);
                sb.append(" \\equals{");
                convert(prod.sort(), prod);
                sb.append(", R} (");
                convert(prod.klabel().get(), prod);
                sb.append("(K1:");
                convert(childSort, prod);
                sb.append(",K2:");
                convert(childSort, prod);
                sb.append("),");
                convert(prod.klabel().get(), prod);
                sb.append("(K2:");
                convert(childSort, prod);
                sb.append(",K1:");
                convert(childSort, prod);
                sb.append(")) [] // commutativity\n");
            }
            if (prod.att().contains(Attribute.IDEMPOTENT_KEY)) {
                // s(K, K) = K
                if (prod.arity() != 2) {
                    throw KEMException.compilerError("Found a non-binary production with the assoc attribute", prod);
                }
                if (!(prod.sort().equals(prod.nonterminal(0).sort()) && prod.sort().equals(prod.nonterminal(1).sort()))) {
                    throw KEMException.compilerError("Found an associative production with ill formed sorts", prod);
                }
                sb.append("  axiom");
                convertParams(prod.klabel().get(), true);
                sb.append(" \\equals{");
                convert(prod.sort(), prod);
                sb.append(", R} (");
                convert(prod.klabel().get(), prod);
                sb.append("(K:");
                convert(prod.sort(), prod);
                sb.append(",K:");
                convert(prod.sort(), prod);
                sb.append("),K:");
                convert(prod.sort(), prod);
                sb.append(") [] // idempotency\n");
            }
            if (isFunction(prod) && prod.att().contains(Attribute.UNIT_KEY)) {
                // s(K, unit) = K
                // s(unit, K) = K
                if (prod.arity() != 2) {
                    throw KEMException.compilerError("Found a non-binary production with the assoc attribute", prod);
                }
                if (!(prod.sort().equals(prod.nonterminal(0).sort()) && prod.sort().equals(prod.nonterminal(1).sort()))) {
                    throw KEMException.compilerError("Found an associative production with ill formed sorts", prod);
                }
                KLabel unit = KLabel(prod.att().get(Attribute.UNIT_KEY));
                sb.append("  axiom");
                convertParams(prod.klabel().get(), true);
                sb.append("\\equals{");
                convert(prod.sort(), prod);
                sb.append(", R} (");
                convert(prod.klabel().get(), prod);
                sb.append("(K:");
                convert(prod.sort(), prod);
                sb.append(",");
                convert(unit, false);
                sb.append("()),K:");
                convert(prod.sort(), prod);
                sb.append(") [] // right unit\n");

                sb.append("  axiom");
                convertParams(prod.klabel().get(), true);
                sb.append("\\equals{");
                convert(prod.sort(), prod);
                sb.append(", R} (");
                convert(prod.klabel().get(), prod);
                sb.append("(");
                convert(unit, false);
                sb.append("(),K:");
                convert(prod.sort(), prod);
                sb.append("),K:");
                convert(prod.sort(), prod);
                sb.append(") [] // left unit\n");
            }
            if (isFunctional(prod, functionRules, impurities)) {
                // exists y . f(...) = y
                sb.append("  axiom");
                convertParams(prod.klabel().get(), true);
                sb.append(" \\exists{R} (Val:");
                convert(prod.sort(), prod);
                sb.append(", \\equals{");
                convert(prod.sort(), prod);
                sb.append(", R} (");
                sb.append("Val:");
                convert(prod.sort(), prod);
                sb.append(", ");
                convert(prod.klabel().get(), prod);
                sb.append("(");
                String conn = "";
                for (int i = 0; i < prod.arity(); i++) {
                    sb.append(conn);
                    sb.append("K").append(i).append(":");
                    convert(prod.nonterminal(i).sort(), prod);
                    conn = ", ";
                }
                sb.append("))) [] // functional\n");
            }
            if (isConstructor(prod, functionRules, impurities)) {
                // c(x1,x2,...) /\ c(y1,y2,...) -> c(x1/\y2,x2/\y2,...)
                if (prod.arity() > 0) {
                    sb.append("  axiom");
                    convertParams(prod.klabel().get(), false);
                    sb.append("\\implies{");
                    convert(prod.sort(), prod);
                    sb.append("} (\\and{");
                    convert(prod.sort(), prod);
                    sb.append("} (");
                    convert(prod.klabel().get(), prod);
                    sb.append("(");
                    String conn = "";
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append(conn);
                        sb.append("X").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        conn = ", ";
                    }
                    sb.append("), ");
                    convert(prod.klabel().get(), prod);
                    sb.append("(");
                    conn = "";
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append(conn);
                        sb.append("Y").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        conn = ", ";
                    }
                    sb.append(")), ");
                    convert(prod.klabel().get(), prod);
                    sb.append("(");
                    conn = "";
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append(conn);
                        sb.append("\\and{");
                        convert(prod.nonterminal(i).sort(), prod);
                        sb.append("} (X").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        sb.append(", Y").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        sb.append(")");
                        conn = ", ";
                    }
                    sb.append(")) [] // no confusion same constructor\n");
                }
                for (Production prod2 : iterable(module.productionsForSort().apply(prod.sort()))) {
                    // !(cx(x1,x2,...) /\ cy(y1,y2,...))
                    prod2 = computePolyProd(prod2);
                    if (prod2.klabel().isEmpty() || noConfusion.contains(Tuple2.apply(prod, prod2)) || prod.equals(prod2) || !isConstructor(prod2, functionRules, impurities)) {
                        continue;
                    }
                    noConfusion.add(Tuple2.apply(prod, prod2));
                    noConfusion.add(Tuple2.apply(prod2, prod));
                    sb.append("  axiom");
                    convertParams(prod.klabel().get(), false);
                    sb.append("\\not{");
                    convert(prod.sort(), prod);
                    sb.append("} (\\and{");
                    convert(prod.sort(), prod);
                    sb.append("} (");
                    convert(prod.klabel().get(), prod);
                    sb.append("(");
                    String conn = "";
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append(conn);
                        sb.append("X").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        conn = ", ";
                    }
                    sb.append("), ");
                    convert(prod2.klabel().get(), prod);
                    sb.append("(");
                    conn = "";
                    for (int i = 0; i < prod2.arity(); i++) {
                        sb.append(conn);
                        sb.append("Y").append(i).append(":");
                        convert(prod2.nonterminal(i).sort(), prod2);
                        conn = ", ";
                    }
                    sb.append("))) [] // no confusion different constructors\n");

                }
            }
        }
        for (Sort sort : iterable(module.definedSorts())) {
            sb.append("  axiom{} ");
            boolean hasToken = false;
            int numTerms = 0;
            for (Production prod : iterable(mutable(module.productionsForSort()).getOrDefault(sort, Set()))) {
                prod = computePolyProd(prod);
                if (isFunction(prod)) {
                    continue;
                }
                if (prod.klabel().isEmpty() && !((prod.att().contains("token") && !hasToken) || prod.isSubsort())) {
                    continue;
                }
                numTerms++;
                sb.append("\\or{");
                convert(sort, false);
                sb.append("} (");
                if (prod.att().contains("token") && !hasToken) {
                    convertTokenProd(sort);
                    hasToken = true;
                } else if (prod.isSubsort()) {
                    sb.append("\\exists{");
                    convert(sort, false);
                    sb.append("} (Val:");
                    convert(prod.nonterminal(0).sort(), prod);
                    sb.append(", inj{");
                    convert(prod.nonterminal(0).sort(), prod);
                    sb.append(", ");
                    convert(sort, false);
                    sb.append("} (Val:");
                    convert(prod.nonterminal(0).sort(), prod);
                    sb.append("))");
                } else if (prod.klabel().isDefined()) {
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append("\\exists{");
                        convert(sort, false);
                        sb.append("} (X").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        sb.append(", ");
                    }
                    convert(prod.klabel().get(), prod);
                    sb.append("(");
                    String conn = "";
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append(conn).append("X").append(i).append(":");
                        convert(prod.nonterminal(i).sort(), prod);
                        conn = ", ";
                    }
                    sb.append(")");
                    for (int i = 0; i < prod.arity(); i++) {
                        sb.append(")");
                    }
                }
                sb.append(", ");
            }
            Att sortAtt = module.sortAttributesFor().get(sort).getOrElse(() -> KORE.Att());
            if (!hasToken && sortAtt.contains("token")) {
                numTerms++;
                sb.append("\\or{");
                convert(sort, false);
                sb.append("} (");
                convertTokenProd(sort);
                sb.append(", ");
                hasToken = true;
            }
            sb.append("\\bottom{");
            convert(sort, false);
            sb.append("}()");
            for (int i = 0; i < numTerms; i++) {
                sb.append(")");
            }
            sb.append(" [] // no junk");
            if (hasToken && !METAVAR) {
                sb.append(" (TODO: fix bug with \\dv)");
            }
            sb.append("\n");
        }
        sb.append("\n// rules\n");
        for (Rule rule : iterable(module.rules())) {
            boolean function = false;
            Sort functionSort = null;
            KLabel functionLabel = null;
            K left = RewriteToTop.toLeft(rule.body());
            if (left instanceof KApply) {
                Production prod = production((KApply)left);
                if (isFunction(prod)) {
                    prod = prod.att().get("originalPrd", Production.class);
                    function = true;
                    functionSort = prod.sort();
                    functionLabel = prod.klabel().get();
                }
            }
            sb.append("// ");
            sb.append(rule.toString());
            sb.append("\n");
            if (function) {
                if (rule.att().contains("owise")) {
                    sb.append("  axiom{R} ");
                    sb.append("\\implies{R} (\n    \\and{R} (\n      \\not{R} (\n        ");
                    for (Rule notMatching : functionRules.get(functionLabel)) {
                        if (notMatching.att().contains("owise")) {
                            continue;
                        }
                        sb.append("\\or{R} (\n          \\ceil{");
                        convert(functionSort, false);
                        sb.append(",R} (\n            ");
                        Set<KVariable> vars = vars(notMatching);
                        for (KVariable var : vars) {
                            sb.append("\\exists{");
                            convert(functionSort, false);
                            sb.append("} (");
                            convert(var);
                            sb.append(", \n              ");
                        }
                        sb.append("\\and{");
                        convert(functionSort, false);
                        sb.append("} (\n                ");
                        convertSideCondition(notMatching.requires(), functionSort);
                        sb.append(",\n                ");
                        convert(RewriteToTop.toLeft(notMatching.body()));
                        sb.append(")");
                        for (KVariable ignored : vars) {
                            sb.append(")");
                        }
                        sb.append("),\n        ");
                    }
                    sb.append("\\bottom{R}()");
                    for (Rule notMatching : functionRules.get(functionLabel)) {
                        if (notMatching.att().contains("owise")) {
                            continue;
                        }
                        sb.append(")");
                    }
                    sb.append("),\n      ");
                    convertSideCondition(rule.requires());
                    sb.append("),\n    \\and{R} (\n      \\equals{");
                    convert(functionSort, false);
                    sb.append(",R} (\n        ");
                    K right = RewriteToTop.toRight(rule.body());
                    convert(left);
                    sb.append(",\n        ");
                    convert(right);
                    sb.append("),\n      ");
                    convertSideCondition(rule.ensures());
                    sb.append("))\n  ");
                    convert(attributes, rule.att());
                    sb.append("\n\n");
                } else {
                    sb.append("  axiom{R} ");
                    sb.append("\\implies{R} (\n    ");
                    convertSideCondition(rule.requires());
                    sb.append(",\n    \\and{R} (\n      \\equals{");
                    convert(functionSort, false);
                    sb.append(",R} (\n        ");
                    K right = RewriteToTop.toRight(rule.body());
                    convert(left);
                    sb.append(",\n        ");
                    convert(right);
                    sb.append("),\n      ");
                    convertSideCondition(rule.ensures());
                    sb.append("))\n  ");
                    convert(attributes, rule.att());
                    sb.append("\n\n");
                }
            } else if (!rule.att().contains(Attribute.MACRO_KEY) && !rule.att().contains(Attribute.ALIAS_KEY) && !rule.att().contains(Attribute.ANYWHERE_KEY)) {
                sb.append("  axiom{} \\and{");
                convert(topCell, false);
                sb.append("} (\n    ");
                convertSideCondition(rule.requires(), topCell);
                sb.append(", \\and{");
                convert(topCell, false);
                sb.append("} (\n    ");
                convertSideCondition(rule.ensures(), topCell);
                sb.append(", ");
                convert(rule.body());
                sb.append("))\n  ");
                convert(attributes, rule.att());
                sb.append("\n\n");
            }
        }
        sb.append("endmodule ");
        convert(attributes, module.att());
        sb.append("\n");
        return sb.toString();
    }

    private void convertTokenProd(Sort sort) {
        if (METAVAR) {
            sb.append("\\exists{");
            convert(sort, false);
            sb.append("} (#Str:#String{}, \\dv{");
            convert(sort, false);
            sb.append("}(#Str:#String{}))");
        } else {
            sb.append("\\top{");
            convert(sort, false);
            sb.append("}()");
        }
    }

    private void convertParams(KLabel kLabel, boolean hasR) {
        sb.append("{");
        String conn = "";
        if (hasR) {
            sb.append("R");
            conn = ", ";
        }
        for (Sort param : iterable(kLabel.params())) {
            sb.append(conn);
            convert(param, true);
            conn = ", ";
        }
        sb.append("}");
    }

    private static <V> Set<V> ancestors(
            Collection<? extends V> startNodes, DirectedGraph<V, ?> graph)
    {
        Queue<V> queue = new LinkedList<V>();
        queue.addAll(startNodes);
        Set<V> visited = new LinkedHashSet<V>(startNodes);
        while(!queue.isEmpty())
        {
            V v = queue.poll();
            Collection<V> neighbors = graph.getPredecessors(v);
            for (V n : neighbors)
            {
                if (!visited.contains(n))
                {
                    queue.offer(n);
                    visited.add(n);
                }
            }
        }
        return visited;
    }

    private void computeDependencies(SetMultimap<KLabel, Rule> functionRules) {
        dependencies = new DirectedSparseGraph<>();

        Set<KLabel> anywhereKLabels = new HashSet<>();
        stream(module.rules()).filter(r -> !r.att().contains(Attribute.MACRO_KEY) && !r.att().contains(Attribute.ALIAS_KEY)).forEach(r -> {
            K left = RewriteToTop.toLeft(r.body());
            if (left instanceof KApply) {
                KApply kapp = (KApply) left;
                if (r.att().contains(Attribute.ANYWHERE_KEY)) {
                    if (kapp.klabel().name().equals(KLabels.INJ)) {
                        K k = kapp.items().get(0);
                        if (k instanceof KApply) {
                            anywhereKLabels.add(((KApply)k).klabel());
                        }
                    } else {
                        anywhereKLabels.add(kapp.klabel());
                    }
                }
            }
        });

        class GetPredecessors extends VisitK {
            private final KLabel current;

            private GetPredecessors(KLabel current) {
                this.current = current;
            }

            @Override
            public void apply(KApply k) {
                if (k.klabel().name().equals(KLabels.INJ)) {
                    super.apply(k);
                    return;
                }
                Production prod = production(k);
                if (isFunction(prod) || anywhereKLabels.contains(k.klabel())) {
                    dependencies.addEdge(new Object(), current, k.klabel());
                }
                if (k.klabel() instanceof KVariable) {
                    // this function requires a call to eval, so we need to add the dummy dependency
                    dependencies.addEdge(new Object(), current, KLabel(""));
                }
                super.apply(k);
            }
        }

        for (Map.Entry<KLabel, Rule> entry : functionRules.entries()) {
            GetPredecessors visitor = new GetPredecessors(entry.getKey());
            visitor.apply(entry.getValue().body());
            visitor.apply(entry.getValue().requires());
        }

        for (KLabel label : Sets.union(functionRules.keySet(), anywhereKLabels)) {
            String hook = module.attributesFor().apply(label).<String>getOptional(Attribute.HOOK_KEY).orElse(".");

            if (hook.equals("KREFLECTION.fresh")) {
                for (KLabel freshFunction : iterable(module.freshFunctionFor().values())) {
                    dependencies.addEdge(new Object(), label, freshFunction);
                }
            }
            //eval depends on everything
            dependencies.addEdge(new Object(), KLabel(""), label);
        }
    }

    private DirectedGraph<KLabel, Object> dependencies;

    private boolean isConstructor(Production prod, SetMultimap<KLabel, Rule> functionRules, Set<KLabel> impurities) {
        Att att = addKoreAttributes(prod, functionRules, impurities);
        return att.contains("constructor");
    }

    private boolean isFunctional(Production prod, SetMultimap<KLabel, Rule> functionRules, Set<KLabel> impurities) {
        Att att = addKoreAttributes(prod, functionRules, impurities);
        return att.contains("functional");
    }

    private Att addKoreAttributes(Production prod, SetMultimap<KLabel, Rule> functionRules, Set<KLabel> impurities) {
        boolean isConstructor = !isFunction(prod);
        boolean isFunctional = !prod.att().contains(Attribute.IMPURE_KEY);
        if (prod.att().contains(Attribute.ASSOCIATIVE_KEY) ||
                prod.att().contains(Attribute.COMMUTATIVE_KEY) ||
                prod.att().contains(Attribute.IDEMPOTENT_KEY) ||
                (prod.att().contains(Attribute.FUNCTION_KEY) && prod.att().contains(Attribute.UNIT_KEY))) {
            isConstructor = false;
        }
        for (Rule r : functionRules.get(prod.klabel().get())) {
            if (r.att().contains(Attribute.ANYWHERE_KEY)) {
                isConstructor = false;
            }
            FoldK<Boolean> hasImpureFunction = new FoldK<Boolean>() {
                @Override
                public Boolean unit() {
                    return false;
                }

                @Override
                public Boolean merge(Boolean a, Boolean b) {
                    return a || b;
                }

                @Override
                public Boolean apply(KApply k) {
                    if (k.klabel().name().equals(KLabels.INJ)) {
                        return super.apply(k);
                    }
                    Production prod = production(k);
                    if (impurities.contains(prod.klabel().get())) {
                        return true;
                    }
                    return super.apply(k);
                }
            };
            if (hasImpureFunction.apply(r.body()) || hasImpureFunction.apply(r.requires()) || hasImpureFunction.apply(r.ensures())) {
                isFunctional = false;
            }
        }
        Att att = prod.att().remove("constructor").remove("functional");
        if (isConstructor) {
            att = att.add("constructor");
        }
        if (isFunctional) {
            att = att.add("functional");
        }
        return att;
    }

    private boolean isFunction(Production prod) {
        Production realProd = prod.att().get("originalPrd", Production.class);
        if (!realProd.att().contains(Attribute.FUNCTION_KEY)) {
            return false;
        }
        if (realProd.att().contains(Attribute.ASSOCIATIVE_KEY) || realProd.att().contains(Attribute.COMMUTATIVE_KEY) || realProd.att().contains(Attribute.IDEMPOTENT_KEY)) {
            return false;
        }
        if (stream(module.productionsForSort().apply(realProd.sort())).filter(p -> p.att().contains(Attribute.UNIT_KEY)).map(p -> p.att().get(Attribute.UNIT_KEY)).anyMatch(lbl -> lbl.equals(realProd.klabel().get().name()))) {
            return false;
        }
        return true;
    }

    private Set<KVariable> vars(Rule rule) {
        Set<KVariable> res = new HashSet<>();
        VisitK visitor = new VisitK() {
            @Override
            public void apply(KVariable k) {
                res.add(k);
            }
        };
        visitor.apply(rule.requires());
        visitor.apply(RewriteToTop.toLeft(rule.body()));
        return res;
    }

    private void convertSideCondition(K k) {
        if (k.equals(BooleanUtils.TRUE)) {
            sb.append("\\top{R}()");
        } else {
            sb.append("\\equals{SortBool{},R}(\n        ");
            convert(k);
            sb.append(",\n        \\dv{SortBool{}}(\"true\"))");
        }
    }

    private void convertSideCondition(K k, Sort result) {
        if (k.equals(BooleanUtils.TRUE)) {
            sb.append("\\top{");
            convert(result, false);
            sb.append("}()");
        } else {
            sb.append("\\equals{SortBool{},");
            convert(result, false);
            sb.append("}(\n        ");
            convert(k);
            sb.append(",\n        \\dv{SortBool{}}(\"true\"))");
        }
    }

    private Production computePolyProd(Production prod) {
        if (!prod.att().contains("poly"))
            return prod.withAtt(prod.att().add("originalPrd", Production.class, prod));
        List<Set<Integer>> poly = RuleGrammarGenerator.computePositions(prod);
        polyKLabels.put(prod.klabel().get().name(), poly);
        List<Sort> params = new ArrayList<>();
        List<NonTerminal> children = new ArrayList<>(mutable(prod.nonterminals()));
        Sort returnSort = prod.sort();
        for (int i = 0; i < poly.size(); i++) {
            Set<Integer> positions = poly.get(i);
            Sort sort = Sort("S" + i);
            params.add(sort);
            for (int j : positions) {
                if (j == 0) {
                    returnSort = sort;
                } else {
                    children.set(j - 1, NonTerminal(sort));
                }
            }
        }
        List<ProductionItem> items = new ArrayList<>();
        int i = 0;
        for (ProductionItem item : iterable(prod.items())) {
            if (item instanceof NonTerminal) {
                items.add(children.get(i));
                i++;
            } else {
                items.add(item);
            }
        }
        return Production(KLabel(prod.klabel().get().name(), immutable(params)), returnSort, immutable(items), prod.att().add("originalPrd", Production.class, prod));
    }

    private KLabel computePolyKLabel(KApply k) {
        List<Set<Integer>> poly = polyKLabels.get(k.klabel().name());
        List<Sort> params = new ArrayList<>();
        for (Set<Integer> positions : poly) {
            int pos = positions.iterator().next();
            Sort sort;
            if (pos == 0) {
                sort = k.att().get(Sort.class);
            } else {
                sort = k.items().get(pos-1).att().get(Sort.class);
            }
            params.add(sort);
        }
        return KLabel(k.klabel().name(), immutable(params));
    }


    private void collectAttributes(Map<String, Boolean> attributes, Att att) {
        for (Tuple2<Tuple2<String, Class<?>>, ?> attribute : iterable(att.att())) {
            String name = attribute._1._1;
            Class<?> cls = attribute._1._2;
            Object val = attribute._2;
            String strVal = val.toString();
            if (strVal.equals("")) {
                if (!attributes.containsKey(name)) {
                    attributes.put(name, false);
                }
            } else {
                attributes.put(name, true);
            }
        }
    }

    private static final Production INJ_PROD = Production(KLabel(KLabels.INJ, Sort("From"), Sort("To")), Sort("To"), Seq(NonTerminal(Sort("From"))));


    private Production production(KApply term) {
        if (term.klabel().name().equals(KLabels.INJ))
            return Production(INJ_PROD.klabel(), INJ_PROD.sort(), INJ_PROD.items(), Att.empty().add("originalPrd", Production.class, INJ_PROD));
        scala.collection.Set<Production> prods = module.productionsFor().apply(((KApply) term).klabel());
        assert(prods.size() == 1);
        return computePolyProd(prods.head());
    }

    private void convert(KLabel klabel, boolean var) {
        if (klabel.name().equals(KLabels.INJ)) {
            sb.append(klabel.name());
        } else {
            sb.append("Lbl");
            convert(klabel.name());
        }
        sb.append("{");
        String conn = "";
        for (Sort param : iterable(klabel.params())) {
            sb.append(conn);
            convert(param, var);
            conn = ", ";
        }
        sb.append("}");
    }

    private void convert(KLabel klabel, Production prod) {
        if (klabel.name().equals(KLabels.INJ)) {
            sb.append(klabel.name());
        } else {
            sb.append("Lbl");
            convert(klabel.name());
        }
        sb.append("{");
        String conn = "";
        for (Sort param : iterable(klabel.params())) {
            sb.append(conn);
            convert(param, prod);
            conn = ", ";
        }
        sb.append("}");
    }

    private void convert(Sort sort, Production prod) {
        convert(sort, prod.klabel().isDefined() && prod.klabel().get().params().contains(sort));
    }

    private void convert(Sort sort, boolean var) {
        sb.append("Sort");
        convert(sort.name());
        if (!var) {
            sb.append("{");
            String conn = "";
            for (Sort param : iterable(sort.params())) {
                sb.append(conn);
                convert(param.name());
                conn = ", ";
            }
            sb.append("}");
        }
    }

    private void convert(Map<String, Boolean> attributes, Att att) {
        sb.append("[");
        if (ATTRIBUTES) {
            String conn = "";
            for (Tuple2<Tuple2<String, Class<?>>, ?> attribute : iterable(att.att())) {
                String name = attribute._1._1;
                Class<?> cls = attribute._1._2;
                Object val = attribute._2;
                String strVal = val.toString();
                sb.append(conn);
                if (attributes.get(name) != null && attributes.get(name)) {
                    sb.append(name).append("{}(\\dv{Att");
                    convert(name);
                    sb.append("{}}(");
                    sb.append(StringUtil.enquoteCString(strVal));
                    sb.append("))");
                } else {
                    sb.append(name).append("{}()");
                }
                conn = ", ";
            }
        }
        sb.append("]");
    }

    private static final Pattern identChar = Pattern.compile("[A-Za-z0-9\\-]");

    private static String[] asciiReadableEncoding = new String[] {
            null,// 00
            null,// 01
            null,// 02
            null,// 03
            null,// 04
            null,// 05
            null,// 06
            null,// 07
            null,// 08
            null,// 09
            null,// 0a
            null,// 0b
            null,// 0c
            null,// 0d
            null,// 0e
            null,// 0f
            null,// 10
            null,// 11
            null,// 12
            null,// 13
            null,// 14
            null,// 15
            null,// 16
            null,// 17
            null,// 18
            null,// 19
            null,// 1a
            null,// 1b
            null,// 1c
            null,// 1d
            null,// 1e
            null,// 1f
            "Spce",// 20
            "Bang",// 21
            "Quot",// 22
            "Hash",// 23
            "Dolr",// 24
            "Perc",// 25
            "And",// 26
            "Apos",// 27
            "LPar",// 28
            "RPar",// 29
            "Star",// 2a
            "Plus",// 2b
            "Comm",// 2c
            "-",// 2d
            "Stop",// 2e
            "Slsh",// 2f
            "0",// 30
            "1",// 31
            "2",// 32
            "3",// 33
            "4",// 34
            "5",// 35
            "6",// 36
            "7",// 37
            "8",// 38
            "9",// 39
            "Coln",// 3a
            "SCln",// 3b
            "-LT-",// 3c
            "Eqls",// 3d
            "-GT-",// 3e
            "Ques",// 3f
            "-AT-",// 40
            "A",// 41
            "B",// 42
            "C",// 43
            "D",// 44
            "E",// 45
            "F",// 46
            "G",// 47
            "H",// 48
            "I",// 49
            "J",// 4a
            "K",// 4b
            "L",// 4c
            "M",// 4d
            "N",// 4e
            "O",// 4f
            "P",// 50
            "Q",// 51
            "R",// 52
            "S",// 53
            "T",// 54
            "U",// 55
            "V",// 56
            "W",// 57
            "X",// 58
            "Y",// 59
            "Z",// 5a
            "LSqB",// 5b
            "Bash",// 5c
            "RSqB",// 5d
            "Xor-",// 5e
            "Unds",// 5f
            "BQuo",// 60
            "a",// 61
            "b",// 62
            "c",// 63
            "d",// 64
            "e",// 65
            "f",// 66
            "g",// 67
            "h",// 68
            "i",// 69
            "j",// 6a
            "k",// 6b
            "l",// 6c
            "m",// 6d
            "n",// 6e
            "o",// 6f
            "p",// 70
            "q",// 71
            "r",// 72
            "s",// 73
            "t",// 74
            "u",// 75
            "v",// 76
            "w",// 77
            "x",// 78
            "y",// 79
            "z",// 7a
            "LBra",// 7b
            "Pipe",// 7c
            "RBra",// 7d
            "Tild",// 7e
            null// 7f
    };

    private void convert(String name) {
        boolean inIdent = true;
        for (int i = 0; i < name.length(); i++) {
            if (identChar.matcher(name).region(i, name.length()).lookingAt()) {
                if (!inIdent) {
                    inIdent = true;
                    sb.append("'");
                }
                sb.append(name.charAt(i));
            } else {
                if (inIdent) {
                    inIdent = false;
                    sb.append("'");
                }
                int charAt = (int) name.charAt(i);
                if (charAt < 128 && asciiReadableEncoding[charAt] != null) {
                    sb.append(asciiReadableEncoding[charAt]);
                } else {
                    sb.append(String.format("%04x", charAt));
                }
            }
        }
        if (!inIdent) {
            sb.append("'");
        }
    }

    private void convert(K k) {
        new VisitK() {
            @Override
            public void apply(KApply k) {
                if (impureFunctions.contains(k.klabel().name())) {
                    throw KEMException.internalError("Cannot yet translate impure function to kore: " + k.klabel().name(), k);
                }
                KLabel label = k.klabel();
                if (polyKLabels.containsKey(k.klabel().name())) {
                    label = computePolyKLabel(k);
                }
                convert(label, false);
                sb.append("(");
                String conn = "";
                for (K item : k.items()) {
                    sb.append(conn);
                    apply(item);
                    conn = ",";
                }
                sb.append(")");
            }

            @Override
            public void apply(KToken k) {
                sb.append("\\dv{");
                convert(k.sort(), false);
                sb.append("}(");
                sb.append(StringUtil.enquoteCString(k.s()));
                sb.append(")");
            }

            @Override
            public void apply(KSequence k) {
                if (k.size() == 1) {
                    apply(k.items().get(0));
                } else {
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
            }

            @Override
            public void apply(KVariable k) {
                sb.append("Var");
                convert(k.name());
                sb.append(":");
                convert(k.att().get(Sort.class), false);
            }

            @Override
            public void apply(KRewrite k) {
                sb.append("\\rewrites{");
                convert(k.att().get(Sort.class), false);
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
                convert(sort, false);
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
