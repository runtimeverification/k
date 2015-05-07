// Copyright (c) 2012-2015 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import org.kframework.compile.utils.SyntaxByTag;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.Production;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KEMException;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ResolveBinder extends CopyOnWriteTransformer {

    private static final KLabelConstant BINDER_PREDICATE
            = KLabelConstant.of(AddPredicates.predicate(Sort.of("Binder")));
    private static final KLabelConstant BOUNDED_PREDICATE
            = KLabelConstant.of(AddPredicates.predicate(Sort.of("Bound")));
    private static final KLabelConstant BOUNDING_PREDICATE
            = KLabelConstant.of(AddPredicates.predicate(Sort.of("Bounding")));

    private static final String REGEX
            = "\\s*(\\d+)(\\s*-\\>\\s*(\\d+))?\\s*(,?)";

    public ResolveBinder(Context context) {
        super("Resolve binder", context);
    }

    @Override
    public ASTNode visit(Module node, Void _void)  {
        Set<Production> prods = SyntaxByTag.get(node, "binder", context);
        prods.addAll(SyntaxByTag.get(node, "metabinder", context));
        if (prods.isEmpty())
            return node;

        List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
        node = node.shallowCopy();
        node.setItems(items);

        for (Production prod : prods) {
            String bindInfo = prod.getAttribute("binder");
            if (bindInfo == null || bindInfo.equals("")) {
                bindInfo = prod.getAttribute("metabinder");
                if (bindInfo == null || bindInfo.equals("")) {
                    bindInfo = "1->" + prod.getArity();
                }
            }
            Pattern p = Pattern.compile(REGEX);
            Matcher m = p.matcher(bindInfo);
            Multimap<Integer, Integer> bndMap = HashMultimap.create();

            while (m.regionStart() < m.regionEnd()) {
                if (!m.lookingAt()) {
                    throw KEMException.criticalError(
                            "could not parse binder attribute \"" + bindInfo.substring(m.regionStart(), m.regionEnd()) + "\"");
                }
                if (m.end() < m.regionEnd()) {
                    if (!m.group(4).equals(",")) {
                        throw KEMException.criticalError("expecting ',' at the end \"" + m.group() + "\"");
                    }
                } else {
                    if (!m.group(4).equals("")) {
                        throw KEMException.criticalError("unexpected ',' at the end \"" + m.group() + "\"");
                    }
                }

                int bndIdx = Integer.parseInt(m.group(1)) - 1; //rebasing  bindings to start at 0
                if (m.group(3) == null) {
                    for (int idx = 0; idx < prod.getArity(); idx++) {
                        if (idx != bndIdx)
                            bndMap.put(bndIdx, idx);
                    }
                } else {
                    bndMap.put(bndIdx, Integer.parseInt(m.group(3)) - 1);  //rebasing positions to start at 0
                }

                m.region(m.end(), m.regionEnd());
            }

            prod.setBinderMap(bndMap);

            Rule rule = new Rule(
                    KApp.of(BINDER_PREDICATE, MetaK.getTerm(prod, context)),
                    BoolBuiltin.TRUE, context);
            rule.addAttribute(Attribute.ANYWHERE);

            Term klblK = KApp.of(new KInjectedLabel(KLabelConstant.of(prod.getKLabel())));

            for (int bndIdx : bndMap.keySet()) {
                KList list = new KList();
                list.getContents().add(klblK);
                list.getContents().add(IntBuiltin.kAppOf(bndIdx + 1));
                rule = new Rule(new KApp(BOUNDED_PREDICATE, list), BoolBuiltin.TRUE, context);
                rule.addAttribute(Attribute.ANYWHERE);
                //String bndSort = prod.getChildSort(bndIdx - 1);
                // (AndreiS): the bounded sort is no longer automatically
                // considered to be subsorted to Variable; Variable must be
                // manually declared.
                //items.add(AddPredicates.getIsVariableRule(
                //        new Variable(MetaK.Constants.anyVarSymbol, bndSort),
                //        context));
            }

            for (int bodyIdx : bndMap.values()) {
                KList list = new KList();
                list.getContents().add(klblK);
                list.getContents().add(IntBuiltin.kAppOf(bodyIdx + 1));
                rule = new Rule(new KApp(BOUNDING_PREDICATE, list), BoolBuiltin.TRUE, context);
                rule.addAttribute(Attribute.ANYWHERE);
            }
        }

        return node;
    }
}
