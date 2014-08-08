// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
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
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

/**
 * Transformer class for semantic equality.
 *
 * @see CopyOnWriteTransformer
 *
 * @author AndreiS
 */
public class AddSemanticEquality extends CopyOnWriteTransformer {

    public static final Sort EQUALITY_SORT = Sort.of("EqualitySort");
    public static final KLabelConstant EQUALITY_PREDICATE
            = KLabelConstant.of(AddPredicates.predicate(EQUALITY_SORT));

    private Map<String, String> equalities = new HashMap<String, String>();

    @Override
    public ASTNode visit(Module node, Void _)  {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        Set<Production> eqProds = node.getSyntaxByTag(Attribute.EQUALITY_KEY, context);
        for (Production prod : eqProds)
            /*
             * operators tagged with "equality" must have the signature
             * Sort -> Sort -> Bool
             */
            if (prod.getSort().equals(Sort.BOOL))
                if (prod.getArity() == 2)
                    if (prod.getChildSort(0).equals(prod.getChildSort(1)))
                        if (!equalities.containsKey(prod.getChildSort(0)))
                            equalities.put(prod.getChildSort(0).getName(), prod.getKLabel());
                        else
                            GlobalSettings.kem.registerCriticalError(
                                    "redeclaration of equality for sort " + prod.getChildSort(0),
                                    this, prod);
                    else
                        GlobalSettings.kem.registerCriticalError(
                                "arguments for equality expected to be of the same sort",
                                this, prod);
                else
                    GlobalSettings.kem.registerCriticalError(
                            "unexpected number of arguments for equality, expected 2",
                            this, prod);
            /* TOOD(AndreiS): cink fails this check; either fix cink or remove the check
            else
                GlobalSettings.kem.register(new KException(
                        KException.ExceptionType.ERROR,
                        KException.KExceptionGroup.CRITICAL,
                        "unexpected sort " + prod.getSort() + " for equality, expected sort "
                        + Sort.BOOL,
                        prod.getFilename(),
                        prod.getLocation()));
            */

        retNode.addConstant(EQUALITY_PREDICATE);

        /* defer =K to =Sort for sorts with equality */
        for(Map.Entry<String, String> item : equalities.entrySet()) {
            Sort sort = Sort.of(item.getKey());
            KLabelConstant sortEq = KLabelConstant.of(item.getValue(), context);
            if (sort.isComputationSort()) {
                retNode.addSubsort(EQUALITY_SORT, sort, context);

                KList kList = new KList();
                kList.add(Variable.getFreshVar(sort));
                kList.add(Variable.getFreshVar(sort));

                Term lhs = new KApp(KLabelConstant.KEQ, kList);
                Term rhs = new KApp(sortEq, kList);
                Rule rule = new Rule(lhs, rhs, context);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);
            }
        }

        Set<Production> prods = node.getSyntaxByTag("", context);
        for (Production prod : prods) {
            if (!prod.isSubsort()
                    && !prod.containsAttribute(Attribute.BRACKET.getKey())
                    && !prod.containsAttribute(Attribute.FUNCTION.getKey())
                    && !prod.containsAttribute(Attribute.PREDICATE.getKey())
                    && (!prod.getSort().isKSort() || prod.getSort().equals(Sort.K))) {
                Variable KListVar1 = Variable.getFreshVar(Sort.KLIST);
                Variable KListVar2 = Variable.getFreshVar(Sort.KLIST);

                KList lhsList = new KList();
                lhsList.add(new KApp(KLabelConstant.of(prod.getKLabel(), context), KListVar1));
                lhsList.add(new KApp(KLabelConstant.of(prod.getKLabel(), context), KListVar2));

                KList rhsList = new KList();
                rhsList.add(KApp.of(new KInjectedLabel(KListVar1)));
                rhsList.add(KApp.of(new KInjectedLabel(KListVar2)));

                Term lhs = new KApp(KLabelConstant.KEQ, lhsList);
                Term rhs = new KApp(KLabelConstant.KLIST_EQUALITY, rhsList);
                Rule rule = new Rule(lhs, rhs, context);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);
            }
        }

        /* defer =K to ==K for lexical tokens */
        for (Sort sort : context.getTokenSorts()) {
            KList kList = new KList();
            kList.add(Variable.getFreshVar(sort));
            kList.add(Variable.getFreshVar(sort));

            Term lhs = new KApp(KLabelConstant.KEQ, kList);
            Term rhs = new KApp(KLabelConstant.KEQ_KLABEL, kList);
            Rule rule = new Rule(lhs, rhs, context);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        /*
        Variable var = MetaK.getFreshVar(MetaK.Constants.K);
        KList list = new KList();
        list.add(var);
        list.add(var);
        Rule rule = new Rule(new KApp(K_EQUALITY, list), Constant.TRUE);
        rule.addAttribute(Attribute.EQUALITY);
        retNode.appendModuleItem(rule);


        for (String sort : retNode.getAllSorts()) {
            if (MetaK.isComputationSort(sort) && !equalities.containsKey(sort)) {
                String symCtor = AddSymbolicK.symbolicConstructor(sort);
                Term symTerm = new KApp(Constant.KLABEL(symCtor), MetaK.getFreshVar(MetaK.Constants.KList));
                KList list = new KList();
                list.add(symTerm);
                list.add(symTerm);
                Rule rule = new Rule(new KApp(K_EQUALITY, list), Constant.TRUE);
                rule.addAttribute(Attribute.EQUALITY);
                retNode.appendModuleItem(rule);
            }
        }
        */

        /*
        Set<Production> prods = node.getSyntaxByTag("");
        for (Production prod : prods) {
            if (!prod.isSubsort()
                    && !prod.containsAttribute(Attribute.BRACKET.getKey())
                    && !prod.containsAttribute(Attribute.FUNCTION.getKey())
                    && !prod.containsAttribute(Attribute.PREDICATE.getKey())) {
                Variable KListVar1 = MetaK.getFreshVar(MetaK.Constants.KList);
                Variable KListVar2 = MetaK.getFreshVar(MetaK.Constants.KList);

                KList lhsList = new KList();
                lhsList.add(new KApp(Constant.KLABEL(prod.getKLabel()), KListVar1));
                lhsList.add(new KApp(Constant.KLABEL(prod.getKLabel()), KListVar2));

                KList rhsList = new KList();
                rhsList.add(new KApp(new KInjectedLabel(KListVar1), Empty.KList));
                rhsList.add(new KApp(new KInjectedLabel(KListVar2), Empty.KList));

                Term lhs = new KApp(K_EQUALITY, lhsList);
                Term rhs = new KApp(KLIST_EQUALITY, rhsList);
                Rule rule = new Rule(lhs, rhs);
                rule.addAttribute(Attribute.FUNCTION);
                retNode.appendModuleItem(rule);
            }
        }
        */

        return retNode;
    }

    public AddSemanticEquality(Context context) {
        super("Define semantic equality", context);
    }
}
