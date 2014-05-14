// Copyright (c) 2012-2014 K Team. All Rights Reserved.
package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;

/**
 * Initially created by: Traian Florin Serbanuta
 * <p/>
 * Date: 12/19/12
 * Time: 11:40 PM
 */
public class AddSuperheatRules extends CopyOnWriteTransformer {
    java.util.List<ModuleItem> superHeats = new ArrayList<ModuleItem>();
    public AddSuperheatRules(Context context) {
        super("Add Superheat rules", context);
    }

    @Override
    public ASTNode visit(Module node, Void _)  {
        superHeats.clear();
        node = (Module) super.visit(node, _);
        if (!superHeats.isEmpty()) {
            node = node.shallowCopy();
            node.setItems(new ArrayList<ModuleItem>(node.getItems()));
            node.getItems().addAll(superHeats);
        }
        return node;
    }

    @Override
    public ASTNode visit(Configuration node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(org.kframework.kil.Context node, Void _)  {
        return node;
    }

    @Override
    public ASTNode visit(Rule node, Void _)  {
        if (!node.containsAttribute(MetaK.Constants.heatingTag)) {
            return node;
        }
        boolean superheat = false;
        for (String heat : kompileOptions.superheat) {
            if (node.containsAttribute(heat)) {
                superheat = true;
                break;
            }
        }
        if (!(node.getBody() instanceof Rewrite)) {
            GlobalSettings.kem.register(
                    new KException(KException.ExceptionType.ERROR,
                            KException.KExceptionGroup.CRITICAL,
                            "Heating rules should have rewrite at the top.",
                            getName(),
                            node.getFilename(),
                            node.getLocation())
            );
        }
        final Rewrite body = (Rewrite) node.getBody();
        if (!superheat) {
            // rule heat(redex((C[e] =>  e ~> C) ~> _:K),, _:KList)
            KSequence kSequence = new KSequence();
            kSequence.getContents().add(body);
            kSequence.add(new Variable(MetaK.Constants.anyVarSymbol,"K"));
            Term redex = KApp.of(KLabelConstant.REDEX_KLABEL, kSequence);
            Term heat = KApp.of(
                    KLabelConstant.HEAT_KLABEL,
                    redex,
                    new Variable(MetaK.Constants.anyVarSymbol, KSorts.KLIST));
            Rule superHeat = node.shallowCopy();
            superHeat.setBody(heat);
            superHeats.add(superHeat);
            return node;
        }
        // add superheat rule
        // rule heat(redex(C[e] ~> RestHeat:K,,    LHeat:KList,,
        //                 (.KList => redex(e ~> C ~> RestHeat:K))),,_:KList)
        // when '_=/=K_('_inKList_(redex(e ~> C ~> RestHeat:K),,KList2KLabel LHeat:KList(.KList)),# true(.KList))
        Rule superHeat = node.shallowCopy();
        Term left = body.getLeft(); // C[e]
        Term right = body.getRight(); // e ~> C
        Variable restHeat = Variable.getFreshVar("K");
        Variable lHeat = Variable.getFreshVar(KSorts.KLIST);
        KSequence red1Seq = new KSequence();
        red1Seq.add(left); red1Seq.add(restHeat); //C[e] ~> RestHeat:K,
        KList red1List = new KList();
        red1List.add(red1Seq);red1List.add(lHeat); //C[e] ~> RestHeat:K,,    LHeat:KList
        KSequence red2Seq = new KSequence();
        KList red2List = new KList();
        red2List.add(red2Seq);
        red2Seq.getContents().addAll(((KSequence)right).getContents()); red2Seq.add(restHeat); // e ~> C ~> RestHeat:K
        Term red2 = new KApp(KLabelConstant.REDEX_KLABEL,
                red2List); // redex(e ~> C ~> RestHeat:K)
        Term red2rew = new Rewrite(KList.EMPTY, red2, context); // (.KList => redex(e ~> C ~> RestHeat:K))
        red1List.add(red2rew);
        Term red1 = new KApp(KLabelConstant.REDEX_KLABEL, red1List); // redex(C[e] ~> RestHeat:K,,    LHeat:KList,,
                                                               //       (.KList => redex(e ~> C ~> RestHeat:K)))
        KList heatList = new KList();
        heatList.add(red1);
        heatList.add(new Variable(MetaK.Constants.anyVarSymbol, KSorts.KLIST));
        Term heat = new KApp(KLabelConstant.HEAT_KLABEL, heatList);
        superHeat.setBody(heat);

        KList inListList = new KList();
        inListList.add(red2);
        inListList.add(KApp.of(new KInjectedLabel(lHeat)));
        Term inList = new KApp(KLabelConstant.of("'_inKList_", context), inListList);
        KList condList = new KList();
        condList.add(inList);
        condList.add(BoolBuiltin.TRUE);
        Term cond = new KApp(KLabelConstant.KNEQ_KLABEL, condList);
        superHeat.setRequires(MetaK.incrementCondition(node.getRequires(), cond));
        superHeats.add(superHeat);

        // replace heating rule by
        // rule C[e] => heat(redex(C[e]),, heated(.KList))
        node = node.shallowCopy();
        Term red3 = KApp.of(KLabelConstant.REDEX_KLABEL, left);
        KList red3List = new KList();
        red3List.add(red3);
        red3List.add(KApp.of(KLabelConstant.HEATED_KLABEL));
        Term heat2 = new KApp(KLabelConstant.HEAT_KLABEL, red3List);
        node.setBody(new Rewrite(left, heat2, context));


        return node;

    }

    @Override
    public ASTNode visit(Syntax node, Void _)  {
        return node;
    }
}
