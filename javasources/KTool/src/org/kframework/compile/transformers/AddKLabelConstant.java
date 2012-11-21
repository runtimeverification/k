package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;


public class AddKLabelConstant extends CopyOnWriteTransformer {

    private static final Constant KLabelConstantPredicate =
            new Constant("KLabel", AddPredicates.predicate("KLabelConstant"));

    public AddKLabelConstant() {
        super("Define isKLabelConstant predicate for KLabel constants");
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        // declare the isKLabelConstant predicate as KLabel
        retNode.addConstant(KLabelConstantPredicate);

        for (String klbl : node.getModuleKLabels()) {
            Constant klblCt = new Constant("KLabel", klbl);
            Term kapp = new KApp(new KInjectedLabel(klblCt), Empty.ListOfK);
            ListOfK list = new ListOfK();
            list.getContents().add(kapp);
            Term lhs = new KApp(KLabelConstantPredicate, list);
            Term trueCt = new Constant("#Bool", "true");
            Term rhs = new KApp(new KInjectedLabel(trueCt), Empty.ListOfK);
            Rule rule = new Rule();
            rule.setBody(new Rewrite(lhs, rhs));
            rule.getAttributes().getContents().add(new Attribute("predicate", ""));
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}

