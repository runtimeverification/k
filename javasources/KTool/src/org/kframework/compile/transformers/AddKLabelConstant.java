package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;


public class AddKLabelConstant extends CopyOnWriteTransformer {

    private static final KLabelConstant KLabelConstantPredicate =
            KLabelConstant.ofStatic(AddPredicates.predicate("KLabelConstant"));

    public AddKLabelConstant(DefinitionHelper definitionHelper) {
        super("Define isKLabelConstant predicate for KLabel constants", definitionHelper);
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        // declare the isKLabelConstant predicate as KLabel
        retNode.addConstant(KLabelConstantPredicate);

        for (String klbl : node.getModuleKLabels()) {
            Term kapp = KApp.of(new KInjectedLabel(KLabelConstant.of(klbl, definitionHelper)));
            Term lhs = KApp.of(KLabelConstantPredicate, kapp);
            Term rhs = BoolBuiltin.TRUE;
            Rule rule = new Rule(lhs, rhs, definitionHelper);
            rule.addAttribute(Attribute.PREDICATE);
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}

