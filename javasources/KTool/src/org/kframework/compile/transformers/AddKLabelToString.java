package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;

import java.util.ArrayList;


public class AddKLabelToString extends CopyOnWriteTransformer {

    private static final KLabelConstant KLabel2String =
            KLabelConstant.ofStatic("KLabel2String");

    private static final String String2KLabelCons =
            "KLabel1String2KLabelSyn";

    public AddKLabelToString(DefinitionHelper definitionHelper) {
        super("Define KLabel2String and String2Klabel for KLabel constants", definitionHelper);
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        /* TODO: escape labels when generating KLabel2String and String2KLabel */
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (String klbl : node.getModuleKLabels()) {
            Term kapp = KApp.of(definitionHelper, new KInjectedLabel(KLabelConstant.of(klbl, definitionHelper)));
            Term lhs = KApp.of(definitionHelper, KLabel2String, kapp);
            Term rhs = KApp.of(definitionHelper, new KInjectedLabel(StringBuiltin.of(StringUtil.escapeMaude(klbl).replace("\"","\\\""))));
            Rule rule = new Rule(lhs, rhs, definitionHelper);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);

            java.util.List<Term> termList = new ArrayList<Term>();
            termList.add(rhs);
            TermCons termCons = new TermCons(KSorts.KLABEL, String2KLabelCons, termList);
            rule = new Rule(termCons, KLabelConstant.of(klbl, definitionHelper), definitionHelper);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}
