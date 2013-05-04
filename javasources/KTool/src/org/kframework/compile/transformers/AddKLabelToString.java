package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;

import java.util.ArrayList;


public class AddKLabelToString extends CopyOnWriteTransformer {

    private static final KLabelConstant KLabel2String =
            KLabelConstant.of("KLabel2String");

    private static final String String2KLabelCons =
            "KLabel1String2KLabelSyn";

    public AddKLabelToString() {
        super("Define KLabel2String and String2Klabel for KLabel constants");
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        /* TODO: escape labels when generating KLabel2String and String2KLabel */
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (String klbl : node.getModuleKLabels()) {
            Term kapp = KApp.of(new KInjectedLabel(KLabelConstant.of(klbl)));
            Term lhs = KApp.of(KLabel2String, kapp);
            Term rhs = KApp.of(new KInjectedLabel(StringBuiltin.of(StringUtil.escapeMaude(klbl).replace("\"","\\\""))));
            Rule rule = new Rule(lhs, rhs);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);

            java.util.List<Term> termList = new ArrayList<Term>();
            termList.add(rhs);
            TermCons termCons = new TermCons(KSorts.KLABEL, String2KLabelCons, termList);
            rule = new Rule(termCons, KLabelConstant.of(klbl));
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}
