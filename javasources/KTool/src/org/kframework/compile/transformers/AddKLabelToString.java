package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;


public class AddKLabelToString extends CopyOnWriteTransformer {

    private static final Constant KLabel2String =
            new Constant("KLabel", "KLabel2String");

    private static final String String2KLabelCons =
            "KLabel1String2KLabelSyn";

    public AddKLabelToString() {
        super("Define KLabel2String and String2Klabel for KLabel constants");
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (String klbl : node.getModuleKLabels()) {
            Constant klblCt = new Constant("KLabel", klbl);
            Term kapp = new KApp(new KInjectedLabel(klblCt), Empty.ListOfK);
            KList list = new KList();
            list.getContents().add(kapp);
            Term lhs = new KApp(KLabel2String, list);
            String str = "\"" + klbl.replace("\"","\\\"") + "\"";
            Constant strCt = new Constant("#String", str);
            Term rhs = new KApp(new KInjectedLabel(strCt), Empty.ListOfK);
            Rule rule = new Rule(lhs, rhs);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);

            java.util.List<Term> termList = new ArrayList<Term>();
            termList.add(rhs);
            TermCons termCons = new TermCons("KLabel", String2KLabelCons, termList);
            rule = new Rule(termCons, klblCt);
            rule.addAttribute(Attribute.FUNCTION);
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}
