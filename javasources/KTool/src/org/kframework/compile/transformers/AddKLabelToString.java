package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;

import java.util.ArrayList;


public class AddKLabelToString extends CopyOnWriteTransformer {

    private static final Constant KLabel2String =
            new Constant("KLabel", "KLabel2String");

    public AddKLabelToString() {
        super("Define KLabel2String for KLabel constants");
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        Module retNode = node.shallowCopy();
        retNode.setItems(new ArrayList<ModuleItem>(node.getItems()));

        for (String klbl : node.getModuleKLabels()) {
            Constant klblCt = new Constant("KLabel", klbl);
            Term kapp = new KApp(new KInjectedLabel(klblCt), Empty.ListOfK);
            ListOfK list = new ListOfK();
            list.getContents().add(kapp);
            Term lhs = new KApp(KLabel2String, list);
            String str = "\"" + klbl.replace("\"","\\\"") + "\"";
            Constant strCt = new Constant("String", str);
            Term rhs = new KApp(new KInjectedLabel(strCt), Empty.ListOfK);
            Rule rule = new Rule();
            rule.setBody(new Rewrite(lhs, rhs));
            rule.getAttributes().getContents().add(new Attribute("function", ""));
            retNode.appendModuleItem(rule);
        }

        if (retNode.getItems().size() != node.getItems().size())
            return retNode;
        else
            return node;
    }

}
