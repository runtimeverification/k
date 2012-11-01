package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import java.util.ArrayList;
import java.util.List;

/**
 * Initially created by Traian Florin Serbanuta
 * Date: 10/31/12
 * Time: 11:46 PM
 */
public class ContextsToHeating extends CopyOnWriteTransformer {
    List<ModuleItem> heating = new ArrayList<ModuleItem>();
    public ContextsToHeating() {
           super("Contexts to Heating Rules");
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        ASTNode result = super.transform(node);
        if (result == node) return node;
        node = ((Module) result).shallowCopy();
        node.setItems(new ArrayList<ModuleItem>(node.getItems()));
        node.getItems().addAll(heating);
        return node;
    }

    @Override
    public ASTNode transform(Context node) {
        Variable x = MetaK.getFreshVar("KItem");
        Term body = node.getBody();
        Term leftHeat = MetaK.fillHole(body, x);
        Term cond = node.getCondition();
        if (cond != null) {
            cond = MetaK.fillHole(cond, x);
        }
        List<Term> seq = new ArrayList<Term>();
        seq.add(x);
        seq.add(MetaK.createFreezer(body));
        KSequence rightHeat = new KSequence(seq);
        return null;
    }

    @Override
    public ASTNode transform(Syntax node) {
        return node;
    }

    @Override
    public ASTNode transform(Rule node) {
        return node;
    }

    @Override
    public ASTNode transform(Configuration node) {
        return node;
    }
}
