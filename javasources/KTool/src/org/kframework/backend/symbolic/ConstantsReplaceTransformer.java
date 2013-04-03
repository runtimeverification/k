package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Replace data constants with symbolic values and
 * store the pair (Variable,Constant) into a map.
 *
 * @author andreiarusoaie
 */
public class ConstantsReplaceTransformer extends CopyOnWriteTransformer {
    private Map<Variable, Constant> generatedSV;

    public ConstantsReplaceTransformer(String name) {
        super("Replace Constants");
        generatedSV = new HashMap<Variable, Constant>();
    }

    @Override
    public ASTNode transform(KApp node) throws TransformerException {

        if (!(node.getLabel() instanceof KInjectedLabel)) {
            return super.transform(node);
        }

        KInjectedLabel label = (KInjectedLabel) node.getLabel();

        if (!(label.getTerm() instanceof Constant)) {
            return super.transform(node);
        }

        Constant constant = (Constant) label.getTerm();
      
        if (!MetaK.isAbstractableSort(constant.getSort())) {
            return super.transform(node);
        }

        String sort = "K";
        Variable newVar = MetaK.getFreshVar(sort);

        generatedSV.put(newVar, constant);
        return newVar;
    }

    public Map<Variable, Constant> getGeneratedSV() {
        return generatedSV;
    }
}
