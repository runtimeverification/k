package org.kframework.backend.symbolic;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Token;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * Replace data constants with symbolic values and
 * store the pair (Variable,Constant) into a map.
 *
 * @author andreiarusoaie
 */
public class ConstantsReplaceTransformer extends CopyOnWriteTransformer {
    private Map<Variable, Token> generatedSV;

    public ConstantsReplaceTransformer(String name, DefinitionHelper definitionHelper) {
        super("Replace Constants", definitionHelper);
        generatedSV = new HashMap<Variable, Token>();
    }
    
    @Override
    public ASTNode transform(Token node) throws TransformerException {
        Variable newVar = Variable.getFreshVar(node.getSort(definitionHelper));
        generatedSV.put(newVar, node);
        return newVar;
    }
    

    public Map<Variable, Token> getGeneratedSV() {
		return generatedSV;
	}
}
