package org.kframework.compile.transformers;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.Module;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class AddStreamCells extends CopyOnWriteTransformer {

    List<Rule> generated = new ArrayList<Rule>();

    public AddStreamCells(Context context) {
        super("Add cells to stream rules", context);
    }

    @Override
    public ASTNode transform(Module node) throws TransformerException {
        ASTNode result = super.transform(node);
		if (generated.isEmpty()) return node;
		result = result.shallowCopy();
		((Module)result).getItems().addAll(generated);
		return result;
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
	
    @Override
    public ASTNode transform(Rule node) throws TransformerException {
        boolean isStream = false;
        if (node.getAttributes().containsKey("stdin")) {
            isStream = true;
            addRules(node, "stdin");
        }
        if (node.getAttributes().containsKey("stdout")) {
            isStream = true;
            addRules(node, "stdout");
        }
        if (node.getAttributes().containsKey("stderr")) {
            isStream = true;
            addRules(node, "stderr");
        }
        if (isStream) {
            return null;
        }
        return node;
    }

    private void addRules(Rule rule, String stream) {
        if (!(rule.getBody().getSort().equals("List") || rule.getBody().getSort().equals("ListItem"))) {
            GlobalSettings.kem.register(new KException(ExceptionType.ERROR,
                    KExceptionGroup.INTERNAL,
                    "Found a rule tagged '" + stream + "' whose body wasn't of sort List.",
                        getName(), rule.getFilename(), rule.getLocation()));
        }
        Set<Cell> cells = new HashSet<Cell>();
        for (String cellName : context.cells.keySet()) {
            Cell cell = context.cells.get(cellName);
            if (stream.equals(cell.getCellAttributes().get("stream"))) {
                cells.add(cell);
            }
        }
        for (Cell cell : cells) {
            Rule newRule = rule.shallowCopy();
            newRule.setBody(MetaK.wrap(rule.getBody(), cell.getLabel(), Ellipses.NONE));
            generated.add(newRule);
        }
    }
}
