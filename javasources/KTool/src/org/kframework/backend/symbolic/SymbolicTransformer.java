package org.kframework.backend.symbolic;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.Rule;
import org.kframework.kil.Term;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

/**
 * This transformer applies some mechanical steps to the semantics 
 * of a programming language in order to transform it into a 
 * symbolic semantics.r
 */
public class SymbolicTransformer extends BasicTransformer {

	public SymbolicTransformer(String name) {
		super("Symbolic Transformer");
	}

	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		return super.transform(node);
	}
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		// TODO Auto-generated method stub
		
		LineariseTransformer lt = new LineariseTransformer("Linearise Rules");
		Rule rule = (Rule) lt.transform(node);
		
		ReplaceConstants rc = new ReplaceConstants("Replace Constants with Variables");
		rule = (Rule) rc.transform(rule);
		
		return rule;
	}
	
	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		Cell cell = new Cell();
		cell.setLabel(MetaK.Constants.pathCondition);
		cell.setEllipses(Ellipses.NONE);
		cell.setContents(new Constant("Bool", "true"));

		Term body = node.getBody();
		List<Term> col = new ArrayList<Term>();
		
		if (body instanceof Cell) {
			col.add(body);
		}
		else if (body instanceof Bag)
		{
			col = ((Bag) body).getContents();
		}
		
		col.add(cell);
		Bag bag = new Bag(col);
		node.setBody(bag);
		
		return node;
	}
}
