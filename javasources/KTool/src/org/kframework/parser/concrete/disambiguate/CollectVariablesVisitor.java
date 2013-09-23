package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;
import java.util.HashMap;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Bracket;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicHookWorker;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class CollectVariablesVisitor extends BasicVisitor {
	public CollectVariablesVisitor(Context context) {
		super(context);
	}

	private java.util.Map<String, java.util.List<Variable>> vars = new HashMap<String, java.util.List<Variable>>();

	public java.util.Map<String, java.util.List<Variable>> getVars() {
		return vars;
	}

	public void setVars(java.util.Map<String, java.util.List<Variable>> vars) {
		this.vars = vars;
	}

	public void visit(Cell c) {
		if (c.getEllipses() == Ellipses.NONE)
			if (context.cellSorts.containsKey(c.getLabel())) {
				try {
					c.setContents((Term) c.getContents().accept(new CollectVariablesVisitor2(context, context.cellSorts.get(c.getLabel()))));
				} catch (TransformerException e) {
					e.printStackTrace();
				}
			}
		super.visit(c);
	}

	@Override
	public void visit(TermCons node) {
		if (isVisited(node))
			return;

		for (int i = 0, j = 0; i < node.getProduction().getItems().size(); i++) {
			if (node.getProduction().getItems().get(i) instanceof Sort) {
				Term t = node.getContents().get(j);
				try {
					t.accept(new CollectVariablesVisitor2(context, ((Sort) node.getProduction().getItems().get(i)).getName()));
				} catch (TransformerException e) {
					e.printStackTrace();
				}
				t.accept(this);
				j++;
			} else if (node.getProduction().getItems().get(i) instanceof UserList) {
				UserList ul = (UserList) node.getProduction().getItems().get(i);
				Term t1 = node.getContents().get(0);
				Term t2 = node.getContents().get(1);
				try {
					t1.accept(new CollectVariablesVisitor2(context, ul.getSort()));
					t2.accept(new CollectVariablesVisitor2(context, node.getProduction().getSort()));
				} catch (TransformerException e) {
					e.printStackTrace();
				}
				t1.accept(this);
				t2.accept(this);
			}
		}

		super.visit(node);
	}

	@Override
	public void visit(Variable var) {
		if (var.getExpectedSort() == null)
			var.setExpectedSort(var.getSort());
		if (!var.getName().equals(MetaK.Constants.anyVarSymbol) && var.isUserTyped())
			if (vars.containsKey(var.getName()))
				vars.get(var.getName()).add(var);
			else {
				java.util.List<Variable> varss = new ArrayList<Variable>();
				varss.add(var);
				vars.put(var.getName(), varss);
			}
	}

	/**
	 * A new class (nested) that goes down one level (jumps over Ambiguity, Rewrite and Bracket) and checks to see if there is a Variable
	 * 
	 * if found, sets a parameter to that variable with the expected sort gathered from the parent production
	 * 
	 * @author Radu
	 * 
	 */
	public class CollectVariablesVisitor2 extends BasicHookWorker {
		String expectedSort = null;

		public CollectVariablesVisitor2(Context context, String expectedSort) {
			super("org.kframework.parser.concrete.disambiguate.CollectVariablesVisitor2", context);
			this.expectedSort = expectedSort;
		}

		@Override
		public ASTNode transform(Variable node) throws TransformerException {
			if (node.isUserTyped()) {
				node.setExpectedSort(node.getSort());
				return node;
			}
			if (node.getExpectedSort() == null) {
				node.setExpectedSort(this.expectedSort);
			}
			// since the terms may be shared, if a node already has an expected sort set up
			// create a new variable with the correct information
			if (!node.getExpectedSort().equals(this.expectedSort)) {
				Variable newV = new Variable(node);
				newV.setExpectedSort(this.expectedSort);
				return newV;
			}
			return node;
		}

		@Override
		public ASTNode transform(Rewrite node) throws TransformerException {
			Rewrite result = new Rewrite(node);
			result.replaceChildren((Term) node.getLeft().accept(this), (Term) node.getRight().accept(this), context);
			return transform((Term) result);
		}

		@Override
		public ASTNode transform(Ambiguity node) throws TransformerException {
			TransformerException exception = null;
			ArrayList<Term> terms = new ArrayList<Term>();
			for (Term t : node.getContents()) {
				ASTNode result = null;
				try {
					result = t.accept(this);
					terms.add((Term) result);
				} catch (TransformerException e) {
					exception = e;
				}
			}
			if (terms.isEmpty())
				throw exception;
			if (terms.size() == 1) {
				return terms.get(0);
			}
			node.setContents(terms);
			return transform((Term) node);
		}

		@Override
		public ASTNode transform(Bracket node) throws TransformerException {
			node.setContent((Term) node.getContent().accept(this));
			return transform((Term) node);
		}
	}
}
