package org.kframework.backend.unparser;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.DefinitionLoader;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Scanner;

public class AddBracketsFilter2 extends BasicTransformer {

	public AddBracketsFilter2() throws IOException {
		super("Add more brackets");
		org.kframework.parser.concrete.KParser.ImportTbl(DefinitionHelper.kompiled.getCanonicalPath() + "/def/Concrete.tbl");
	}

	private Term reparsed = null;
	public AddBracketsFilter2(Term reparsed) {
		super("Add brackets to term based on parse forest");
		this.reparsed = reparsed;
	}

	public Map<String, Term> substitution = new HashMap<String, Term>();
	private boolean atTop = true;

	@Override
	public ASTNode transform(TermCons ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(Constant ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}


	@Override
	public ASTNode transform(Collection ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(MapItem ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(Cell ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(CollectionItem ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(KApp ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(Hole ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(Freezer ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}

	@Override
	public ASTNode transform(KInjectedLabel ast) throws TransformerException {
		boolean tmp = atTop;
		atTop = false;
		ASTNode result = super.transform(ast);
		return postpare((Term)result, tmp);
	}
	
	private ASTNode postpare(Term ast, boolean atTop) throws TransformerException {
		if (reparsed != null) {
			ASTNode result = addBracketsIfNeeded(ast);
			if (atTop && result instanceof Bracket) {
				return new Cast(result.getLocation(), result.getFilename(), (Term)result);
			}
			return result;
		}
		UnparserFilter unparser = new UnparserFilter(false, false, false);
		ast.accept(unparser);
		String unparsed = unparser.getResult();
		try {
			ASTNode rule = DefinitionLoader.parsePatternAmbiguous(unparsed);
			Term reparsed = ((Rule)rule).getBody();
			return ast.accept(new AddBracketsFilter2(reparsed));
		} catch (TransformerException e) {
			return replaceWithVar(ast);
		}
	}

	private Variable replaceWithVar(Term ast) {
		Variable var = MetaK.getFreshVar(((Term)ast).getSort());
		substitution.put(var.getName(), (Term) ast);
		return var;
	}

	private ASTNode addBracketsIfNeeded(Term ast) throws TransformerException {
		TraverseForest trans = new TraverseForest(ast);
		reparsed = (Term)reparsed.accept(trans);
		if (trans.needsParens) {
			return new Bracket(ast.getLocation(), ast.getFilename(), ast);
		}
		return ast;
	}

	private class GetRealLocation extends BasicVisitor {
		public GetRealLocation(Term ast) {
			super("Find term in parse forest");
			this.ast = ast;
		}
		private Term ast;
		public Term realTerm;

		public void visit(Term t) {
			if (t.contains(ast)) {
				realTerm = t;
			}
		}
	}

	private class TraverseForest extends BasicTransformer {
		public TraverseForest(Term ast) {
			super("Determine if term needs parentheses");
			this.ast = ast;
		}
		private Term ast;
		public boolean needsParens;
		private boolean hasTerm;
		private boolean needsCast;
		private String realLocation;

		public ASTNode transform(Ambiguity amb) throws TransformerException {
			GetRealLocation visitor = new GetRealLocation(ast);
			amb.accept(visitor);
			if (visitor.realTerm == null) return amb;
			realLocation = visitor.realTerm.getLocation();
			for (int i = amb.getContents().size() - 1; i >= 0; i--) {
				Term t = amb.getContents().get(i);
				boolean tmp = hasTerm;
				hasTerm = false;
				t.accept(this);
				if (!hasTerm) {
					needsParens = true;
					amb.getContents().remove(i);
				}
				hasTerm = tmp;

			}
			if (amb.getContents().size() == 1)
				return amb.getContents().get(0);
			return amb;
		}

		public ASTNode transform(Term t) throws TransformerException {
			if (t.equals(ast) && t.getLocation().equals(realLocation)) {
				hasTerm = true;
			}
			return t;
		}
	}
}
