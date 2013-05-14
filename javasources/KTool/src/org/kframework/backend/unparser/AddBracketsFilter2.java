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

	public AddBracketsFilter2(DefinitionHelper definitionHelper) throws IOException {
		super("Add more brackets", definitionHelper);
		org.kframework.parser.concrete.KParser.ImportTbl(definitionHelper.kompiled.getCanonicalPath() + "/def/Concrete.tbl");
	}

	private Term reparsed = null;
	public AddBracketsFilter2(Term reparsed, DefinitionHelper definitionHelper) {
		super("Add brackets to term based on parse forest", definitionHelper);
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
				return new Cast(result.getLocation(), result.getFilename(), (Term)result, definitionHelper);
			}
			return result;
		}
		UnparserFilter unparser = new UnparserFilter(false, false, false, true, definitionHelper);
		ast.accept(unparser);
		String unparsed = unparser.getResult();
		try {
			ASTNode rule = DefinitionLoader.parsePatternAmbiguous(unparsed, definitionHelper);
			Term reparsed = ((Rule)rule).getBody();
			reparsed.accept(new AdjustLocations(definitionHelper));
			if (!reparsed.contains(ast)) {
				return replaceWithVar(ast);
			}
			return ast.accept(new AddBracketsFilter2(reparsed, definitionHelper));
		} catch (TransformerException e) {
			return replaceWithVar(ast);
		}
	}

	private class AdjustLocations extends BasicVisitor {
		public AdjustLocations(DefinitionHelper definitionHelper) {
			super("Apply first-line location offset", definitionHelper);
		}

		public void visit(ASTNode ast) {
			if (ast.getLocation().equals("generated")) return;
			Scanner scanner = new Scanner(ast.getLocation()).useDelimiter("[,)]").skip("\\(");
			int beginLine = scanner.nextInt();
			int beginCol = scanner.nextInt();
			int endLine = scanner.nextInt();
			int endCol = scanner.nextInt();
			if (beginLine == 1) {
				beginCol -= "rule ".length();
			}
			if (endLine == 1) {
				endCol -= "rule ".length();
			}
			ast.setLocation("(" + beginLine + "," + beginCol + "," + endLine + "," + endCol + ")");
		}
	}

	private Variable replaceWithVar(Term ast) {
		Variable var = MetaK.getFreshVar(((Term)ast).getSort(definitionHelper));
		substitution.put(var.getName(), (Term) ast);
		return var;
	}

	private ASTNode addBracketsIfNeeded(Term ast) throws TransformerException {
		TraverseForest trans = new TraverseForest(ast, definitionHelper);
		reparsed = (Term)reparsed.accept(trans);
		if (trans.needsParens) {
			return new Bracket(ast.getLocation(), ast.getFilename(), ast, definitionHelper);
		}
		return ast;
	}

	private class GetRealLocation extends BasicVisitor {
		public GetRealLocation(Term ast, DefinitionHelper definitionHelper) {
			super("Find term in parse forest", definitionHelper);
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
		public TraverseForest(Term ast, DefinitionHelper definitionHelper) {
			super("Determine if term needs parentheses", definitionHelper);
			this.ast = ast;
		}
		private Term ast;
		public boolean needsParens;
		private boolean hasTerm;
		private boolean needsCast;
		private String realLocation;

		public ASTNode transform(Ambiguity amb) throws TransformerException {
			GetRealLocation visitor = new GetRealLocation(ast, definitionHelper);
			amb.accept(visitor);
			if (visitor.realTerm == null) return amb;
			realLocation = visitor.realTerm.getLocation();
			for (int i = amb.getContents().size() - 1; i >= 0; i--) {
				Term t = amb.getContents().get(i);
				boolean tmp = hasTerm;
				hasTerm = false;
				t.accept(this);
				if (!hasTerm) {
					System.err.println(realLocation);
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
