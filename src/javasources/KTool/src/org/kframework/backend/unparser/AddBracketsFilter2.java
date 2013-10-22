package org.kframework.backend.unparser;

import org.kframework.kil.*;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.krun.ColorSetting;
import org.kframework.parser.DefinitionLoader;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;
import java.util.Scanner;

public class AddBracketsFilter2 extends BasicTransformer {

	public AddBracketsFilter2(Context context) throws IOException {
		super("Add more brackets", context);
		org.kframework.parser.concrete.KParser.ImportTbl(context.kompiled.getCanonicalPath() + "/def/Concrete.tbl");
	}

	private Term reparsed = null;
	public AddBracketsFilter2(Term reparsed, Context context) {
		super("Add brackets to term based on parse forest", context);
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
		if (ast.getLabel() instanceof Token) return ast;
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
				return new Cast(result.getLocation(), result.getFilename(), (Term)result, context);
			}
			return result;
		}
		UnparserFilter unparser = new UnparserFilter(false, ColorSetting.OFF, false, true, context);
		ast.accept(unparser);
		String unparsed = unparser.getResult();
		try {
			ASTNode rule = DefinitionLoader.parsePatternAmbiguous(unparsed, context);
			Term reparsed = ((Sentence)rule).getBody();
			reparsed.accept(new AdjustLocations(context));
			if (!reparsed.contains(ast)) {
				return replaceWithVar(ast);
			}
			return ast.accept(new AddBracketsFilter2(reparsed, context));
		} catch (TransformerException e) {
			return replaceWithVar(ast);
		}
	}

	private class AdjustLocations extends BasicVisitor {
		public AdjustLocations(Context context) {
			super("Apply first-line location offset", context);
		}

		public void visit(ASTNode ast) {
			if (ast.getLocation().equals("generated")) return;
			Scanner scanner = new Scanner(ast.getLocation()).useDelimiter("[,)]").skip("\\(");
			int beginLine = scanner.nextInt();
			int beginCol = scanner.nextInt();
			int endLine = scanner.nextInt();
			int endCol = scanner.nextInt();
			ast.setLocation("(" + beginLine + "," + beginCol + "," + endLine + "," + endCol + ")");
		}
	}

	private Variable replaceWithVar(Term ast) {
		Variable var = Variable.getFreshVar(((Term)ast).getSort());
		substitution.put(var.getName(), (Term) ast);
		return var;
	}

	private ASTNode addBracketsIfNeeded(Term ast) throws TransformerException {
		TraverseForest trans = new TraverseForest(ast, context);
		reparsed = (Term)reparsed.accept(trans);
		if (trans.needsParens) {
			return new Bracket(ast.getLocation(), ast.getFilename(), ast, context);
		}
		return ast;
	}

	private class GetRealLocation extends BasicVisitor {
		public GetRealLocation(Term ast, Context context) {
			super("Find term in parse forest", context);
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
		public TraverseForest(Term ast, org.kframework.kil.loader.Context context) {
			super("Determine if term needs parentheses", context);
			this.ast = ast;
		}
		private Term ast;
		public boolean needsParens;
		private boolean hasTerm;
		private boolean needsCast;
		private String realLocation;

		public ASTNode transform(Ambiguity amb) throws TransformerException {
			realLocation = ast.getLocation();
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
