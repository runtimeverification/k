package ro.uaic.info.fmse.latex;

import java.util.HashMap;
import java.util.Map;
import java.util.List;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.k.LiterateComment.LiterateCommentType;
import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.BasicVisitor;

public class LatexFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	private String result="";
	private String preamble="";
	private boolean firstProduction = false;
	private Map<String,String> colors = new HashMap<String,String>();
	private LatexPatternsVisitor patternsVisitor = new LatexPatternsVisitor();
	

	public void setResult(String result) {
		this.result = result;
	}

	public void setPreamble(String preamble) {
		this.preamble = preamble;
	}

	public String getPreamble() {
		return preamble;
	}

	public String getResult() {
		return result;
	}
	
	@Override
	public void visit(Definition def) {
		def.accept(patternsVisitor);
		result += "\\begin{kdefinition}" + endl;
		super.visit(def);
		result += "\\end{kdefinition}" + endl;
	}
	
	@Override
	public void visit(Module mod) {
		if (DefinitionHelper.isModulePredefined(mod.getName())) return;
		result += "\\begin{module}{\\moduleName{" + DefinitionHelper.latexify(mod.getName()) + "}}" + endl;
		super.visit(mod);
		result += "\\end{module}" + endl;
	}
	
	@Override
	public void visit(Syntax syn) {
		result += endl + "\\begin{syntaxBlock}";
		firstProduction = true;
		super.visit(syn);
		result += endl + "\\end{syntaxBlock}" + endl;
	}
	
	@Override
	public void visit(Sort sort) {
		result += "{\\nonTerminal{\\sort{" + DefinitionHelper.latexify(sort.getSort()) + "}}}";
	}
	
	@Override
	public void visit(Production p) {
		if (firstProduction) {
			result += "\\syntax{";
			firstProduction = false;
		} else {
			result += "\\syntaxCont{";
		}
		if (p.getAttributes().containsKey(Constants.CONS_cons_ATTR) && 
				patternsVisitor.getPatterns().containsKey(p.getAttributes().get(Constants.CONS_cons_ATTR))) {
			String pattern = patternsVisitor.getPatterns().get(p.getAttributes().get(Constants.CONS_cons_ATTR));
			int n = 1;
			LatexFilter termFilter = new LatexFilter();
			for (ProductionItem pi : p.getItems()) {
				if (pi.getType()!=ProductionType.TERMINAL) {
					termFilter.setResult("");
					pi.accept(termFilter);
					pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
				}
			}
			result += pattern;
		} else {
			super.visit(p);
		}
		result += "}{";
		printSentenceAttributes(p.getAttributes());
		result += "}";
	}
	
	@Override
	public void visit(Terminal pi) {
		String terminal = pi.getTerminal();
		if (terminal.isEmpty()) return;
		if (DefinitionHelper.isSpecialTerminal(terminal)) {
			result += DefinitionHelper.latexify(terminal);
		} else {
			result += "\\terminal{" + DefinitionHelper.latexify(terminal) + "}";
		}
	}
	
	@Override
	public void visit(UserList ul) {
		result += "List\\{" + DefinitionHelper.latexify(ul.getSort()) + 
			", \\mbox{``}" + DefinitionHelper.latexify(ul.getSeparator()) + "\\mbox{''}\\}";
	}
	
	@Override
	public void visit(Configuration conf) {
		result += "\\kconfig{";
		super.visit(conf);
		result += "}" + endl;
	}
	
	@Override
	public void visit(Cell c) {
		if (c.getElipses().equals("left")) {
			result += "\\ksuffix";
		} else if (c.getElipses().equals("right")) {
			result += "\\kprefix";
		} else if (c.getElipses().equals("both")) {
			result += "\\kmiddle";
		} else {
			result += "\\kall";
		}
		if (c.getAttributes().containsKey("color")) {
			colors.put(c.getLabel(), c.getAttributes().get("color"));
		} 
		if (colors.containsKey(c.getLabel())) {
			result += "[" + colors.get(c.getLabel()) + "]";				
		}
		result += "{" + DefinitionHelper.latexify(c.getLabel()) + "}{";
		super.visit(c);
		result += "}" + endl;
	}
	
	public void visit(Collection col) {
		List<Term> contents = col.getContents();
		printList(contents, "\\mathrel{}");
	}

	private void printList(List<Term> contents, String str) {
		boolean first = true;
		for (Term trm : contents) {
			if (first) {
				first = false;
			} else {
				result += str;
			}
			trm.accept(this);
		}
	}
	
	
	@Override
	public void visit(Variable var) {
		if (var.getName().equals("_")) {
			result += "\\AnyVar";
		} else {
			result += "\\variable";
		}
		if (var.getSort() != null) {
			result += "[" + DefinitionHelper.latexify(var.getSort()) + "]";
		}
		if (!var.getName().equals("_")) {
			result += "{" + makeIndices(makeGreek(DefinitionHelper.latexify(var.getName()))) + "}";
		}
	}
	
	private String makeIndices(String str) {
		return str;
	}

	private String makeGreek(String name) {
		return name
		.replace("Alpha", "{\\alpha}")
		.replace("Beta", "{\\beta}")
		.replace("Gamma", "{\\gamma}")
		.replace("Delta", "{\\delta}")
		.replace("VarEpsilon", "{\\varepsilon}")
		.replace("Epsilon", "{\\epsilon}")
		.replace("Zeta", "{\\zeta}")
		.replace("Eta", "{\\eta}")
		.replace("Theta", "{\\theta}")
		.replace("Kappa", "{\\kappa}")
		.replace("Lambda", "{\\lambda}")
		.replace("Mu", "{\\mu}")
		.replace("Nu", "{\\nu}")
		.replace("Xi", "{\\xi}")
		.replace("Pi", "{\\pi}")
		.replace("VarRho", "{\\varrho}")
		.replace("Rho", "{\\rho}")
		.replace("VarSigma", "{\\varsigma}")
		.replace("Sigma", "{\\sigma}")
		.replace("GAMMA", "{\\Gamma}")
		.replace("DELTA", "{\\Delta}")
		.replace("THETA", "{\\Theta}")
		.replace("LAMBDA", "{\\Lambda}")
		.replace("XI", "{\\Xi}")
		.replace("PI", "{\\Pi}")
		.replace("SIGMA", "{\\Sigma}")
		.replace("UPSILON", "{\\Upsilon}")
		.replace("PHI", "{\\Phi}")
		;
	}

	@Override 
	public void visit(Empty e) {
		result += "\\dotCt{" + e.getSort() + "}";
	}
	
	@Override
	public void visit(Rule rule) {
		result += "\\krule";
		if (!rule.getLabel().equals("")) {
			result += "[" + rule.getLabel() + "]";
		}
		result += "{" + endl;
		rule.getBody().accept(this);
		result +=  "}{";
		if (rule.getCondition() != null) {
			rule.getCondition().accept(this);
		}
		result += "}{"; 
		printSentenceAttributes(rule.getAttributes()); 
		result += "}" + endl;
	}	
	
	@Override
	public void visit(Context cxt) {
		result += "\\kcontext";
		result += "{" + endl;
		cxt.getBody().accept(this);
		result +=  "}{";
		if (cxt.getCondition() != null) {
			cxt.getCondition().accept(this);
		}
		result += "}{"; 
		printSentenceAttributes(cxt.getAttributes()); 
		result += "}" + endl;
	}	
	
	@Override
	public void visit(Hole hole) {
		result += "\\khole{}";
	}
	
	@Override
	public void visit(Rewrite rew) {
		result += "\\reduce{";
		rew.getLeft().accept(this);
		result += "}{";
		rew.getRight().accept(this);
		result += "}";
	}
	
	@Override 
	public void visit(TermCons trm) {
		String pattern = patternsVisitor.getPatterns().get("\"" + trm.getCons() + "\"");
		if (pattern == null) {
			Production pr = DefinitionHelper.conses.get("\"" + trm.getCons() + "\"");
			pr.accept(patternsVisitor);
			pattern = patternsVisitor.getPatterns().get("\"" + trm.getCons() + "\"");
		}
		int n = 1;
		LatexFilter termFilter = new LatexFilter();
		for (Term t : trm.getContents()) {
			termFilter.setResult("");
			t.accept(termFilter);
			pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
		}
		result += pattern;
	}
	
	@Override
	public void visit(Constant c) {
		result += "\\constant[" + DefinitionHelper.latexify(c.getSort()) + "]{" + DefinitionHelper.latexify(c.getValue()) + "}";
	}
	
	@Override
	public void visit(MapItem mi) {
		mi.getKey().accept(this);
		result += "\\mapsto";		
		mi.getItem().accept(this);
	}
	
	@Override
	public void visit(KSequence k) {
		printList(k.getContents(), "\\kra");
		
	}
	
	@Override
	public void visit(KApp app) {
		app.getLabel().accept(this);
		result += "(";
		app.getChild().accept(this);
		result += ")";
	}
	
	@Override 
	public void visit(ListOfK list) {
		printList(list.getContents(), "\\kcomma");
	}
	
	@Override
	public void visit(LiterateDefinitionComment comment) {
		if (comment.getType()==LiterateCommentType.LATEX) {
			result += "\\begin{kblock}[text]" + endl;
			result += comment.getValue();
			result += "\\end{kblock}" + endl;		
		} else if (comment.getType()==LiterateCommentType.PREAMBLE) {
			preamble += comment.getValue();
		}
	}
	
	@Override
	public void visit(LiterateModuleComment comment) {
		if (comment.getType()==LiterateCommentType.LATEX) {
			result += "\\begin{kblock}[text]" + endl;
			result += comment.getValue();
			result += "\\end{kblock}" + endl;		
		} else if (comment.getType()==LiterateCommentType.PREAMBLE) {
			preamble += comment.getValue();
		}
	}	
	
	private void printSentenceAttributes(Map<String, String> attributes) {
		boolean first = true;
		String value;
		for (Map.Entry<String, String> entry : attributes.entrySet()) {
			if (DefinitionHelper.isTagGenerated(entry.getKey())) continue;
			if (entry.getKey().equals("latex")) continue;
			if (first) {
				first = false;
			} else {
				result += ", ";
			}
			result += entry.getKey();
			value = entry.getValue();
			if (!value.isEmpty()) {
				result += "(" + value + ")"; 
			}
		}
	}
}
