package org.kframework.backend.latex;

import java.util.HashMap;
import java.util.Map;
import java.util.List;
import java.util.regex.Pattern;

import org.kframework.kil.*;
import org.kframework.kil.LiterateComment.LiterateCommentType;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;

import ro.uaic.info.fmse.utils.strings.StringUtil;

public class LatexFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	private String result = "";
	private String preamble = "";
	private boolean firstProduction = false;
	private Map<String, String> colors = new HashMap<String, String>();
	private LatexPatternsVisitor patternsVisitor = new LatexPatternsVisitor();
	private boolean firstAttribute;
	private boolean parentParens = false;

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

	public boolean isParentParens() {
		return parentParens;
	}

	private void setParentParens(boolean parentParens) {
		this.parentParens = parentParens;
	}

	@Override
	public void visit(Definition def) {
		def.accept(patternsVisitor);
		result += "\\begin{kdefinition}" + endl + "\\maketitle" + endl;
		super.visit(def);
		result += "\\end{kdefinition}" + endl;
		if (!preamble.contains("\\title{")) {
			preamble += "\\title{" + def.getMainModule() + "}" + endl;
		}
	}

	@Override
	public void visit(Module mod) {
		if (mod.isPredefined())
			return;
		result += "\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl;
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
		result += "{\\nonTerminal{\\sort{" + StringUtil.latexify(sort.getName()) + "}}}";
	}

	@Override
	public void visit(Production p) {
		if (firstProduction) {
			result += "\\syntax{";
			firstProduction = false;
		} else {
			result += "\\syntaxCont{";
		}
		if (p.getItems().get(0).getType() != ProductionType.USERLIST && p.getAttributes().containsKey(Constants.CONS_cons_ATTR) && patternsVisitor.getPatterns().containsKey(p.getAttributes().get(Constants.CONS_cons_ATTR))) {
			String pattern = patternsVisitor.getPatterns().get(p.getAttributes().get(Constants.CONS_cons_ATTR));
			int n = 1;
			LatexFilter termFilter = new LatexFilter();
			for (ProductionItem pi : p.getItems()) {
				if (pi.getType() != ProductionType.TERMINAL) {
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
		p.getAttributes().accept(this);
		result += "}";
	}

	@Override
	public void visit(Terminal pi) {
		String terminal = pi.getTerminal();
		if (terminal.isEmpty())
			return;
		if (DefinitionHelper.isSpecialTerminal(terminal)) {
			result += StringUtil.latexify(terminal);
		} else {
			result += "\\terminal{" + StringUtil.latexify(terminal) + "}";
		}
	}

	@Override
	public void visit(UserList ul) {
		result += "List\\{" + StringUtil.latexify(ul.getSort()) + ", \\mbox{``}" + StringUtil.latexify(ul.getSeparator()) + "\\mbox{''}\\}";
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
		result += "{" + StringUtil.latexify(c.getLabel() + StringUtil.emptyIfNull(c.getAttributes().get("multiplicity"))) + "}{";
		super.visit(c);
		result += "}" + endl;
	}

	public void visit(Collection col) {
		List<Term> contents = col.getContents();
		printList(contents, "\\mathrel{}");
	}

	private void printList(List<Term> contents, String str) {
//		result += "\\begin{array}{l}";
		boolean first = true;
		for (Term trm : contents) {
			if (first) {
				first = false;
			} else {
				result += str;
			}
			trm.accept(this);
		}
//		result += "\\end{array}";
	}
	
	public void visit(TermComment tc) {
		result += "\\\\";
		super.visit(tc);
	}

	@Override
	public void visit(Variable var) {
		if (var.getName().equals("_")) {
			result += "\\AnyVar";
		} else {
			result += "\\variable";
		}
		if (var.getSort() != null) {
			result += "[" + StringUtil.latexify(var.getSort()) + "]";
		}
		if (!var.getName().equals("_")) {
			result += "{" + makeIndices(makeGreek(StringUtil.latexify(var.getName()))) + "}";
		}
	}

	private String makeIndices(String str) {
		return str;
	}

	private String makeGreek(String name) {
		return name.replace("Alpha", "{\\alpha}").replace("Beta", "{\\beta}").replace("Gamma", "{\\gamma}").replace("Delta", "{\\delta}").replace("VarEpsilon", "{\\varepsilon}").replace("Epsilon", "{\\epsilon}").replace("Zeta", "{\\zeta}").replace("Eta", "{\\eta}")
				.replace("Theta", "{\\theta}").replace("Kappa", "{\\kappa}").replace("Lambda", "{\\lambda}").replace("Mu", "{\\mu}").replace("Nu", "{\\nu}").replace("Xi", "{\\xi}").replace("Pi", "{\\pi}").replace("VarRho", "{\\varrho}").replace("Rho", "{\\rho}")
				.replace("VarSigma", "{\\varsigma}").replace("Sigma", "{\\sigma}").replace("GAMMA", "{\\Gamma}").replace("DELTA", "{\\Delta}").replace("THETA", "{\\Theta}").replace("LAMBDA", "{\\Lambda}").replace("XI", "{\\Xi}").replace("PI", "{\\Pi}")
				.replace("SIGMA", "{\\Sigma}").replace("UPSILON", "{\\Upsilon}").replace("PHI", "{\\Phi}");
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
		result += "}{";
		if (rule.getCondition() != null) {
			rule.getCondition().accept(this);
		}
		result += "}{";
		rule.getAttributes().accept(this);
		result += "}" + endl;
	}

	@Override
	public void visit(Context cxt) {
		result += "\\kcontext";
		result += "{" + endl;
		cxt.getBody().accept(this);
		result += "}{";
		if (cxt.getCondition() != null) {
			cxt.getCondition().accept(this);
		}
		result += "}{";
		cxt.getAttributes().accept(this);
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
		String pattern = patternsVisitor.getPatterns().get(trm.getCons());
		if (pattern == null) {
			Production pr = DefinitionHelper.conses.get(trm.getCons());
			pr.accept(patternsVisitor);
			pattern = patternsVisitor.getPatterns().get(trm.getCons());
		}
		String regex = "\\{#\\d+\\}$";
		Pattern p = Pattern.compile(regex);
		if (parentParens && (pattern.indexOf("{#") == 0 
				|| p.matcher(pattern).matches())) {
			pattern = "(" + pattern + ")";
		}		
		int n = 1;
		LatexFilter termFilter = new LatexFilter();
		for (Term t : trm.getContents()) {
			termFilter.setResult("");
			regex = "\\{#\\d+\\}\\{#" + n + "\\}";
			p = Pattern.compile(regex);
			if (pattern.contains("{#" + n + "}{#") || p.matcher(pattern).matches()) {
				termFilter.setParentParens(true);				
			}
			t.accept(termFilter);
			pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
		}
		result += pattern;
	}

	@Override
	public void visit(Constant c) {
		result += "\\constant[" + StringUtil.latexify(c.getSort()) + "]{" + StringUtil.latexify(c.getValue()) + "}";
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
		if (comment.getType() == LiterateCommentType.LATEX) {
			result += "\\begin{kblock}[text]" + endl;
			result += comment.getValue();
			result += "\\end{kblock}" + endl;
		} else if (comment.getType() == LiterateCommentType.PREAMBLE) {
			preamble += comment.getValue();
		}
	}

	@Override
	public void visit(LiterateModuleComment comment) {
		if (comment.getType() == LiterateCommentType.LATEX) {
			result += "\\begin{kblock}[text]" + endl;
			result += comment.getValue();
			result += "\\end{kblock}" + endl;
		} else if (comment.getType() == LiterateCommentType.PREAMBLE) {
			preamble += comment.getValue();
		}
	}

	@Override
	public void visit(Attribute entry) {
		if (DefinitionHelper.isTagGenerated(entry.getKey()))
			return;
		if (DefinitionHelper.isParsingTag(entry.getKey()))
			return;
		if (entry.getKey().equals("latex"))
			return;
		if (entry.getKey().equals("html"))
			return;
		if (firstAttribute) {
			firstAttribute = false;
		} else {
			result += ", ";
		}
		result += "\\kattribute{" +
				StringUtil.latexify(entry.getKey()) +"}";
		String value = entry.getValue();
		if (!value.isEmpty()) {
			result += "(" + StringUtil.latexify(value) + ")";
		}
	}

	@Override
	public void visit(Attributes attributes) {
		firstAttribute = true;
		for (Attribute entry : attributes.getContents()) {
			entry.accept(this);
		}
	}
}
