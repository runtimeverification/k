package org.kframework.backend.latex;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.kframework.backend.BackendFilter;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.LiterateComment.LiterateCommentType;
import org.kframework.kil.loader.*;
import org.kframework.utils.StringUtil;

public class LatexFilter extends BackendFilter {
	public LatexFilter(org.kframework.kil.loader.Context context) {
		super(context);
	}

	String endl = System.getProperty("line.separator");
	private StringBuilder preamble = new StringBuilder();
	private boolean firstProduction = false;
	private boolean terminalBefore = false;
	private Map<String, String> colors = new HashMap<String, String>();
	private LatexPatternsVisitor patternsVisitor = new LatexPatternsVisitor(context);
	private boolean firstAttribute;
	private boolean hasTitle = false;

	public LinkedList<Boolean> getWantParens() {
		return wantParens;
	}

	private LinkedList<Boolean> wantParens = new LinkedList<Boolean>();
	{
		wantParens.push(Boolean.TRUE);
	}

	// private boolean termComment;

	public void setResult(StringBuilder result) {
		this.result = result;
	}

	public void setPreamble(StringBuilder preamble) {
		this.preamble = preamble;
	}

	public StringBuilder getPreamble() {
		return preamble;
	}

	@Override
	public void visit(Definition def) {
		def.accept(patternsVisitor);
		result.append("\\begin{kdefinition}" + endl + "\\maketitle" + endl);
		super.visit(def);
		result.append("\\end{kdefinition}" + endl);
		if (!hasTitle) {
			preamble.append("\\title{" + def.getMainModule() + "}" + endl);
			hasTitle = true;
		}
	}

    @Override
    public void visit(PriorityExtended node) {
        return;
    }

    @Override
    public void visit(PriorityExtendedAssoc node) {
        return;
    }

    @Override
	public void visit(Module mod) {
		if (mod.isPredefined())
			return;
		result.append("\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl);
		super.visit(mod);
		result.append("\\end{module}" + endl);
	}

	@Override
	public void visit(Syntax syn) {
		result.append(endl + "\\begin{syntaxBlock}");
		firstProduction = true;
		super.visit(syn);
		result.append(endl + "\\end{syntaxBlock}" + endl);
	}

	@Override
	public void visit(Sort sort) {
		result.append("{\\nonTerminal{\\sort{" + StringUtil.latexify(sort.getName()) + "}}}");
                terminalBefore = false;
	}

	@Override
	public void visit(Production p) {
		if (firstProduction) {
			result.append("\\syntax{");
			firstProduction = false;
		} else {
			result.append("\\syntaxCont{");
		}
		if (!(p.getItems().get(0) instanceof UserList) && p.containsAttribute(Constants.CONS_cons_ATTR)
				&& patternsVisitor.getPatterns().containsKey(p.getAttribute(Constants.CONS_cons_ATTR))) {
			String pattern = patternsVisitor.getPatterns().get(p.getAttribute(Constants.CONS_cons_ATTR));
			int n = 1;
			LatexFilter termFilter = new LatexFilter(context);
			for (ProductionItem pi : p.getItems()) {
				if (!(pi instanceof Terminal)) {
					termFilter.setResult(new StringBuilder());
					pi.accept(termFilter);
					pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
				}
			}
			result.append(pattern);
		} else {
			super.visit(p);
		}
		result.append("}{");
		p.getAttributes().accept(this);
		result.append("}");
	}

	@Override
	public void visit(Terminal pi) {
		String terminal = pi.getTerminal();
		if (terminal.isEmpty())
			return;
		if (context.isSpecialTerminal(terminal)) {
			result.append(StringUtil.latexify(terminal));
		} else {
                  if (terminalBefore) result.append("{}");
			result.append("\\terminal{" + StringUtil.latexify(terminal) + "}");
		}
                terminalBefore = true;
	}

	@Override
	public void visit(UserList ul) {
		result.append("List\\{");
		new Sort(ul.getSort()).accept(this);
		result.append(", \\mbox{``}" + StringUtil.latexify(ul.getSeparator()) + "\\mbox{''}\\}");
                terminalBefore = false;
	}

        @Override
        public void visit(Lexical t) {
                result.append("Token\\{");
                result.append("\\mbox{``}" + StringUtil.latexify(t.getLexicalRule()) +  "\\mbox{''}\\}");
        }

	@Override
	public void visit(Configuration conf) {
		result.append("\\kconfig{");
		super.visit(conf);
		result.append("}" + endl);
	}

	@Override
	public void visit(Cell c) {
		wantParens.push(Boolean.FALSE);
		Ellipses ellipses = c.getEllipses();
		if (ellipses == Ellipses.LEFT) {
			result.append("\\ksuffix");
		} else if (ellipses == Ellipses.RIGHT) {
			result.append("\\kprefix");
		} else if (ellipses == Ellipses.BOTH) {
			result.append("\\kmiddle");
		} else {
			result.append("\\kall");
		}
		if (c.getCellAttributes().containsKey("color")) {
			colors.put(c.getLabel(), c.getCellAttributes().get("color"));
		}
		if (colors.containsKey(c.getLabel())) {
			result.append("[" + colors.get(c.getLabel()) + "]");
		}
		result.append("{" + StringUtil.latexify(c.getLabel() + StringUtil.emptyIfNull(c.getCellAttributes().get("multiplicity"))) + "}{");
		super.visit(c);
		result.append("}" + endl);
		wantParens.pop();
	}

	public void visit(Collection col) {
		final boolean parens = wantParens.peek();
		final boolean hasBR = containsBR(col);
        if (col.isEmpty()) {
            printEmpty(col.getSort());
            return;
        }
		if (hasBR) {
			if (parens) result.append("\\left(");
			result.append("\\begin{array}{@{}c@{}}");
		}
		List<Term> contents = col.getContents();
		printList(contents, "\\mathrel{}");
		if (hasBR) {
			result.append("\\end{array}");
			if (parens) result.append("\\right)");
		}
	}

	private boolean containsBR(Collection col) {
		for (Term t : col.getContents()) {
			if (t instanceof TermComment) {
				return true;
			}
		}
		return false;
	}

	private void printList(List<Term> contents, String str) {
		// result.append("\\begin{array}{l}");
		boolean first = true;
		for (Term trm : contents) {
			if (first) {
				first = false;
			} else {
				result.append(str);
			}
			trm.accept(this);
		}
		// result.append("\\end{array}");
	}

	public void visit(TermComment tc) {
		// termComment = true;
		result.append("\\\\");
		super.visit(tc);
	}

	@Override
	public void visit(Variable var) {
		if (var.getName().equals(MetaK.Constants.anyVarSymbol)) {
			result.append("\\AnyVar");
		} else {
			result.append("\\variable");
		}
		if (var.getSort() != null) {
			result.append("[" + StringUtil.latexify(var.getSort()) + "]");
		}
		if (!var.getName().equals(MetaK.Constants.anyVarSymbol)) {
			result.append("{" + makeIndices(makeGreek(StringUtil.latexify(var.getName()))) + "}");
		}
	}

	private String makeIndices(String str) {
		return str;
	}

	private String makeGreek(String name) {
		return name.replace("Alpha", "{\\alpha}").replace("Beta", "{\\beta}").replace("Gamma", "{\\gamma}").replace("Delta", "{\\delta}").replace("VarEpsilon", "{\\varepsilon}")
				.replace("Epsilon", "{\\epsilon}").replace("Zeta", "{\\zeta}").replace("Eta", "{\\eta}").replace("Theta", "{\\theta}").replace("Kappa", "{\\kappa}").replace("Lambda", "{\\lambda}")
				.replace("Mu", "{\\mu}").replace("Nu", "{\\nu}").replace("Xi", "{\\xi}").replace("Pi", "{\\pi}").replace("VarRho", "{\\varrho}").replace("Rho", "{\\rho}")
				.replace("VarSigma", "{\\varsigma}").replace("Sigma", "{\\sigma}").replace("GAMMA", "{\\Gamma}").replace("DELTA", "{\\Delta}").replace("THETA", "{\\Theta}")
				.replace("LAMBDA", "{\\Lambda}").replace("XI", "{\\Xi}").replace("PI", "{\\Pi}").replace("SIGMA", "{\\Sigma}").replace("UPSILON", "{\\Upsilon}").replace("PHI", "{\\Phi}");
	}

	@Override
	public void visit(Empty e) {
        printEmpty(e.getSort());
    }

    private void printEmpty(String sort) {
        result.append("\\dotCt{" + sort + "}");
    }

    @Override
	public void visit(Rule rule) {
		// termComment = false;
		result.append("\\krule");
		if (!"".equals(rule.getLabel())) {
			result.append("[" + rule.getLabel() + "]");
		}
		result.append("{" + endl);
		rule.getBody().accept(this);
		result.append("}{");
		if (rule.getRequires() != null) {
			rule.getRequires().accept(this);
		}
		result.append("}{");
		if (rule.getEnsures() != null) {
			rule.getEnsures().accept(this);
		}
		result.append("}{");
		rule.getAttributes().accept(this);
		result.append("}");
		result.append("{");
		// if (termComment) result.append("large");
		result.append("}");
		result.append(endl);
	}

	@Override
	public void visit(org.kframework.kil.Context cxt) {
		result.append("\\kcontext");
		result.append("{" + endl);
		cxt.getBody().accept(this);
		result.append("}{");
		if (cxt.getRequires() != null) {
			cxt.getRequires().accept(this);
		}
		result.append("}{");
		if (cxt.getEnsures() != null) {
			cxt.getEnsures().accept(this);
		}
		result.append("}{");
		cxt.getAttributes().accept(this);
		result.append("}" + endl);
	}

	@Override
	public void visit(Hole hole) {
		result.append("\\khole{}");
	}

	@Override
	public void visit(Rewrite rew) {
		wantParens.push(Boolean.TRUE);
		result.append("\\reduce{");
		rew.getLeft().accept(this);
		result.append("}{");
		rew.getRight().accept(this);
		result.append("}");
		wantParens.pop();
	}

	@Override
	public void visit(Bracket trm) {
		if (trm.getContent() instanceof Rewrite)
			super.visit(trm);
		else {
			String pattern = getBracketPattern(trm);
			LatexFilter termFilter = new LatexFilter(context);
			termFilter.getWantParens().push(Boolean.FALSE);
			trm.getContent().accept(termFilter);
			pattern = pattern.replace("{#1}", "{" + termFilter.getResult() + "}");
			result.append(pattern);
		}
	}

	private String getBracketPattern(Bracket trm) {
		return "\\left({#1}\\right)";
	}

	@Override
	public void visit(TermCons trm) {
		String pattern = patternsVisitor.getPatterns().get(trm.getCons());
		if (pattern == null) {
			Production pr = context.conses.get(trm.getCons());
			pr.accept(patternsVisitor);
			pattern = patternsVisitor.getPatterns().get(trm.getCons());
		}
		int n = 1;
		LatexFilter termFilter = new LatexFilter(context);
		for (Term t : trm.getContents()) {
			termFilter.setResult(new StringBuilder());
			t.accept(termFilter);
			pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
		}
		result.append(pattern);
	}

        @Override
        public void visit(KLabelConstant c) {
                result.append(StringUtil.latexify(c.getLabel()));
        }

	@Override
	public void visit(Token t) {
		result.append("\\constant[" + StringUtil.latexify(t.tokenSort()) + "]{" + StringUtil.latexify(t.value()) + "}");
	}

	@Override
	public void visit(MapItem mi) {
		mi.getKey().accept(this);
		result.append("\\mapsto");
		mi.getItem().accept(this);
	}

	@Override
	public void visit(KSequence k) {
        if (k.getContents().isEmpty()) printEmpty(KSort.K.name());
		else printList(k.getContents(), "\\kra");

	}

	@Override
	public void visit(KApp app) {
		if (app.getLabel() instanceof Token) {
			result.append("\\constant[" + StringUtil.latexify(((Token)app.getLabel()).tokenSort()) + "]{" + StringUtil.latexify(((Token)app.getLabel()).value()) + "}");
		} else {
			app.getLabel().accept(this);
			result.append("(");
			app.getChild().accept(this);
			result.append(")");
		}
	}

	@Override
	public void visit(KList list) {
		printList(list.getContents(), "\\kcomma");
	}

	@Override
	public void visit(LiterateDefinitionComment comment) {
		if (comment.getType() == LiterateCommentType.LATEX) {
			result.append("\\begin{kblock}[text]" + endl);
			result.append(comment.getValue());
			result.append("\\end{kblock}" + endl);
		} else if (comment.getType() == LiterateCommentType.PREAMBLE) {
			preamble.append(comment.getValue());
			if (comment.getValue().contains("\\title{")) {
				hasTitle = true;
			}
		}
	}

	@Override
	public void visit(LiterateModuleComment comment) {
		if (comment.getType() == LiterateCommentType.LATEX) {
			result.append("\\begin{kblock}[text]" + endl);
			result.append(comment.getValue());
			result.append("\\end{kblock}" + endl);
		} else if (comment.getType() == LiterateCommentType.PREAMBLE) {
			preamble.append(comment.getValue());
			if (comment.getValue().contains("\\title{")) {
				hasTitle = true;
			}
		}
	}

	@Override
	public void visit(Attribute entry) {
		if (Constants.GENERATED_LOCATION.equals(entry.getLocation()))
			return;
		if (context.isTagGenerated(entry.getKey()))
			return;
		if (context.isParsingTag(entry.getKey()))
			return;
		if (entry.getKey().equals("latex"))
			return;
		if (entry.getKey().equals("html"))
			return;
		if (firstAttribute) {
			firstAttribute = false;
		} else {
			result.append(", ");
		}
		result.append("\\kattribute{" + StringUtil.latexify(entry.getKey()) + "}");
		String value = entry.getValue();
		if (!value.isEmpty()) {
			result.append("(" + StringUtil.latexify(value) + ")");
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
