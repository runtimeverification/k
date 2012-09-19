package org.kframework.backend.latex;

import java.util.HashMap;
import java.util.Map;

import org.kframework.kil.*;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.utils.strings.StringUtil;


public class LatexPatternsVisitor extends BasicVisitor {
	private Map<String, String> patterns = new HashMap<String, String>();
	String pattern = "";
	int nonTerm;
	boolean prevNonTerm;

	public void setPatterns(Map<String, String> patterns) {
		this.patterns = patterns;
	}

	public Map<String, String> getPatterns() {
		return patterns;
	}

	@Override
	public void visit(Production p) {
		if (!p.getAttributes().containsKey("cons")) {
			return;
		}
		if (p.getAttributes().containsKey("latex")) {
			pattern = p.getAttributes().get("latex");
		} else {
			pattern = "";
			nonTerm = 1;
			prevNonTerm = false;
			super.visit(p);
		}
		patterns.put(p.getAttributes().get("cons"), pattern);
	}

	@Override
	public void visit(Sort sort) {
		if (prevNonTerm)
			pattern += "\\mathrel{}";
		pattern += "{#" + nonTerm++ + "}";
		prevNonTerm = true;
	}

	@Override
	public void visit(UserList sort) {
		// Should be only nonterminal in a production, so prevNonTerm has no effect
		pattern += "{#" + nonTerm++ + "}";
		pattern += "\\mathpunct{\\terminalNoSpace{" + StringUtil.latexify(sort.getSeparator()) + "}}";
		pattern += "{#" + nonTerm++ + "}";
	}

	@Override
	public void visit(Terminal pi) {
		String terminal = pi.getTerminal();
		if (terminal.isEmpty())
			return;
		if (DefinitionHelper.isSpecialTerminal(terminal)) {
			pattern += StringUtil.latexify(terminal);
		} else {
			pattern += "\\terminal{" + StringUtil.latexify(terminal) + "}";
		}
		prevNonTerm = false;
	}

	// Premature optimization :-)

	@Override
	public void visit(Rule node) {
		return;
	}

	@Override
	public void visit(Configuration node) {
		return;
	}

	@Override
	public void visit(Context node) {
		return;
	}
}
