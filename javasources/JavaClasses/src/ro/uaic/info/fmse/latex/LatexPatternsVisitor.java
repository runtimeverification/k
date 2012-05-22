package ro.uaic.info.fmse.latex;

import java.util.HashMap;
import java.util.Map;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.BasicVisitor;

public class LatexPatternsVisitor extends BasicVisitor {
	private Map<String,String> patterns = new HashMap<String,String>();
	String pattern = "";
	int nonTerm;
	boolean prevNonTerm = false;
	
	public void setPatterns(Map<String,String> patterns) {
		this.patterns = patterns;
	}


	public Map<String,String> getPatterns() {
		return patterns;
	}


	@Override 
	public void visit(Production p) {
		if (!p.getAttributes().containsKey("cons")) {
			return;
		}		
		if (p.getAttributes().containsKey("latex")) {
			pattern = p.getAttributes().get("latex");
			pattern = pattern.substring(1, pattern.length()-1);
		} else {
			pattern = ""; nonTerm = 1;
			super.visit(p);
		}
		patterns.put(p.getAttributes().get("cons"), pattern);
	}


	@Override
	public void visit(Sort sort) {
		if (prevNonTerm) pattern += "\\mathrel{}";
		pattern += "{#" + nonTerm++ + "}";
		prevNonTerm = true;
	}
	
	
	@Override
	public void visit(UserList sort) {
		if (prevNonTerm) pattern += "\\mathrel{}";
		pattern += "{#" + nonTerm++ + "}";
		prevNonTerm = true;
	}
	
	
	@Override
	public void visit(Terminal pi) {
		String terminal = pi.getTerminal();
		if (terminal.isEmpty()) return;
		if (DefinitionHelper.isSpecialTerminal(terminal)) {
			pattern += DefinitionHelper.latexify(terminal);
		} else {
			pattern += "\\terminal{" + DefinitionHelper.latexify(terminal) + "}";
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
