package org.kframework.html;

import java.util.HashMap;
import java.util.Map;

import org.kframework.k.*;
import org.kframework.visitors.BasicVisitor;


public class HTMLPatternsVisitor extends BasicVisitor {
	public enum HTMLPatternType {
		LATEX, HTML, DEFAULT
	};
	
	private Map<String,String> patterns = new HashMap<String,String>();
	private Map<String,HTMLPatternType> type = new HashMap<String,HTMLPatternType>();
	
	String pattern = "";
	int nonTerm;
	boolean prevNonTerm;
	
	public void setPatterns(Map<String,String> patterns) {
		this.patterns = patterns;
	}


	public Map<String,String> getPatterns() {
		return patterns;
	}

	public HTMLPatternType getPatternType(String cons){
		if(type.containsKey(cons))
			return type.get(cons);
		else
			return null;
	}

	@Override 
	public void visit(Production p) {
		if (!p.getAttributes().containsKey("cons")) {
			return;
		}
		if(p.getAttributes().containsKey("latex") || p.getAttributes().containsKey("html")) {
			if (p.getAttributes().containsKey("latex")) {
				
				pattern = p.getAttributes().get("latex");
				pattern = pattern.replace("\\\\", "\\");
				patterns.put(p.getAttributes().get("cons"), pattern);
				type.put(p.getAttributes().get("cons"), HTMLPatternType.LATEX);
				
			}
			if (p.getAttributes().containsKey("html")) {
				
				pattern = p.getAttributes().get("html");
				pattern = pattern.substring(1, pattern.length()-1).replace("\\\\", "\\");
				patterns.put(p.getAttributes().get("cons"), pattern);
				type.put(p.getAttributes().get("cons"), HTMLPatternType.HTML);
				
			} 
		} else {
			type.put(p.getAttributes().get("cons"), HTMLPatternType.DEFAULT);
			//super.visit(p);
		}
		
	}


	@Override
	public void visit(Sort sort) {
		/*if (prevNonTerm) pattern += "\\mathrel{}";
		pattern += "{#" + nonTerm++ + "}";
		prevNonTerm = true;*/
	}
	
	
	@Override
	public void visit(UserList sort) {
		//Should be only nonterminal in a production, so prevNonTerm has no effect
		/*pattern += "{#" + nonTerm++ + "}";
		pattern += "\\mathpunct{\\terminalNoSpace{" + StringUtil.latexify(sort.getSeparator()) + "}}";
		pattern += "{#" + nonTerm++ + "}";*/
	}
	
	
	@Override
	public void visit(Terminal pi) {
		/*String terminal = pi.getTerminal();
		if (terminal.isEmpty()) return;
		if (DefinitionHelper.isSpecialTerminal(terminal)) {
			pattern += StringUtil.latexify(terminal);
		} else {
			pattern += "\\terminal{" + StringUtil.latexify(terminal) + "}";
		}
		prevNonTerm = false;*/
	}

}
