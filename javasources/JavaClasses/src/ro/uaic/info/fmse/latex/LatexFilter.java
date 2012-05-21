package ro.uaic.info.fmse.latex;

import java.util.HashMap;
import java.util.Map;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.parsing.BasicVisitor;

public class LatexFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	private String result="";
	private boolean firstProduction = false;
	private Map<String,String> colors = new HashMap<String,String>();

	public void setResult(String result) {
		this.result = result;
	}

	public String getResult() {
		return result;
	}
	
	@Override
	public void visit(Definition def) {
		result += "\\begin{kdefinition}" + endl
		+ "\\maketitle" + endl;
		super.visit(def);
		result += "\\end{kdefinition}" + endl;
	}
	
	@Override
	public void visit(Module mod) {
		if (DefinitionHelper.isModulePredefined(mod.getName())) return;
		result += "\\begin{module}{\\moduleName{" + latexify(mod.getName()) + "}}" + endl;
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
		result += "{\\nonTerminal{\\sort{" + latexify(sort.getSort()) + "}}}";
	}
	
	@Override
	public void visit(Production p) {
		if (firstProduction) {
			result += "\\syntax{";
			firstProduction = false;
		} else {
			result += "\\syntaxCont{";
		}
		super.visit(p);
		result += "}{";
		printSentenceAttributes(p.getAttributes());
		result += "}";
	}
	
	@Override
	public void visit(Terminal pi) {
		String terminal = pi.getTerminal();
		if (terminal.isEmpty()) return;
		result += "\\terminal{" + latexify(terminal) + "}";
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
		result += "{" + latexify(c.getLabel()) + "}{";
		super.visit(c);
		result += "}" + endl;
	}
	
	
	@Override
	public void visit(Variable var) {
		if (var.getName().equals("_")) {
			result += "\\AnyVar";
		} else {
			result += "\\variable";
		}
		if (var.getSort() != null) {
			result += "[" + latexify(var.getSort()) + "]";
		}
		if (!var.getName().equals("_")) {
			result += "{" + latexify(var.getName()) + "}";
		}
	}
	
	@Override 
	public void visit(Empty e) {
		result += "\\dotCt{" + e.getSort() + "}";
	}
	
	
	private String latexify(String name) {
		return name.replace("{","\\{").replace("}", "\\}").replace("#", "\\#").replace("%", "\\%").replace(
				"$", "\\$").replace("&", "\\&").replace("~", "\\mbox{\\~{}}").replace("^", "\\mbox{\\^{}}");
	}

	private void printSentenceAttributes(Map<String, String> attributes) {
		boolean first = true;
		String value;
		for (Map.Entry<String, String> entry : attributes.entrySet()) {
			if (DefinitionHelper.isTagGenerated(entry.getKey())) continue;
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
