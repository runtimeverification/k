package ro.uaic.info.fmse.html;

import java.util.HashMap;
import java.util.Map;
import java.util.List;

import ro.uaic.info.fmse.k.*;
import ro.uaic.info.fmse.k.LiterateComment.LiterateCommentType;
import ro.uaic.info.fmse.k.ProductionItem.ProductionType;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.utils.strings.StringUtil;
import ro.uaic.info.fmse.visitors.BasicVisitor;

public class HTMLFilter extends BasicVisitor {
	String endl = System.getProperty("line.separator");
	private String result = "";
	private String css = "";
	private String title = "";
	private boolean firstProduction = false;
	private Map<String, String> colors = new HashMap<String, String>();
//	private LatexPatternsVisitor patternsVisitor = new LatexPatternsVisitor();
	private boolean firstAttribute;

	/*public void setResult(String result) {
		this.result = result;
	}*/

	/*public void setPreamble(String preamble) {
		this.preamble = preamble;
	}

	public String getPreamble() {
		return preamble;
	}*/

	public String getResult() {
		
		String html = 
			"<!DOCTYPE html>" + endl + 
			"<html lang=\"en\">" + endl + 
			"<head>" + endl + 
			"	<title>" + title + "</title>" + endl + 
			"	<style>" + endl + 
			css + 
			"	</style>" + endl + 
			"	<meta charset=\"utf-8\" />" + endl + 
			"</head>" + endl + 
			"<body>" + endl;
		html += 
			result + 
			"</body>" + endl +
			"</html>" + endl;

		return html;
	}

	@Override
	public void visit(Definition def) {
		initializeCss();
		
		result += "<div>" + "Definition" + endl;
		super.visit(def);
		result += "Definition - END" + "</div>" + endl;
		title  = def.getMainModule();
	}

	@Override
	public void visit(Module mod) {
		if (mod.isPredefined())
			return;
		result += "<div>" + "Module " + mod.getName() + endl;
		//result += "\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl;
		super.visit(mod);
		result += "Module " + mod.getName() + "- END " + "<br />" + "<br />" + "</div>" + endl;
	}

	@Override
	public void visit(Syntax syn) {
		result += "<div>" + "SYNTAX" + endl;
		firstProduction = true;
		super.visit(syn);
		result += "</div>" + endl;
	}

	@Override
	public void visit(Sort sort) {
		result += "<span class =\"italic\">" + sort.getSort() + "</span>";
		/*result += "{\\nonTerminal{\\sort{" + StringUtil.latexify(sort.getSort()) + "}}}";*/
	}

	@Override
	public void visit(Production p) {
		if (firstProduction) {
			result += " ::= ";
			firstProduction = false;
		} else {
			result += "" + " | ";
		}
//		if (p.getItems().get(0).getType() != ProductionType.USERLIST && p.getAttributes().containsKey(Constants.CONS_cons_ATTR) && patternsVisitor.getPatterns().containsKey(p.getAttributes().get(Constants.CONS_cons_ATTR))) {
//			String pattern = patternsVisitor.getPatterns().get(p.getAttributes().get(Constants.CONS_cons_ATTR));
//			int n = 1;
//			HTMLFilter termFilter = new HTMLFilter();
//			for (ProductionItem pi : p.getItems()) {
//				if (pi.getType() != ProductionType.TERMINAL) {
//					termFilter.setResult("");
//					pi.accept(termFilter);
//					pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
//				}
//			}
//			result += pattern;
//		} else {
		//result += "<div>" + "Production" + endl;
		super.visit(p);
//		}
		p.getAttributes().accept(this);
		//result += "Production - END " + "</div>" + endl;
	}

	@Override
	public void visit(Terminal pi) {
		result += "<span>" + "\"" + pi.getTerminal() + "\"" + "</span>"  + endl;
		/*String terminal = pi.getTerminal();
		if (terminal.isEmpty())
			return;
		if (DefinitionHelper.isSpecialTerminal(terminal)) {
			result += StringUtil.latexify(terminal);
		} else {
			result += "\\terminal{" + StringUtil.latexify(terminal) + "}";
		}*/
	}

	@Override
	public void visit(UserList ul) {
		result += "<span class =\"italic\">" + "List(#" + ul.getSort() + ",\"" + ul.getSeparator() + "\") </span>"  + endl;
		//result += "List\\{" + StringUtil.latexify(ul.getSort()) + ", \\mbox{``}" + StringUtil.latexify(ul.getSeparator()) + "\\mbox{''}\\}";
	}

	@Override
	public void visit(Configuration conf) {
		result += "Configuration{";
		super.visit(conf);
		result += "}" + endl;
	}

	@Override
	public void visit(Cell c) {
		/*if (c.getElipses().equals("left")) {
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
		}*/
		result += "{" + StringUtil.latexify(c.getLabel()) + "}{";
		super.visit(c);
		result += "}" + endl;
	}

	public void visit(Collection col) {
		List<Term> contents = col.getContents();
		printList(contents, " -> ");
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
			result += "_";
		} else {
			result += "var";
		}
		if (var.getSort() != null) {
			result += "[" + var.getSort() + "]";
		}
		if (!var.getName().equals("_")) {
			result += " " + makeGreek(var.getName())+ " ";
		}
	}

	/*private String makeIndices(String str) {
		return str;
	}*/

	private String makeGreek(String name) {
		return name.replace("Alpha", "&alpha;").replace("Beta", "&beta;").replace("Gamma", "&gamma;").replace("Delta", "&delta;").replace("VarEpsilon", "&vepsilon;").replace("Epsilon", "&epsilon;").replace("Zeta", "&zeta;").replace("Eta", "&eta;")
				.replace("Theta", "&theta;").replace("Kappa", "&kappa;").replace("Lambda", "&lambda;").replace("Mu", "&mu;").replace("Nu", "&nu;").replace("Xi", "&xi;").replace("Pi", "&pi;").replace("VarRho", "&varrho;").replace("Rho", "&rho;")
				.replace("VarSigma", "&vsigma;").replace("Sigma", "&sigma;").replace("GAMMA", "&Gamma;").replace("DELTA", "&Delta;").replace("THETA", "&Theta;").replace("LAMBDA", "&Lambda;").replace("XI", "&Xi;").replace("PI", "&Pi;")
				.replace("SIGMA", "&Sigma;").replace("UPSILON", "&Upsilon;").replace("PHI", "&Phi;");
	}

	@Override
	public void visit(Empty e) {
		result += " <span class = \"bold\">&middot;</span> " + e.getSort() + " ";
	}

	@Override
	public void visit(Rule rule) {
		result += "<div> RULE";
		if (!rule.getLabel().equals("")) {
			result += "  [" + rule.getLabel() + "] ";
		}
		rule.getBody().accept(this);
		if (rule.getCondition() != null) {
			result += " when ";
			rule.getCondition().accept(this);
		}
		rule.getAttributes().accept(this);
		result += "</div>" + endl;
		//result += "\\krule";
		
		/*result += "{" + endl;
		rule.getBody().accept(this);
		result += "}{";*/
		
		/*result += "}{";
		rule.getAttributes().accept(this);
		result += "}" + endl;*/
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
		result += "HOLE";
	}

	@Override
	public void visit(Rewrite rew) {
		
		result += " ";
		rew.getLeft().accept(this);
		result += " => ";
		rew.getRight().accept(this);
		result += " ";
	}

	@Override
	public void visit(TermCons trm) {
//		String pattern = patternsVisitor.getPatterns().get("\"" + trm.getCons() + "\"");
//		if (pattern == null) {
//			Production pr = DefinitionHelper.conses.get("\"" + trm.getCons() + "\"");
//			pr.accept(patternsVisitor);
//			pattern = patternsVisitor.getPatterns().get("\"" + trm.getCons() + "\"");
//		}
//		int n = 1;
//		HTMLFilter termFilter = new HTMLFilter();
//		for (Term t : trm.getContents()) {
//			termFilter.setResult("");
//			t.accept(termFilter);
//			pattern = pattern.replace("{#" + n++ + "}", "{" + termFilter.getResult() + "}");
//		}
//		result += pattern;
		//result += "\\mbox{" + StringUtil.latexify(trm.toString()) + "}";
		result += trm.toString();
		if(trm.toString().isEmpty())
			result += ".";
	}

	@Override
	public void visit(Constant c) {
		result += c.getSort() + " " + c.getValue();
		//result += "\\constant[" + StringUtil.latexify(c.getSort()) + "]{" + StringUtil.latexify(c.getValue()) + "}";
	}

	@Override
	public void visit(MapItem mi) {
		mi.getKey().accept(this);
		//result += "\\mapsto";
		mi.getItem().accept(this);
	}

	@Override
	public void visit(KSequence k) {
		printList(k.getContents(), "ksequence ");

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
		printList(list.getContents(), "listofK");
	}

	@Override
	public void visit(LiterateDefinitionComment comment) {
		/*if (comment.getType() == LiterateCommentType.LATEX) {
			result += "\\begin{kblock}[text]" + endl;
			result += comment.getValue();
			result += "\\end{kblock}" + endl;
		} else if (comment.getType() == LiterateCommentType.PREAMBLE) {
			preamble += comment.getValue();
		}*/
	}

	@Override
	public void visit(LiterateModuleComment comment) {
		/*if (comment.getType() == LiterateCommentType.LATEX) {
			result += "\\begin{kblock}[text]" + endl;
			result += comment.getValue();
			result += "\\end{kblock}" + endl;
		} else if (comment.getType() == LiterateCommentType.PREAMBLE) {
			preamble += comment.getValue();
		}*/
	}

	@Override
	public void visit(Attribute entry) {
		if (DefinitionHelper.isTagGenerated(entry.getKey()))
			return;
		if (entry.getKey().equals("latex"))
			return;
		
		if (firstAttribute) {
			firstAttribute = false;
		} else {
			result += ", ";
		}
		result += entry.getKey();
		String value = entry.getValue();
		
		if (!value.isEmpty()) {
			result += "(" + value + ")";
		}
		

		
	}

	@Override
	public void visit(Attributes attributes) {
		if(!attributes.getContents().isEmpty()){
			result += " [ <span class =\"attribute\"> ";
			firstAttribute = true;
			for (Attribute entry : attributes.getContents()) {
				entry.accept(this);
			}
			result += "</span> ]";
		}
	}
	
	private void initializeCss(){
		css += ".bold" + endl
				+ "{" + endl
				+ "font-weight: bold;"+endl
				+ "}" + endl;
		css += ".italic" + endl
				+ "{" + endl
				+ "font-style: italic;"+endl
				+ "}" + endl;
		css += ".attribute" + endl
				+ "{" + endl
				+ "color: blue;"+endl
				+ "}" + endl;
				
	}
}
