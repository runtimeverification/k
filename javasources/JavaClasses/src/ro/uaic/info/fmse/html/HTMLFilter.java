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
		result += "</div>" + endl;
		title  = def.getMainModule();
	}

	@Override
	public void visit(Module mod) {
		if (mod.isPredefined())
			return;
		result += "<div>" + "Module " + mod.getName() + "<br/>" + endl;
		//result += "\\begin{module}{\\moduleName{" + StringUtil.latexify(mod.getName()) + "}}" + endl;
		super.visit(mod);
		result += "<br />" + "<br />" + "</div>" + endl;
	}

	@Override
	public void visit(Syntax syn) {
		result += "<table> <tr> <td> SYNTAX" + endl;
		firstProduction = true;
		super.visit(syn);
		result += "</table>" + endl;
	}

	@Override
	public void visit(Sort sort) {
		result += "<span class =\"italic\"> " + sort.getSort() + " </span>";
		/*result += "{\\nonTerminal{\\sort{" + StringUtil.latexify(sort.getSort()) + "}}}";*/
	}

	@Override
	public void visit(Production p) {
		if (firstProduction) {
			result += "</td><td> ::= </td> <td>";
			firstProduction = false;
		} else {
			result += "<tr> <td> </td> <td class = \"textCentered\"> |  </td> <td>";
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
		result += "</td> </tr>";
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
		result += "Configuration : <br />";
		super.visit(conf);
	}

	@Override
	public void visit(Cell c) {
		String blockClasses = "block";
		if (c.getElipses().equals("left")) {
			blockClasses += " left";
		} else if (c.getElipses().equals("right")) {
			blockClasses += " right";
		} /*else if (c.getElipses().equals("both")) {
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
		result += "<div class=\"cell\"> <div class=\"tab\">";
		result += "<span class = \"bold\">" + makeGreek(htmlify(c.getLabel())) + "</span> </div>";
		result += "<br />";
		result += "<div class=\"" + blockClasses + "\">";
		super.visit(c);
		result += "</div> </div>" + endl;
	}

	public void visit(Collection col) {
		List<Term> contents = col.getContents();
		printList(contents, "");
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
		result += " <span title=\""+ e.getSort()+"\" class = \"bold\"> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&middot;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;</span> ";
	}

	@Override
	public void visit(Rule rule) {
		result += "<div> RULE";
		if (!rule.getLabel().equals("")) {
			result += "  [" + rule.getLabel() + "] ";
		}
		result+="<div class=\"cell\"> ";
		rule.getBody().accept(this);
		result+="</div> ";
		if (rule.getCondition() != null) {
			result += " when ";
			rule.getCondition().accept(this);
		}
		rule.getAttributes().accept(this);
		result += "</div> <br />" + endl;
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
		
		result += "<div class=\"textCentered\"> <em>";
		rew.getLeft().accept(this);
		result += "</em> <hr class=\"reduce\"/> <em>";
		rew.getRight().accept(this);
		result += "</em> </div>";
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
		result += makeGreek(htmlify(trm.toString()));
		if(trm.toString().isEmpty())
			result += "&nbsp; &nbsp; &nbsp; .&nbsp; &nbsp; &nbsp; ";
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
			result += " [ <span class =\"attribute\"> ";
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
		firstAttribute = true;
		for (Attribute entry : attributes.getContents()) {
			entry.accept(this);
		}
		if(!firstAttribute)
			result += "</span> ]";
	
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
		css += "em" + endl
				+ "{" + endl
				+ "font-style: italic;"+endl
				+ "}" + endl;
		css += ".attribute" + endl
				+ "{" + endl
				+ "color: blue;"+endl
				+ "}" + endl;
		css += ".textCentered" + endl
				+ "{" + endl
				+ "text-align: center;"+endl
				+ "}" + endl;
		css += ".cell" + endl
				+ "{" + endl
				+ "display: inline-block;"+endl
				+ "vertical-align: top;"+endl
				+ "}" + endl;
		css += "hr.reduce" + endl
				+ "{" + endl
				+ "color: black;"+endl
				+ "background-color: black;"+endl
				+ "height: 3px;"+endl
				+ "}" + endl;
		css += "hr.reduce:after" + endl
				+ "{" + endl
				+ "width: 0;"+endl
				+ "height: 0;"+endl
				+ "border-left : 6px solid transparent;"+endl
				+ "border-right : 6px solid transparent;"+endl
				+ "border-top : 6px solid black;"+endl
				+ "position: absolute;"+endl
				+ "content: \"\";"+endl
				+ "}" + endl;
		css += ".tab" + endl
				+ "{" + endl
				+ "display: inline-block;"+endl
				+ "padding : 2px;"+endl
				+ "margin-left : 0;"+endl
				+ "border-top : 3px solid;"+endl
				+ "border-left : 3px solid;"+endl
				+ "border-right : 3px solid;"+endl
				+ "position: relative;"+endl
				+ "left: 30px;"+endl
				+ "top : 3px;"+endl
				+ "border-color :#008000;"+endl
				+ "background-color: #BEEEBE;"+endl
				+ "}" + endl;
		
		css += ".block" + endl
				+ "{" + endl
				+ "color : black;"+endl
				+ "border: 3px #008000;"+endl
				+ "background-color: #BEEEBE;"+endl
				+ "display: inline-block; "+endl
				+ "padding: 10px;"+endl
				+ "padding-left: 20px;"+endl
				+ "padding-right: 20px;"+endl
				+ "border-radius: 30px;"+endl
				+ "border-style: solid;"+endl
				+ "}" + endl;
		
		css += ".block.right" + endl
				+ "{" + endl
				+ "border-top-right-radius: 0px;"+endl
				+ "border-bottom-right-radius: 0px;"+endl
				+ "border-right-style: dotted;"+endl
				+ "}" + endl;
		
		css += ".block.left" + endl
				+ "{" + endl
				+ "border-top-left-radius: 0px;"+endl
				+ "border-bottom-left-radius: 0px;"+endl
				+ "border-left-style: dotted;"+endl
				+ "}" + endl;		
	}
	
	private String htmlify(String name) {
		return name.replace("<", "&lt;");
	}
}
