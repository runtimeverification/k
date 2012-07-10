package ro.uaic.info.fmse.html;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.List;
import java.util.Random;
import java.util.Vector;

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
	private Map<String, String> colors = new HashMap<String,String>();
	private HashSet<String> usedColors = new HashSet();
	private Map<String, String> cellColors = new HashMap<String,String>();

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
	
	public HTMLFilter() {
		initializeCss();
		createColors();
	}
	
	public void createColors(){
		colors.clear();
		colors.put("yellow" , ".yellow" + endl
				+ "{" + endl
				+ "border-color: #96915c;"+endl
				+ "background-color: #f7f7c5;"+endl
				+ "}" + endl);
		colors.put("orange" , ".orange" + endl
				+ "{" + endl
				+ "border-color: #804000;"+endl
				+ "background-color: #f6dec5;"+endl
				+ "}" + endl);
		colors.put("red" , ".red" + endl
				+ "{" + endl
				+ "border-color: #892d29;"+endl
				+ "background-color: #f5c4c4;"+endl
				+ "}" + endl);
		colors.put("green" , ".green" + endl
				+ "{" + endl
				+ "border-color: #008000;"+endl
				+ "background-color: #BEEEBE;"+endl
				+ "}" + endl);
		colors.put("LightSkyBlue" , ".LightSkyBlue" + endl
				+ "{" + endl
				+ "border-color: #44677d;"+endl
				+ "background-color: #d8e6ee;"+endl
				+ "}" + endl);
		colors.put("magenta" , ".magenta" + endl
				+ "{" + endl
				+ "border-color: #ad7a9b;"+endl
				+ "background-color: #edbeed;"+endl
				+ "}" + endl);
		colors.put("Orchid" , ".Orchid" + endl
				+ "{" + endl
				+ "border-color: #957294;"+endl
				+ "background-color: #e8d4e8;"+endl
				+ "}" + endl);
		colors.put("white" , ".white" + endl
				+ "{" + endl
				+ "border-color: #808080;"+endl
				+ "background-color: #f0f0f0;"+endl
				+ "}" + endl);
		colors.put("gray" , ".gray" + endl
				+ "{" + endl
				+ "border-color: #7c7c7c;"+endl
				+ "background-color: #d7d7d7;"+endl
				+ "}" + endl);
		colors.put("grey" , ".grey" + endl
				+ "{" + endl
				+ "border-color: #7c7c7c;"+endl
				+ "background-color: #d7d7d7;"+endl
				+ "}" + endl);
		colors.put("defaultColor" , ".defaultColor" + endl
				+ "{" + endl
				+ "border-color: #000000;"+endl
				+ "background-color: #FFFFFF;"+endl
				+ "}" + endl);
		
	}
	
	private String getRandomColor(){
		Random generator = new Random();
		Object[] keys = colors.keySet().toArray();
		return (String) keys[generator.nextInt(keys.length)];
	}
	
	private String getCellColor(String cellName){
		if(cellColors.get(cellName) != null)
			return cellColors.get(cellName);
		else
			return "defaultColor";
			
	}

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
		title  = def.getMainModule();
		result += "<span class=\"xlarge\">" + title + " </span> " + endl;
		result += "<div> <br /> </div>" + endl;
		super.visit(def);

	}

	@Override
	public void visit(Module mod) {
		if (mod.isPredefined())
			return;
		result += "<div>" + "MODULE <span class=\"large\">" + mod.getName() + "</span> <br /> <br />" + endl;
		super.visit(mod);
		result += "END MODULE </div>" + endl + "<br />" + endl;
	}

	@Override
	public void visit(Syntax syn) {
		result += "<table> <tr> <td> SYNTAX ";
		firstProduction = true;
		super.visit(syn);
		result += "</table>" + endl + "<br />" + endl;
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
		result += "</td> </tr>" + endl;
	}

	@Override
	public void visit(Terminal pi) {
		result += htmlify(pi.getTerminal()) +" ";
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
		result += "<span class =\"italic\">" + "List{#" + ul.getSort() + ",\"" + ul.getSeparator() + "\"} </span>"  + endl;
		//result += "List\\{" + StringUtil.latexify(ul.getSort()) + ", \\mbox{``}" + StringUtil.latexify(ul.getSeparator()) + "\\mbox{''}\\}";
	}

	@Override
	public void visit(Configuration conf) {
		result += "<div> CONFIGURATION : <br />";
		super.visit(conf);
		result += "</div> <br />" ;
	}

	@Override
	public void visit(Cell c) {
		String blockClasses = "block";
		String tabClasses = "tab";
		if (c.getElipses().equals("left")) {
			blockClasses += " left";
			tabClasses += " straightEdge";
		} else if (c.getElipses().equals("right")) {
			blockClasses += " right";
			tabClasses += " curvedEdge";
		} else if (c.getElipses().equals("both")) {
			blockClasses += " left right";
			tabClasses += " straightEdge";
		} else {
			tabClasses += " curvedEdge";
		}
		if (c.getAttributes().containsKey("color") && colors.containsKey(c.getAttributes().get("color"))) {
			cellColors.put(c.getLabel(), c.getAttributes().get("color"));
		}

		String color = getCellColor(makeGreek(htmlify(c.getLabel())));
		String cellName = makeGreek(htmlify(c.getLabel()));
		
		if(usedColors.add(color))
			css+= colors.get(color);
		
		result += "<div class=\"cell\"> <div class=\"" + tabClasses + " " + color + "\">";
		result += "<span class = \"bold\">" + cellName + "</span> </div>";
		result += "<br />";
		result += "<div class=\"" + blockClasses + " " + color + "\" ";
		if(cellName.length() > 5) {
			double mw = Math.floor(cellName.length() * 0.7 *10 +0.5 )/10.0;
			result += "style=\"min-width:"+mw+"em\"";
		}
			
		result += "> <div class=\"center\">";
		super.visit(c);
		result += "</div> </div> </div>" + endl;
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
		result +="<span ";
		if (var.getSort() != null) {
			result += "title =\"" + var.getSort() + "\"";
		}
		result+=">" + makeGreek(var.getName());
		
		/*if (var.getName().equals("_")) {
			result += "_";
		} else {
			result += "var " + makeGreek(var.getName())+ " ";
		}*/
		result+=" </span> ";
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
		result += " <span title=\""+ e.getSort()+"\" class = \"bold\"> &nbsp;&nbsp;&middot;&nbsp;&nbsp;</span> ";
	}

	@Override
	public void visit(Rule rule) {
		result += "<div> <span ";
		if (!rule.getLabel().equals("")) {
			result += "title =\"Rule Label: " + rule.getLabel() + "\"";
		}
		result += "> RULE </span>";
		result += "<div class=\"cell\"> ";
		rule.getBody().accept(this);
		result += "</div> ";
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
		result += "<div> CONTEXT ";
		cxt.getBody().accept(this);
		if (cxt.getCondition() != null) {
			result += " when ";
			cxt.getCondition().accept(this);
		}
		cxt.getAttributes().accept(this);
		result += "</div> <br />" + endl;
	}

	@Override
	public void visit(Hole hole) {
		result += "&#9633;";
	}

	@Override
	public void visit(Rewrite rew) {
		
		result += "<div class=\"textCentered\"> <em> ";
		rew.getLeft().accept(this);
		result += "</em> <hr class=\"reduce\"/> <em> ";
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
		
		/*result += makeGreek(htmlify(trm.toString()));
		if(trm.toString().isEmpty())
			result += "&nbsp; &nbsp; &nbsp; &middot; &nbsp; &nbsp; &nbsp; ";*/
		boolean empty = true;
		Production pr = trm.getProduction();

		if (pr.getItems().size() > 0) {
			if (pr.getItems().get(0).getType() == ProductionType.USERLIST) {
				String separator = ((UserList) pr.getItems().get(0)).getSeparator();
				trm.getContents().get(0).accept(this);
				result += " " + separator + " ";
				trm.getContents().get(1).accept(this);
				result += " ";
				empty = false;
			} else
				for (int i = 0, j = 0; i < pr.getItems().size(); i++) {
					ProductionItem pi = pr.getItems().get(i);
					if (pi.getType() == ProductionType.TERMINAL) {
						pi.accept(this);
						empty = false;
					} else if (pi.getType() == ProductionType.SORT) {
						Term t = trm.getContents().get(j++);
						t.accept(this);	
						empty = false;
					}
				}
		}
		if(empty)
			result += "&nbsp; &nbsp; &middot; &nbsp; &nbsp;";
	}

	@Override
	public void visit(Constant c) {
		result += "<span title =\"" + c.getSort() + "\"> " + c.getValue() + " </span> ";
		//result += "\\constant[" + StringUtil.latexify(c.getSort()) + "]{" + StringUtil.latexify(c.getValue()) + "}";
	}

	@Override
	public void visit(MapItem mi) {
		mi.getKey().accept(this);
		result += "<span text-size=\"large\"> &#x21a6; </span>";
		mi.getItem().accept(this);
	}

	@Override
	public void visit(KSequence k) {
		printList(k.getContents(), "&#x219d; ");

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
		printList(list.getContents(), "<span class=\"bold\">, </span>");
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
		if (DefinitionHelper.isParsingTag(entry.getKey()))
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
		
		css += ".large" + endl
				+ "{" + endl
				+ "font-size: large;"+endl
				+ "}" + endl;
		
		css += ".xlarge" + endl
				+ "{" + endl
				+ "font-size: x-large;"+endl
				+ "}" + endl;
		
		css += ".attribute" + endl
				+ "{" + endl
				+ "color: blue;"+endl
				+ "}" + endl;
		
		css += ".center" + endl
				+ "{" + endl
				+ "text-align: center;"+endl
				+ "}" + endl;
		
		css += ".textCentered" + endl
				+ "{" + endl
				+ "text-align: center;"+endl
				+ "display: inline-block;"+endl
				+ "vertical-align: top;"+endl
				+ "min-width: 20px;"+endl
				+ "}" + endl;
		
		css += ".cell" + endl
				+ "{" + endl
				+ "display: inline-block;"+endl
				+ "vertical-align: top;"+endl
				+ "text-align:left;" +endl
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
				+ "text-align: left;"+endl
				+ "}" + endl;
		
		css += ".tab.curvedEdge" + endl
				+ "{" + endl
				+ "position: relative;"+endl
				+ "left: 30px;"+endl
				+ "top : 3px;"+endl
				+ "}" + endl;
		
		css += ".tab.straightEdge" + endl
				+ "{" + endl
				+ "position: relative;"+endl
				+ "left: 8px;"+endl
				+ "top : 3px;"+endl
				+ "}" + endl;
		
		css += ".block" + endl
				+ "{" + endl
				+ "color : black;"+endl
				+ "border-width: 3px;"+endl
				+ "display: inline-block; "+endl
				+ "padding: 10px;"+endl
				+ "padding-left: 20px;"+endl
				+ "padding-right: 20px;"+endl
				+ "border-radius: 30px;"+endl
				+ "border-style: solid;"+endl
				+ "min-width: 60px;"+endl
				+ "text-align: left;"+endl
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
