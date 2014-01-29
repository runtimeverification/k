package org.kframework.backend.kore;

import org.kframework.backend.BasicBackend;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.kil.*;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.loader.Context;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.Stopwatch;

import java.io.IOException;
import java.util.List;

public class KoreBackend extends BasicBackend {
  public KoreBackend(Stopwatch sw, Context context) {
    super(sw, context);
  }

  @Override
  public void run(Definition definition) throws IOException {
    KoreFilter filter = new KoreFilter(context);
    ToBuiltinTransformer oldFilter = new ToBuiltinTransformer(context);
    ToKAppTransformer newFilter = new ToKAppTransformer(context);
    
    try {
		definition.accept(oldFilter).accept(newFilter).accept(filter);
	} catch (TransformerException e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	}
    
    String output = filter.getResult();
    System.out.println("\n\n+++KORE+++\n");
    System.out.println(output);
/*
		FileUtil.save(context.dotk.getAbsolutePath() + "/def.k", unparsedText);

		FileUtil.save(GlobalSettings.outputDir + File.separator + FileUtil.stripExtension(GlobalSettings.mainFile.getName()) + ".unparsed.k", unparsedText);
*/
  }

  @Override
  public String getDefaultStep() {
    return "FirstStep";
  }
}

class KoreFilter extends UnparserFilter {

  KoreFilter(Context context) {
	  super(context);
  }
  
	KoreFilter(boolean inConfiguration, ColorSetting color, boolean addParentheses, org.kframework.kil.loader.Context context) {
		super(inConfiguration, color, addParentheses, false, context);
	}

	@Override
	public String getName() {
		return "KoreFilter";
	}
	
	/*
	  public void visit(ASTNode node) {
		    sb.write("(TODO:"+node.getClass().getName()+")");
		  }

		  public void visit(Term node) { visit((ASTNode)node); }
		  public void visit(ModuleItem node) { visit((ASTNode)node); }
		  public void visit(DefinitionItem node) { visit((ASTNode)node); }
		  public void visit(ParseError node) { visit((ASTNode)node); }
*/
	@Override
	public void visit(Definition node) {
		prepare(node);
		for (DefinitionItem di : node.getItems()) {
			di.accept(this);
		}
		postpare();
    }

  @Override
  public void visit(LiterateDefinitionComment node) {
	  prepare(node);
	  indenter.write("/*"+node.getType()+node.getValue()+"*/");
	  indenter.endLine();
	  postpare();
  }
  
  @Override
  public void visit(LiterateModuleComment node) {
	  prepare(node);
	  indenter.write("/*"+node.getType()+node.getValue()+"*/");
	  indenter.endLine();
	  postpare();
  }

  @Override
  public void visit(Sentence node) {
	  prepare(node);
	  indenter.write(node instanceof Configuration ? "configuration" :
              node instanceof org.kframework.kil.Context ? "context" :
              node instanceof Rule ? "rule" : null);
    if (!node.getLabel().isEmpty()) indenter.write(" ["+node.getLabel()+"]: ");
    node.getBody().accept(this);
    if (node.getRequires() != null) { indenter.write(" requires "); node.getRequires().accept(this); }
    if (node.getEnsures() != null) { indenter.write(" ensures "); node.getEnsures().accept(this); }
//TODO:    node.getAttributes().accept(this);
    indenter.endLine();
    postpare();
  }

  /*
  @Override
  public void visit(Rule node) { visit((Sentence)node); }
  
  @Override
  public void visit(org.kframework.kil.Context node) { visit((Sentence)node); }
  
  @Override
  public void visit(Configuration node) { visit((Sentence)node); }
*/

/*
  public void visit(PriorityExtended node) {
    visit((ASTNode)node);

    sb.append("syntax priorities");
    if (isVisited(node))
			return;
		for (PriorityBlockExtended pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);

	}

	public void visit(PriorityExtendedAssoc node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		for (KLabelConstant pb : node.getTags()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);

	}
*/
  
  /*
	public void visit(PriorityBlock node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		for (Production p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);

	}

	public void visit(PriorityBlockExtended node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		for (Term p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);

	}

	public void visit(Production node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		for (ProductionItem pi : node.getItems()) {
			pi.accept(this);
		}
		visit((ASTNode) node);

	}

	public void visit(ProductionItem node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		visit((ASTNode) node);
	}


	public void visit(Sort node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		visit((ProductionItem) node);

	}

	public void visit(Terminal node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		visit((ProductionItem) node);

	}

  
	public void visit(Lexical node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		visit((ProductionItem) node);

	}

	public void visit(UserList node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		visit((ProductionItem) node);

	}


	public void visit(Cell cell) {
		prepare(cell);
		String attributes = "";
		for (Entry<String, String> entry : cell.getCellAttributes().entrySet()) {
			if (entry.getKey() != "ellipses") {
				attributes += " " + entry.getKey() + "=\"" + entry.getValue() + "\"";
			}
		}
		String colorCode = "";
        Cell declaredCell = context.cells.get(cell.getLabel());
        if (declaredCell != null) {
            String declaredColor = declaredCell.getCellAttributes().get("color");
            if (declaredColor != null) {
                colorCode = ColorUtil.RgbToAnsi(ColorUtil.colors.get(declaredColor), color);
                sb.write(colorCode);
            }
        }

		sb.write("<" + cell.getLabel() + attributes + ">");
		if (inConfiguration && inTerm == 0) {
			sb.endLine();
			sb.indent(TAB);
		} else {
			if (cell.hasLeftEllipsis()) {
				sb.write("... ");
			} else {
				sb.write(" ");
			}
		}
		if (!colorCode.equals("")) {
			sb.write(ColorUtil.ANSI_NORMAL);
		}
		cell.getContents().accept(this);
		sb.write(colorCode);
		if (inConfiguration && inTerm == 0) {
			sb.endLine();
			sb.unindent();
		} else {
			if (cell.hasRightEllipsis()) {
				sb.write(" ...");
			} else {
				sb.write(" ");
			}
		}
		sb.write("</" + cell.getLabel() + ">");
		if (!colorCode.equals("")) {
			sb.write(ColorUtil.ANSI_NORMAL);
		}
		postpare();
	}

	public void visit(Collection node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		for (Term t : node.getContents()) {
			t.accept(this);
		}
		visit((Term) node);

	}
*/
	public void visit(Ambiguity node) {
          assert false : "Ambiguities not supported in Kore";
	}

	/*
	public void visit(Bag node) {
    visit((ASTNode)node);

		if (isVisited(node))
			return;
		visit((Collection) node);

	}

*/
  private void visitList(List<? extends ASTNode> nodes, String sep, String empty) {
    if (nodes.size() == 0) { this.indenter.write(empty); }
    else {
      for (int i = 0; i < nodes.size(); i++) {
        nodes.get(i).accept(this);
        if (i < nodes.size() - 1) { indenter.write(sep); }
      }
    }
  }

  	@Override
	public void visit(KSequence node) { 
		prepare(node);
		visitList(node.getContents(), " ~> ", ".K");
		postpare();
	}

  	@Override
	public void visit(org.kframework.kil.List node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

  	@Override
	public void visit(KList node) {
		prepare(node);
          visitList(node.getContents(), ", ", ".KList");
          postpare();
/*
if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

  	@Override
	public void visit(BoolBuiltin node) {
		prepare(node);
          this.indenter.write(node.value()); // TODO: true() vs #"true"()
          postpare();
	}

	@Override
	public void visit(IntBuiltin node) {
		prepare(node);
		this.indenter.write(node.value()); // TODO: true() vs #"true"()
          postpare();
	}

	@Override
	public void visit(StringBuiltin node) {
		prepare(node);
		this.indenter.write(node.value());
          postpare();
          // TODO: "abc" vs "abc"()
	}

/*
	public void visit(FreezerHole node) {
          sb.append("HOLE");
	}
*/
	@Override
	public void visit(KApp node) {
		prepare(node);
          node.getLabel().accept(this);
          this.indenter.write("(");

          if(node.getChild() instanceof KList && ((KList)node.getChild()).isEmpty()){
        	  
        	  this.indenter.write(".KList");
          } else {
        	  node.getChild().accept(this);
          }
          this.indenter.write(")");
          postpare();
	}

	@Override
	public void visit(KLabelConstant node) {
		prepare(node);
		this.indenter.write(node.getLabel().replaceAll("\\(", "'(").replaceAll("\\)", "')")); // TODO: escape the label
		postpare();
	}
/*
	public void visit(TermCons node) {
		prepare(node);
          visit(new KApp(KLabelConstant.of(node.getProduction().getKLabel(), context), new KList(node.getContents())));
          postpare();
	}
*/
	@Override
	public void visit(Variable node) {
		prepare(node);
		this.indenter.write(node.getName() + ":" + node.getSort());
          postpare();
	}
}
