package org.kframework.backend.kore;

import org.kframework.backend.BasicBackend;
import org.kframework.kil.*;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.loader.Context;
import org.kframework.utils.Stopwatch;
import org.kframework.utils.file.FileUtil;
import org.kframework.utils.general.GlobalSettings;

import java.io.File;
import java.io.IOException;
import java.util.List;

public class KoreBackend extends BasicBackend {
  public KoreBackend(Stopwatch sw, Context context) {
    super(sw, context);
  }

  @Override
  public void run(Definition definition) throws IOException {
    KoreFilter filter = new KoreFilter(context);
    definition.accept(filter);
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

class KoreFilter implements Visitor {
  StringBuilder sb = new StringBuilder();
  Context context;

  KoreFilter(Context context) { this.context = context; }

	@Override
	public String getName() {
		return "KoreFilter";
	}

  public String getResult() { return sb.toString(); }

  public void visit(ASTNode node) {
    sb.append("(TODO:"+node.getClass().getName()+")");
  }

  public void visit(Term node) { visit((ASTNode)node); }
  public void visit(ModuleItem node) { visit((ASTNode)node); }
  public void visit(DefinitionItem node) { visit((ASTNode)node); }
  public void visit(ParseError node) { visit((ASTNode)node); }


  public void visit(Definition node) {
    for (DefinitionItem di : node.getItems()) {
      di.accept(this);
    }
  }

  public void visit(LiterateDefinitionComment node) {
    sb.append("/*"+node.getType()+node.getValue()+"*/\n");
  }

  public void visit(Module node) {
    sb.append("module "+node.getName()+"\n");
    for (ModuleItem mi : node.getItems()) {
      mi.accept(this);
    }
    sb.append("endmodule\n");
  }

  public void visit(Require node) {
    sb.append("require "+node.getValue()+"\n");
  }

  public void visit(Import node) {
    sb.append("imports "+node.getName()+"\n");
  }

  public void visit(LiterateModuleComment node) {
    sb.append("/*"+node.getType()+node.getValue()+"*/\n");
  }

  public void visit(Sentence node) {
    sb.append(node instanceof Configuration ? "configuration" :
              node instanceof org.kframework.kil.Context ? "context" :
              node instanceof Rule ? "rule" : null);
    if (!node.getLabel().isEmpty()) sb.append(" ["+node.getLabel()+"]: ");
    node.getBody().accept(this);
    if (node.getRequires() != null) { sb.append(" requires "); node.getRequires().accept(this); }
    if (node.getEnsures() != null) { sb.append(" ensures "); node.getEnsures().accept(this); }
//TODO:    node.getAttributes().accept(this);
    sb.append("\n");
  }

  public void visit(Rule node) { visit((Sentence)node); }
  public void visit(org.kframework.kil.Context node) { visit((Sentence)node); }
  public void visit(Configuration node) { visit((Sentence)node); }

  public void visit(Syntax node) {
    sb.append("syntax "+node.getSort().getName()+" := ");
    for (PriorityBlock pb : node.getPriorityBlocks()) {
      pb.accept(this);
      sb.append("\n> ");
    }
    sb.setLength(sb.length() - 2);
  }

  public void visit(PriorityExtended node) {
    visit((ASTNode)node);
/*
    sb.append("syntax priorities");
    if (isVisited(node))
			return;
		for (PriorityBlockExtended pb : node.getPriorityBlocks()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
*/
	}

	public void visit(PriorityExtendedAssoc node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (KLabelConstant pb : node.getTags()) {
			pb.accept(this);
		}
		visit((ModuleItem) node);
*/
	}

	public void visit(PriorityBlock node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (Production p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);
*/
	}

	public void visit(PriorityBlockExtended node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (Term p : node.getProductions()) {
			p.accept(this);
		}
		visit((ASTNode) node);
*/
	}

	public void visit(Production node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (ProductionItem pi : node.getItems()) {
			pi.accept(this);
		}
		visit((ASTNode) node);
*/
	}

	public void visit(ProductionItem node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ASTNode) node);
*/
	}

	public void visit(Sort node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
*/
	}

	public void visit(Terminal node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
*/
	}

	public void visit(Lexical node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
*/
	}

	public void visit(UserList node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ProductionItem) node);
*/
	}

	public void visit(TermComment node) {
          sb.append("<br/>");
	}

	public void visit(Cell node) {
          sb.append("<"+node.getLabel()+" multiplicity=TODO ellipses=TODO>");
          node.getContents().accept(this);
          sb.append("</"+node.getEndLabel()+">");
	}

	public void visit(Collection node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (Term t : node.getContents()) {
			t.accept(this);
		}
		visit((Term) node);
*/
	}

	public void visit(Ambiguity node) {
          assert false : "Ambiguities not supported in Kore";
	}

	public void visit(Bag node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

  private void visitList(List<? extends ASTNode> nodes, String sep, String empty) {
    if (nodes.size() == 0) { sb.append(empty); }
    else {
      for (int i = 0; i < nodes.size(); i++) {
        nodes.get(i).accept(this);
        if (i < nodes.size() - 1) { sb.append(sep); }
      }
    }
  }

	public void visit(KSequence node) { visitList(node.getContents(), " ~> ", ".K"); }

	public void visit(org.kframework.kil.List node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

	public void visit(KList node) {
          // TODO: is there an ambiguity here if commas occur in other places?
          visitList(node.getContents(), ", ", "");
/*
		if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

	public void visit(Map node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

	public void visit(Set node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Collection) node);
*/
	}

	public void visit(CollectionItem node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.getItem().accept(this);
		visit((Term) node);
*/
	}

	public void visit(BagItem node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((CollectionItem) node);
*/
	}

	public void visit(ListItem node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((CollectionItem) node);
*/
	}

	public void visit(MapItem node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.getKey().accept(this);
		visit((CollectionItem) node);
*/
	}

	public void visit(SetItem node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((CollectionItem) node);
*/
	}

	public void visit(DataStructureBuiltin node) {
    visit((ASTNode)node);
/*
          node.getKore().accept(this);
*/
	}

	public void visit(CollectionBuiltin node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (Term term : node.elements()) {
			term.accept(this);
		}

		visit((DataStructureBuiltin) node);
*/
	}

    @Override
    public void visit(SetBuiltin node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (Term entry : node.elements()) {
			entry.accept(this);
		}

		visit((DataStructureBuiltin) node);
*/
    }

    @Override
    public void visit(SetLookup node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.base().accept(this);
		node.key().accept(this);
		visit((Term) node);
*/
    }

    @Override
    public void visit(SetUpdate node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.set().accept(this);
		for (Term entry : node.removeEntries()) {
			entry.accept(this);
		}
		visit((Term) node);
*/
    }

    public void visit(ListBuiltin node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (Term entry : node.elementsLeft()) {
			entry.accept(this);
		}
		for (Term entry : node.elementsRight()) {
			entry.accept(this);
		}

		visit((DataStructureBuiltin) node);
*/
	}

	public void visit(ListLookup node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.base().accept(this);
		node.key().accept(this);
		node.value().accept(this);
		visit((Term) node);
*/
	}

	public void visit(ListUpdate node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.base().accept(this);
		for (Term entry : node.removeLeft()) {
			entry.accept(this);
		}
        for (Term entry : node.removeRight()) {
			entry.accept(this);
		}
		visit((Term) node);
*/
	}

    public void visit(MapBuiltin node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		for (java.util.Map.Entry<Term, Term> entry : node.elements().entrySet()) {
			entry.getKey().accept(this);
			entry.getValue().accept(this);
		}

		visit((DataStructureBuiltin) node);
*/
	}

	public void visit(MapLookup node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.base().accept(this);
		node.key().accept(this);
		node.value().accept(this);
		visit((Term) node);
*/
	}

	public void visit(MapUpdate node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		node.map().accept(this);
		for (java.util.Map.Entry<Term, Term> entry : node.removeEntries().entrySet()) {
			entry.getKey().accept(this);
			entry.getValue().accept(this);
		}
		for (java.util.Map.Entry<Term, Term> entry : node.updateEntries().entrySet()) {
			entry.getKey().accept(this);
			entry.getValue().accept(this);
		}
		visit((Term) node);
*/
	}

	public void visit(Token node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((KLabel) node);
*/
	}

	public void visit(BoolBuiltin node) {
          sb.append(node.value()); // TODO: true() vs #"true"()
	}

	public void visit(IntBuiltin node) {
          sb.append(node.value()); // TODO: true() vs #"true"()
	}

	public void visit(StringBuiltin node) {
          sb.append(node.value());
          // TODO: "abc" vs "abc"()
	}

	public void visit(GenericToken node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Token) node);
*/
	}

	public void visit(ListTerminator node) {
          sb.append(node.toString());
	}

	public void visit(Hole node) {
          sb.append("HOLE");
	}

	public void visit(FreezerHole node) {
          sb.append("HOLE");
	}

	public void visit(KApp node) {
          node.getLabel().accept(this);
          sb.append("(");
          node.getChild().accept(this);
          sb.append(")");
	}

	public void visit(KLabel node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((Term) node);
*/
	}

	public void visit(KLabelConstant node) {
          sb.append("'"+node.getLabel()+"'"); // TODO: escape the label
	}

	public void visit(Rewrite node) {
          sb.append("(");
          node.getLeft().accept(this);
          sb.append(" => ");
          node.getRight().accept(this);
          sb.append(")");
	}

	public void visit(TermCons node) {
          visit(new KApp(KLabelConstant.of(node.getProduction().getKLabel(), context), new KList(node.getContents())));
	}

	public void visit(Bracket node) {
          sb.append("(");
          node.getContent().accept(this);
          sb.append(")");
	}

	public void visit(Cast node) {
          sb.append("(");
          node.getContent().accept(this);
          sb.append(node.isSyntactic() ? " :: " : " : ");
          sb.append(node.getSort());
          sb.append(")");
	}

	public void visit(Variable node) {
          sb.append(node.getName() + ":" + node.getSort());
	}

	public void visit(Attributes node) {
    visit((ASTNode)node);
/*
		if (isVisited(attributes))
			return;
		for (Attribute t : attributes.getContents()) {
			t.accept(this);
		}
		visit((ASTNode) attributes);
*/
	}

	public void visit(Attribute node) {
    visit((ASTNode)node);
/*
		if (isVisited(attribute))
			return;
		visit((ASTNode) attribute);
*/
	}

	public void visit(StringSentence node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ModuleItem) node);
*/
	}

	public void visit(Restrictions node) {
    visit((ASTNode)node);
/*
		if (isVisited(node))
			return;
		visit((ModuleItem) node);
*/
	}

	public void visit(Freezer node) {
    visit((ASTNode)node);
/*
		if (isVisited(f))
			return;
		f.getTerm().accept(this);
		visit((Term) f);
*/
	}

	public void visit(BackendTerm node) {
    visit((ASTNode)node);
/*
		if (isVisited(term))
			return;
		visit((Term) term);
*/
	}

	public void visit(KInjectedLabel node) {
    visit((ASTNode)node);
/*
		if (isVisited(kInjectedLabel))
			return;
		kInjectedLabel.getTerm().accept(this);
		visit((Term) kInjectedLabel);
*/
	}

	public void visit(FreezerLabel node) {
    visit((ASTNode)node);
/*
		if (isVisited(freezerLabel))
			return;
		freezerLabel.getTerm().accept(this);
		visit((Term) freezerLabel);
*/
	}
}
