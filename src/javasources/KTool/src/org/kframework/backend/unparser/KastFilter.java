package org.kframework.backend.unparser;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class KastFilter extends BasicVisitor {
    protected Indenter result;
    private boolean nextline;
    
	public KastFilter(org.kframework.kil.loader.Context context) {
		super(context);
		result = new Indenter();
		result.setWidth(Integer.MAX_VALUE);
	}
	
	public KastFilter(IndentationOptions indentationOptions, boolean nextline, org.kframework.kil.loader.Context context) {
		super(context);
		result = new Indenter(indentationOptions);
		this.nextline = nextline;
	}

	public String getResult() {
		return result.toString();
	}

	@Override
	public void visit(Definition def) {
		throw new RuntimeException("don't know how to kast Definition");
	}

	@Override
	public void visit(Import imp) {
		throw new RuntimeException("don't know how to kast Import");
	}

	@Override
	public void visit(Module mod) {
		throw new RuntimeException("don't know how to kast Module");
	}

	@Override
	public void visit(Syntax syn) {
		throw new RuntimeException("don't know how to kast Syntax");
	}

	@Override
	public void visit(PriorityBlock priorityBlock) {
		throw new RuntimeException("don't know how to kast PriorityBlock");
	}

	@Override
	public void visit(Production prod) {
		throw new RuntimeException("don't know how to kast Production");
	}

	@Override
	public void visit(Sort sort) {		
		throw new RuntimeException("don't know how to kast Sort");
	}

	@Override
	public void visit(Terminal terminal) {
		throw new RuntimeException("don't know how to kast Terminal");
	}

	@Override
	public void visit(StringSentence stringSentence) {
		result.write("StringSentence should not be StringSentence");
	}

	@Override
	public void visit(UserList userList) {
		throw new RuntimeException("don't know how to kast UserList");
	}

	@Override
	public void visit(KList listOfK) {
		if (listOfK.getContents().size() == 0) {
			new Empty(listOfK.getSort()).accept(this);
		} else if (listOfK.getContents().size() == 1) {
			listOfK.getContents().get(0).accept(this);
		} else {
			boolean first = true;
			for (Term term : listOfK.getContents()) {
				if (!first) {
					result.write(",,");
					result.endLine();
				} else {
					first = false;
				}
				if (term == null) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"NULL Term encountered when KastFilter ran on collection " + listOfK.getContents() + ".", 
							listOfK.getFilename(), listOfK.getLocation()));				
				}	
				term.accept(this);
			}
		}
	}

	@Override
	public void visit(Attributes attributes) {
		throw new RuntimeException("don't know how to kast Attributes");
	}

	@Override
	public void visit(Attribute attribute) {
		throw new RuntimeException("don't know how to kast Attribute");
	}

	@Override
	public void visit(Configuration configuration) {
		throw new RuntimeException("don't know how to kast Configuration");
	}

	@Override
	public void visit(Cell cell) {
		throw new RuntimeException("don't know how to kast Cell");
	}

	@Override
	public void visit(Variable variable) {
		throw new RuntimeException("don't know how to kast Variable");
	}

	@Override
	public void visit(Empty empty) {
		String sort = empty.getSort();
		if (MaudeHelper.basicSorts.contains(sort)) {
			result.write(".");
			result.write(sort);
		} else {
			Production prd = context.listConses.get(sort);
			UserList ul = (UserList) prd.getItems().get(0);
			result.write(".List`{\"");
			result.write(ul.getSeparator());
			result.write("\"`}");
		}
	}

	@Override
	public void visit(Rule rule) {		
		throw new RuntimeException("don't know how to kast Rule");
	}

	@Override
	public void visit(KApp kapp) {
		if (kapp.getLabel() instanceof Token) {
			Token token = (Token)kapp.getLabel();
			if (token.tokenSort().equals("#Id")) {
				result.write("#id \"");
			}
			result.write(token.value());
			if (token.tokenSort().equals("#Id")) {
				result.write("\"");
			} 
			result.write(token.toString());
		} else {
			kapp.getLabel().accept(this);
			result.write("(");
			boolean stopnextline = false;
			if (kapp.getChild() instanceof KList) {
				KList listOfK = (KList)kapp.getChild();
				if (listOfK.getContents().size() <= 1) {
					stopnextline = true;
				}
			}
			if (kapp.getChild() instanceof Empty) {
				stopnextline = true;
			}
			if (nextline) {
				if (!stopnextline) {
					result.endLine();
					result.indent(1);
				}
			} else {
				result.indentToCurrent();
			}
			kapp.getChild().accept(this);
			result.write(")");
			if (!nextline || !stopnextline) {
				result.unindent();
			}
		}
	}

	@Override
	public void visit(KSequence ksequence) {
		throw new RuntimeException("don't know how to kast KSequence");
	}

	@Override
	public void visit(TermCons termCons) {
		throw new RuntimeException("don't know how to kast TermCons");
	}
	
	@Override
	public void visit(Sentence sentence) {
		throw new RuntimeException("don't know how to kast Sentence");
	}
	
	@Override
	public void visit(Rewrite rewrite) {
		throw new RuntimeException("don't know how to kast Rewrite");
	}

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        result.write(kLabelConstant.getLabel());
    }

    @Override
    public void visit(Token token) {
        result.write(token.toString());
    }

	@Override
	public void visit(Collection collection) {
		throw new RuntimeException("don't know how to kast Collection");
	}	
	
	@Override
	public void visit(CollectionItem collectionItem) {
		throw new RuntimeException("don't know how to kast CollectionItem");
	}

	@Override
	public void visit(BagItem bagItem) {
		throw new RuntimeException("don't know how to kast BagItem");
	}

	@Override
	public void visit(ListItem listItem) {
		throw new RuntimeException("don't know how to kast ListItem");
	}

	@Override
	public void visit(SetItem setItem) {
		throw new RuntimeException("don't know how to kast SetItem");
	}

	@Override
	public void visit(MapItem mapItem) {
		throw new RuntimeException("don't know how to kast MapItem");
	}

	@Override
	public void visit(Hole hole) {
		throw new RuntimeException("don't know how to kast Hole");
	}

	@Override
	public void visit(KInjectedLabel kInjectedLabel) {
		Term term = kInjectedLabel.getTerm();
		if (MetaK.isKSort(term.getSort())) {
            result.write(KInjectedLabel.getInjectedSort(term.getSort()));
			result.write("2KLabel_("); 
		} else {
			result.write("#_(");
		}
		term.accept(this);
		result.write(")");
	}

	@Override
	public void visit(KLabel kLabel) {
		throw new RuntimeException("don't know how to kast KLabel");
	}

	@Override
	public void visit(TermComment termComment) {
		throw new RuntimeException("don't know how to kast TermComment");
	}

	@Override
	public void visit(org.kframework.kil.List list) {
		throw new RuntimeException("don't know how to kast List");
	}

	@Override
	public void visit(org.kframework.kil.Map map) {
		throw new RuntimeException("don't know how to kast Map");
	}

	@Override
	public void visit(Bag bag) {
		throw new RuntimeException("don't know how to kast Bag");
	}
	
	@Override
	public void visit(org.kframework.kil.Set set) {
		throw new RuntimeException("don't know how to kast Set");
	}

	@Override
	public void visit(org.kframework.kil.Ambiguity ambiguity) {
		throw new RuntimeException("don't know how to kast Ambiguity");
	}

	@Override
	public void visit(org.kframework.kil.Context context) {
		throw new RuntimeException("don't know how to kast Context");
	}

	@Override
	public void visit(LiterateDefinitionComment literateDefinitionComment) {
		throw new RuntimeException("don't know how to kast LiterateDefinitionComment");
	}

	@Override
	public void visit(LiterateModuleComment literateModuleComment) {
		throw new RuntimeException("don't know how to kast LiterateModuleComment");
	}
	
	@Override
	public void visit(org.kframework.kil.Require require) {
		throw new RuntimeException("don't know how to kast Require");
	}
}
