package org.kframework.backend.unparser;

import org.kframework.backend.maude.MaudeFilter;
import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.Attribute;
import org.kframework.kil.Attributes;
import org.kframework.kil.Bag;
import org.kframework.kil.BagItem;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Definition;
import org.kframework.kil.Empty;
import org.kframework.kil.Hole;
import org.kframework.kil.Import;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabel;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListItem;
import org.kframework.kil.ListOfK;
import org.kframework.kil.LiterateDefinitionComment;
import org.kframework.kil.LiterateModuleComment;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sentence;
import org.kframework.kil.SetItem;
import org.kframework.kil.Sort;
import org.kframework.kil.StringSentence;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermComment;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;
import org.kframework.utils.utils.strings.StringUtil;

public class KastFilter extends BasicVisitor {
    protected Indenter result;
    
	public KastFilter() {
		result = new Indenter();
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
	public void visit(ListOfK listOfK) {
		if (listOfK.getContents().size() == 0) {
			new Empty(listOfK.getSort()).accept(this);
		} else if (listOfK.getContents().size() == 1) {
			listOfK.getContents().get(0).accept(this);
		} else {
//			String constructor = MaudeFilter.getMaudeConstructor(listOfK.getSort());
//			result.write(constructor);
//			result.write("(");
//			result.endLine();
//			result.indent(4);

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

//			result.unindent();
//			result.write(")");
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
			if (!sort.equals("List{K}")) {
				result.write("(.).");
				result.write(sort);
			} else {
				result.write(".");
				result.write(sort);
			}
		} else {
			Production prd = DefinitionHelper.listConses.get(sort);
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
//		result.write("_`(_`)(");
//		result.endLine();
		kapp.getLabel().accept(this);
		result.indentToCurrent();
		result.write("(");
//		result.endLine();
//		result.indent(4);
		kapp.getChild().accept(this);
		result.write(")");
		result.unindent();
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
	public void visit(Constant constant) {
		if (constant.getSort().equals("#Id")) {
			result.write("#id \"");
		}
		result.write(constant.getValue());
		if (constant.getSort().equals("#Id")) {
			result.write("\"");
		}
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
			result.write(StringUtil.escapeMaude(kInjectedLabel.getInjectedSort(term.getSort())));
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
		// TODO
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
