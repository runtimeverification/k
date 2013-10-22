package org.kframework.backend.kil;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.kil.*;
import org.kframework.kil.visitors.BasicVisitor;

public class KExpFilter extends BasicVisitor {
    protected StringBuilder result;

	public KExpFilter(org.kframework.kil.loader.Context context) {
		super(context);
		result = new StringBuilder();
	}

	public String getResult() {
		return result.toString();
	}

	/*
	@Override
	public void visit(Definition def) {
		throw new RuntimeException("don't know how to transform Definition to K Expression");
	}

	@Override
	public void visit(Import imp) {
		throw new RuntimeException("don't know how to transform Import to K Expression");
	}

	@Override
	public void visit(Module mod) {
		throw new RuntimeException("don't know how to transform Module to K Expression");
	}

	@Override
	public void visit(Syntax syn) {
		throw new RuntimeException("don't know how to transform Syntax to K Expression");
	}

	@Override
	public void visit(PriorityBlock priorityBlock) {
		throw new RuntimeException("don't know how to transform PriorityBlock to K Expression");
	}

	@Override
	public void visit(Production prod) {
		throw new RuntimeException("don't know how to transform Production to K Expression");
	}

	@Override
	public void visit(Sort sort) {
		throw new RuntimeException("don't know how to transform Sort to K Expression");
	}

	@Override
	public void visit(Terminal terminal) {
		throw new RuntimeException("don't know how to transform Terminal to K Expression");
	}

	@Override
	public void visit(StringSentence stringSentence) {
		result.append("StringSentence should not be StringSentence");
	}

	@Override
	public void visit(UserList userList) {
		throw new RuntimeException("don't know how to transform UserList to K Expression");
	}

	@Override
	public void visit(Attributes attributes) {
		throw new RuntimeException("don't know how to transform Attributes to K Expression");
	}

	@Override
	public void visit(Attribute attribute) {
		throw new RuntimeException("don't know how to transform Attribute to K Expression");
	}

	@Override
	public void visit(Configuration configuration) {
		throw new RuntimeException("don't know how to transform Configuration to K Expression");
	}

	@Override
	public void visit(Cell cell) {
		throw new RuntimeException("don't know how to transform Cell to K Expression");
	}

	@Override
	public void visit(Variable variable) {
		throw new RuntimeException("don't know how to transform Variable to K Expression");
	}
	*/

	@Override
	public void visit(Empty empty) {
		String sort = empty.getSort();
		if (MaudeHelper.basicSorts.contains(sort)) {
			if (!sort.equals(KSorts.KLIST)) {
				result.append("()");
			}
		} else {
			throw new RuntimeException("don't know how to transform Empty syntax list to K Expression");
		}
	}

	/*
	@Override
	public void visit(Rule rule) {
		throw new RuntimeException("don't know how to transform Rule to K Expression");
	}
	*/

	@Override
	public void visit(KApp kapp) {
		if (kapp.getLabel() instanceof Token) {
			final boolean isString = ((Token)kapp.getLabel()).getSort().equals("#String");
			if (isString)
				result.append("\"");
			result.append(((Token)kapp.getLabel()).value());
			if (isString)
				result.append("\""); 
		} else {
			result.append("(");
			kapp.getLabel().accept(this);
			result.append(" ");
			kapp.getChild().accept(this);
			result.append(")");
		}
	}

	/*
	@Override
	public void visit(KSequence ksequence) {
		throw new RuntimeException("don't know how to transform KSequence to K Expression");
	}

	@Override
	public void visit(TermCons termCons) {
		throw new RuntimeException("don't know how to transform TermCons to K Expression");
	}

	@Override
	public void visit(Sentence sentence) {
		throw new RuntimeException("don't know how to transform Sentence to K Expression");
	}

	@Override
	public void visit(Rewrite rewrite) {
		throw new RuntimeException("don't know how to transform Rewrite to K Expression");
	}
	*/

    @Override
    public void visit(KLabelConstant kLabelConstant) {
        result.append(kLabelConstant.getLabel());
    }

    @Override
    public void visit(Token token) {
        result.append(token);
    }

	/*
	@Override
	public void visit(Collection collection) {
		throw new RuntimeException("don't know how to transform Collection to K Expression");
	}

	@Override
	public void visit(CollectionItem collectionItem) {
		throw new RuntimeException("don't know how to transform CollectionItem to K Expression");
	}

	@Override
	public void visit(BagItem bagItem) {
		throw new RuntimeException("don't know how to transform BagItem to K Expression");
	}

	@Override
	public void visit(ListItem listItem) {
		throw new RuntimeException("don't know how to transform ListItem to K Expression");
	}

	@Override
	public void visit(SetItem setItem) {
		throw new RuntimeException("don't know how to transform SetItem to K Expression");
	}

	@Override
	public void visit(MapItem mapItem) {
		throw new RuntimeException("don't know how to transform MapItem to K Expression");
	}

	@Override
	public void visit(Hole hole) {
		throw new RuntimeException("don't know how to transform Hole to K Expression");
	}
	*/

	@Override
	public void visit(KInjectedLabel kInjectedLabel) {
		result.append("(");
		Term term = kInjectedLabel.getTerm();
		result.append(term.getSort().replaceFirst("#",""));
		result.append(" ");
		term.accept(this);
		result.append(")");
	}

	/*
	@Override
	public void visit(KLabel kLabel) {
		throw new RuntimeException("don't know how to transform KLabel to K Expression");
	}

	@Override
	public void visit(TermComment termComment) {
		throw new RuntimeException("don't know how to transform TermComment to K Expression");
	}

	@Override
	public void visit(List list) {
		throw new RuntimeException("don't know how to transform List to K Expression");
	}

	@Override
	public void visit(Map map) {
		throw new RuntimeException("don't know how to transform Map to K Expression");
	}

	@Override
	public void visit(Bag bag) {
		throw new RuntimeException("don't know how to transform Bag to K Expression");
	}

	@Override
	public void visit(Set set) {
		throw new RuntimeException("don't know how to transform Set to K Expression");
	}

	@Override
	public void visit(Ambiguity ambiguity) {
		throw new RuntimeException("don't know how to transform Ambiguity to K Expression");
	}

	@Override
	public void visit(Context context) {
		throw new RuntimeException("don't know how to transform Context to K Expression");
	}

	@Override
	public void visit(LiterateDefinitionComment literateDefinitionComment) {
		throw new RuntimeException("don't know how to transform LiterateDefinitionComment to K Expression");
	}

	@Override
	public void visit(LiterateModuleComment literateModuleComment) {
		throw new RuntimeException("don't know how to transform LiterateModuleComment to K Expression");
	}

	@Override
	public void visit(Require require) {
		throw new RuntimeException("don't know how to transform Require to K Expression");
	}
	*/
}
