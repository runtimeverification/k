package org.kframework.kil.visitors;

import org.kframework.kil.*;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class BasicHookWorker implements Transformer {
	private String name;
	protected boolean skip;
	protected org.kframework.kil.loader.Context context;

	public BasicHookWorker(String name, org.kframework.kil.loader.Context context) {
		this.context = context;
		this.name = name;
	}

	@Override
	public ASTNode transform(ASTNode node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(ParseError node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(DefinitionItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(LiterateDefinitionComment node) throws TransformerException {
		return transform((DefinitionItem) node);
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		return transform((DefinitionItem) node);
	}

	@Override
	public ASTNode transform(ModuleItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Import node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(LiterateModuleComment node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return transform((Sentence) node);
	}

	@Override
	public ASTNode transform(org.kframework.kil.Context node) throws TransformerException {
		return transform((Sentence) node);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		return transform((Sentence) node);
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityExtended node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityExtendedAssoc node) throws TransformerException {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityBlock node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(PriorityBlockExtended node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Production node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(ProductionItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Sort node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Terminal node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Lexical node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(UserList node) throws TransformerException {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Term node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Collection node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Ambiguity node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Bag node) throws TransformerException {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(KSequence node) throws TransformerException {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(List node) throws TransformerException {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(KList node) throws TransformerException {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(Map node) throws TransformerException {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(Set node) throws TransformerException {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(CollectionItem node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(BagItem node) throws TransformerException {
		return transform((CollectionItem) node);
	}

	@Override
	public ASTNode transform(ListItem node) throws TransformerException {
		return transform((CollectionItem) node);
	}

	@Override
	public ASTNode transform(MapItem node) throws TransformerException {
		return transform((CollectionItem) node);
	}

	@Override
	public ASTNode transform(SetItem node) throws TransformerException {
		return transform((CollectionItem) node);
	}

    @Override
    public ASTNode transform(CollectionBuiltin node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(SetBuiltin node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(SetLookup node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(SetUpdate node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(ListBuiltin node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(ListLookup node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(ListUpdate node) throws TransformerException {
        return transform((Term) node);
    }

     @Override
    public ASTNode transform(MapBuiltin node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(MapLookup node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(MapUpdate node) throws TransformerException {
        return transform((Term) node);
    }

    @Override
    public ASTNode transform(Token node) throws TransformerException {
        /* an instance of class Token is immutable */
        return transform((KLabel) node);
    }

    @Override
    public ASTNode transform(BoolBuiltin node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(IntBuiltin node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(StringBuiltin node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
    public ASTNode transform(GenericToken node) throws TransformerException {
        return transform((Token) node);
    }

    @Override
	public ASTNode transform(Empty node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(ListTerminator node) throws TransformerException {
		return transform((Empty) node);
	}

	@Override
	public ASTNode transform(Hole node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(KLabel node) throws TransformerException {
		return transform((Term) node);
	}

    @Override
    public ASTNode transform(KLabelConstant node) throws TransformerException {
        return transform((KLabel) node);
    }

    @Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Bracket node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Cast node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Freezer node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(BackendTerm term) throws TransformerException {
		return transform((Term) term);
	}

	@Override
	public ASTNode transform(Attributes node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Attribute node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public ASTNode transform(KInjectedLabel node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(FreezerHole node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(FreezerLabel node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(StringSentence node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Restrictions node) throws TransformerException {
		return node;
	}

	public boolean isSkip() {
		return skip;
	}
}
