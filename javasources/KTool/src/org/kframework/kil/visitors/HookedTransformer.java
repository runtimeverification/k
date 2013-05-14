package org.kframework.kil.visitors;

import org.kframework.kil.*;
import org.kframework.kil.visitors.exceptions.TransformerException;


public class HookedTransformer implements Transformer {

	BasicHookWorker before = null;
	BasicHookWorker after = null;
	String name;
	BasicTransformerPropagator propagator = new BasicTransformerPropagator(this);

	public HookedTransformer(BasicHookWorker before, String name) {
		this.before = before;
		this.name = name;
	}

	public HookedTransformer(String name, BasicHookWorker after) {
		this.name = name;
		this.after = after;
	}

	public HookedTransformer(BasicHookWorker before, String name, BasicHookWorker after) {
		this.before = before;
		this.name = name;
		this.after = after;
	}

	public void setBefore(BasicHookWorker before) {
		this.before = before;
	}

	public void setAfter(BasicHookWorker after) {
		this.after = after;
	}

	@Override
	public ASTNode transform(ASTNode node) throws TransformerException {
		if (before != null) {
			node = node.accept(before);
			if (before.isSkip())
				return node;
		}
		if (node == null)
			return null;
		node = node.accept(propagator);
		if (node == null)
			return node;
		if (after != null) {
			node = node.accept(after);
		}
		return node;
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
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(ModuleItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Import node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(LiterateModuleComment node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Sentence node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(StringSentence node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Restrictions node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Context node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(PriorityExtended node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(PriorityExtendedAssoc node) throws TransformerException {
		return transform((ASTNode) node);
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
	public ASTNode transform(Attributes node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Attribute node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Sort node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Lexical node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Terminal node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(UserList node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Term node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Collection node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Ambiguity node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Bag node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(KSequence node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(List node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(KList node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Map node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Set node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(CollectionItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(BagItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(ListItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(MapItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(SetItem node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Constant node) throws TransformerException {
		return transform((ASTNode) node);
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
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(ListTerminator node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Hole node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(KLabel node) throws TransformerException {
		return transform((ASTNode) node);
	}

    @Override
    public ASTNode transform(KLabelConstant node) throws TransformerException {
        return transform((KLabel) node);
    }

    @Override
	public ASTNode transform(KInjectedLabel node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(FreezerHole node) throws TransformerException {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(FreezerLabel node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(TermCons node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Bracket node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Cast node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Freezer node) throws TransformerException {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(BackendTerm term) throws TransformerException {
		return transform((ASTNode) term);
	}

	public void setPropagator(BasicTransformerPropagator propagator) {
		this.propagator = propagator;
	}

	@Override
	public String getName() {
		return name;
	}
}
