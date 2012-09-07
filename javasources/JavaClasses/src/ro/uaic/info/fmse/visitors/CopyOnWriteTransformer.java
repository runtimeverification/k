package ro.uaic.info.fmse.visitors;

import java.util.ArrayList;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.*;

public class CopyOnWriteTransformer implements Transformer {

	@Override
	public ASTNode transform(ASTNode node) {
		return node;
	}

	@Override
	public ASTNode transform(Definition node) {
		boolean change = false;
		ArrayList<DefinitionItem> items = new ArrayList<DefinitionItem>();
		for (DefinitionItem di : node.getItems()) {
			ASTNode result = di.accept(this);
			if (result != di) change = true;
			if (result != null) {
				if (!(result instanceof DefinitionItem)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting DefinitionItem, but got " + result.getClass() + " while transforming.", 
							di.getFilename(), di.getLocation(), 0));					
				}
				items.add((DefinitionItem) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setItems(items);
		}
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(DefinitionItem node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(LiterateDefinitionComment node) {
		return transform((DefinitionItem) node);
	}

	@Override
	public ASTNode transform(Module node) {
		boolean change = false;
		ArrayList<ModuleItem> items = new ArrayList<ModuleItem>();
		for (ModuleItem mi : node.getItems()) {
			ASTNode result = mi.accept(this);
			if (result != mi) change = true;
			if (result != null) {
				if (!(result instanceof ModuleItem)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting ModuleItem, but got " + result.getClass() + " while transforming.", 
							mi.getFilename(), mi.getLocation(), 0));					
				}
				items.add((ModuleItem) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setItems(items);
		}
		return transform((DefinitionItem) node);
	}

	@Override
	public ASTNode transform(ModuleItem node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Import node) {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(LiterateModuleComment node) {
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Sentence node) {
		boolean change = false;
		Term body = node.getBody();
		ASTNode bodyAST = body.accept(this);
		if (bodyAST != body) change = true;
		if (null == bodyAST) return null;
		if (!(bodyAST instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + bodyAST.getClass() + " while transforming.", 
					body.getFilename(), body.getLocation(), 0));					
		}
		body = (Term) bodyAST;
		Term condition = node.getCondition();
		if (condition != null) {
			ASTNode conditionAST = condition.accept(this);
			if (conditionAST != condition) change = true;
			if (null == conditionAST) return null;
			if (!(conditionAST instanceof Term)) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.INTERNAL, 
						"Expecting Term, but got " + conditionAST.getClass() + " while transforming.", 
						condition.getFilename(), condition.getLocation(), 0));					
			}
			condition = (Term) conditionAST;
		}
		if (change) {
			node = node.shallowCopy();
			node.setBody(body);
			node.setCondition(condition);			
		}
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(Configuration node) {
		return transform((Sentence) node);
	}

	@Override
	public ASTNode transform(Context node) {
		return transform((Sentence) node);
	}

	@Override
	public ASTNode transform(Rule node) {
		return transform((Sentence) node);
	}

	@Override
	public ASTNode transform(Syntax node) {
		boolean change = false;
		ArrayList<PriorityBlock> pbs = new ArrayList<PriorityBlock>();
		for (PriorityBlock pb : node.getPriorityBlocks()) {
			ASTNode result = pb.accept(this);
			if (result != pb) change = true;
			if (result != null) {
				if (!(result instanceof PriorityBlock)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting PriorityBlock, but got " + result.getClass() + " while transforming.", 
							pb.getFilename(), pb.getLocation(), 0));					
				}
				pbs.add((PriorityBlock) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setPriorityBlocks(pbs);
		}
		return transform((ModuleItem) node);
	}

	@Override
	public ASTNode transform(PriorityBlock node) {
		boolean change = false;
		ArrayList<Production> prods = new ArrayList<Production>();
		for (Production p : node.getProductions()) {
			ASTNode result = p.accept(this);
			if (result != p) change = true;
			if (result != null) {
				if (!(result instanceof Production)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting Production, but got " + result.getClass() + " while transforming.", 
							p.getFilename(), p.getLocation(), 0));					
				}
				prods.add((Production) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setProductions(prods);
		}
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Production node) {
		boolean change = false;
		ArrayList<ProductionItem> pis = new ArrayList<ProductionItem>();
		for (ProductionItem pi : node.getItems()) {
			ASTNode result = pi.accept(this);
			if (result != pi) change = true;
			if (result != null) {
				if (!(result instanceof ProductionItem)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting Production, but got " + result.getClass() + " while transforming.", 
							pi.getFilename(), pi.getLocation(), 0));					
				}
				pis.add((ProductionItem) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setItems(pis);
		}
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(ProductionItem node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Sort node) {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Terminal node) {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(UserList node) {
		return transform((ProductionItem) node);
	}

	@Override
	public ASTNode transform(Term node) {
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Cell node) {
		Term term = node.getContents();
		ASTNode result = term.accept(this);
		if (result == null) {
			result = MetaK.defaultTerm(term);
		}
		if (!(result instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + result.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (result != term) {
			node = node.shallowCopy();
			node.setContents((Term) result);
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Collection node) {
		boolean change = false;
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			ASTNode result = t.accept(this);
			if (result != t) change = true;
			if (result != null) {
				if (!(result instanceof Term)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting Term, but got " + result.getClass() + " while transforming.", 
							t.getFilename(), t.getLocation(), 0));					
				}
				terms.add((Term) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setContents(terms);
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Ambiguity node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(Bag node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(KSequence node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(List node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(ListOfK node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(Map node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(Set node) {
		return transform((Collection) node);
	}

	@Override
	public ASTNode transform(CollectionItem node) {
		Term term = node.getItem();
		ASTNode result = term.accept(this);
		if (result == null) return null;
		if (!(result instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + result.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (result != term) {
			node = node.shallowCopy();
			node.setItem((Term) result);
		}
		return transform((Term) node);		
	}

	@Override
	public ASTNode transform(BagItem node) {
		return transform((CollectionItem) node);
	}

	@Override
	public ASTNode transform(ListItem node) {
		return transform((CollectionItem) node);
	}

	@Override
	public ASTNode transform(MapItem node) {
		boolean change = false;
		Term term = node.getKey();
		ASTNode key = term.accept(this);
		if (key == null) return null;
		if (!(key instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + key.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (key != term) {
			change = true;
		}
		term = node.getValue();
		ASTNode value = term.accept(this);
		if (value == null) return null;
		if (!(value instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + value.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (value != term) {
			change = true;
		}
		if (change) {
			node = node.shallowCopy();
			node.setKey((Term) key);
			node.setValue((Term) value);
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(SetItem node) {
		return transform((CollectionItem) node);
	}

	@Override
	public ASTNode transform(Constant node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Empty node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Hole node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(KApp node) {
		boolean change = false;
		Term term = node.getLabel();
		ASTNode label = term.accept(this);
		if (label == null) return null;
		if (!(label instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + label.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (label != term) {
			change = true;
		}
		term = node.getChild();
		ASTNode child = term.accept(this);
		if (child == null) return null;
		if (!(child instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + child.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (child != term) {
			change = true;
		}
		if (change) {
			node = node.shallowCopy();
			node.setLabel((Term) label);
			node.setChild((Term) child);
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(KLabel node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Rewrite node) {
		boolean change = false;
		Term term = node.getLeft();
		ASTNode left = term.accept(this);
		if (left == null) return null;
		if (!(left instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + left.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (left != term) {
			change = true;
		}
		term = node.getRight();
		ASTNode right = term.accept(this);
		if (right == null) return null;
		if (!(right instanceof Term)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + right.getClass() + " while transforming.", 
					term.getFilename(), term.getLocation(), 0));					
		}
		if (right != term) {
			change = true;
		}
		if (change) {
			node = node.shallowCopy();
			node.setLeft((Term) left);
			node.setRight((Term) right);
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(TermCons node) {
		boolean change = false;
		ArrayList<Term> terms = new ArrayList<Term>();
		for (Term t : node.getContents()) {
			ASTNode result = t.accept(this);
			if (result != t) change = true;
			if (result != null) {
				if (!(result instanceof Term)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting Term, but got " + result.getClass() + " while transforming.", 
							t.getFilename(), t.getLocation(), 0));					
				}
				terms.add((Term) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setContents(terms);
		}
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Variable node) {
		return transform((Term) node);
	}

	@Override
	public ASTNode transform(Attributes node) {
		boolean change = false;
		java.util.List<Attribute> contents = new ArrayList<Attribute>();
		for (Attribute at : node.getContents()) {
			ASTNode result = at.accept(this);
			if (result != at) change = true;
			if (result != null) {
				if (!(result instanceof Attribute)) {
					GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
							KExceptionGroup.INTERNAL, 
							"Expecting Attribute, but got " + result.getClass() + " while transforming.", 
							at.getFilename(), at.getLocation(), 0));					
				}
				contents.add((Attribute) result);
			}
		}
		if (change) {
			node = node.shallowCopy();
			node.setContents(contents);			
		}
		return transform((ASTNode) node);
	}

	@Override
	public ASTNode transform(Attribute node) {
		return transform((ASTNode) node);
	}
}
