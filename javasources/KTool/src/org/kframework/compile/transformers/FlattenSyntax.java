package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Constant;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KSequence;
import org.kframework.kil.ListOfK;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.kil.Terminal;

public class FlattenSyntax extends CopyOnWriteTransformer {
	FlattenKSyntax kTrans = new FlattenKSyntax(this);
	Set<String> listSeparators = new HashSet<String>();
	boolean isComputation = false;

	public FlattenSyntax() {
		super("Syntax K to Abstract K");
	}
	
	
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		listSeparators.clear();
		node = (Module) super.transform(node);
		if (listSeparators.isEmpty()) return node;
		List<PriorityBlock> pbs = new ArrayList<PriorityBlock>();
		PriorityBlock pb = new PriorityBlock();
		pbs.add(pb);
		Syntax syn = new Syntax(new Sort("KLabel"), pbs);
		node.getItems().add(syn);
		for (String separator : listSeparators) {
			List<ProductionItem> pis = new ArrayList<ProductionItem>();
			pis.add(new Terminal(MetaK.getListUnitLabel(separator)));
			pb.getProductions().add(new Production(new Sort("KLabel"), pis));
		}
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		if (!MetaK.isComputationSort(node.getSort().getName())) {
			isComputation = false;
			return super.transform(node);
		}
		isComputation = true;
		node = (Syntax)super.transform(node);
		node.setSort(new Sort("KLabel"));
		return node;
	}
	
	@Override
	public ASTNode transform(Production node) throws TransformerException {
		if (!isComputation) return super.transform(node);
		if (node.isSubsort()) return null;
		String arity = String.valueOf(node.getArity());
		Attributes attrs = node.getAttributes().shallowCopy();
		if (node.isListDecl()) {
			listSeparators.add(((UserList)node.getItems().get(0)).getSeparator());
			arity = "2";
			attrs.set("hybrid", "");
		}
		node = node.shallowCopy();
		List<ProductionItem> pis = new ArrayList<ProductionItem>();
		pis.add(new Terminal(node.getKLabel()));
		node.setItems(pis);
		attrs.set("arity", arity);
		node.setAttributes(attrs);
		return node;
	}
	
	@Override
	public ASTNode transform(Sort node) throws TransformerException {
		if (!MetaK.isComputationSort(node.getName())) return node;
		return new Sort("K");
	}
	
	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		return node.accept(kTrans);
	}
	
	@Override
	public ASTNode transform(KSequence node) throws TransformerException {
		return node.accept(kTrans);
	}
	
	@Override
	public ASTNode transform(Variable node) throws TransformerException {
		if (MetaK.isComputationSort(node.getSort())) return node.accept(kTrans);
		return node;
	}
	
	@Override
	public ASTNode transform(Empty node) throws TransformerException {
		if (MetaK.isComputationSort(node.getSort())) return node.accept(kTrans);
		return node;
	}
	
	@Override
	public ASTNode transform(Constant node) throws TransformerException {
		if (MetaK.isComputationSort(node.getSort())) return node.accept(kTrans);
		return node;
	}
	
	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (MetaK.isComputationSort(tc.getSort())) return tc.accept(kTrans);
		return super.transform(tc);
	}
	
	class FlattenKSyntax extends CopyOnWriteTransformer {
		FlattenSyntax trans;
		
		public FlattenKSyntax(FlattenSyntax t) {
			super("Flatten K Syntax");
			trans = t;
		}
		
		@Override
		public ASTNode transform(KApp node) throws TransformerException {
			Term label = (Term)node.getLabel().accept(trans);
			Term child = (Term)node.getChild().accept(trans);
			if (child != node.getChild() || label != node.getLabel()) {
				node = node.shallowCopy();
				node.setChild(child);
				node.setLabel(label);
			}
			return node;
		}

		@Override
		public ASTNode transform(TermCons tc) throws TransformerException {
			if (!MetaK.isComputationSort(tc.getSort())) {
				return new KApp(new KInjectedLabel((Term)tc.accept(trans)), new Empty("List{K}"));
			}
			String l = tc.getLocation();
			String f = tc.getFilename();
			Production ppp = DefinitionHelper.conses.get(tc.getCons());
			String klabel = ppp.getKLabel();
			KApp kapp = new KApp(l, f);
			kapp.setLabel(new Constant(l, f, "KLabel", klabel));
			ListOfK lok = new ListOfK(l, f);
			kapp.setChild(lok);
			for (Term t : tc.getContents()) {
				lok.getContents().add((Term) t.accept(this));
			}
			return kapp;
		}

		@Override
		public ASTNode transform(Constant cst) {
			String l = cst.getLocation();
			String f = cst.getFilename();
			
			if (!cst.getSort().equals("KLabel"))
				return new KApp(l, f, new KInjectedLabel(cst), new Empty(l, f, "List{K}"));

			return cst;
		}

		@Override
		public ASTNode transform(Empty emp) {
			String l = emp.getLocation();
			String f = emp.getFilename();
			if (!MetaK.isComputationSort(emp.getSort())) {
				return new KApp(new KInjectedLabel(emp), new Empty("List{K}"));	
			}
			// if this is a list sort
			if (!MaudeHelper.basicSorts.contains(emp.getSort())) {
				Production listProd = DefinitionHelper.listConses.get(emp.getSort());
				String separator = ((UserList)listProd.getItems().get(0)).getSeparator();
				return new KApp(l, f, new Constant("KLabel", MetaK.getListUnitLabel(separator)),new Empty("List{K}"));
//				Constant cst = new Constant(l, f, "KLabel", "'." + emp.getSort() + "");
//				return new KApp(l, f, cst, new Empty(l, f, "List{K}"));
			}
			return emp;
		}
		
		@Override
		public ASTNode transform(Collection node) throws TransformerException {
			if (node instanceof KSequence) return super.transform(node);
			return new KApp(new KInjectedLabel((Term)node.accept(trans)), new Empty("List{K}"));
		}
		
		@Override
		public ASTNode transform(CollectionItem node) throws TransformerException {
			return new KApp(new KInjectedLabel((Term)node.accept(trans)), new Empty("List{K}"));
		}

		
		@Override
		public ASTNode transform(Cell node) throws TransformerException {
			return new KApp(new KInjectedLabel((Term)node.accept(trans)), new Empty("List{K}"));
		}
		
		@Override
		public ASTNode transform(Variable node) throws TransformerException {
			if ("K".equals(node.getSort())) return node;
			if (MetaK.isKSort(node.getSort())) 			
				return new KApp(new KInjectedLabel(node), new Empty("List{K}"));
			node = node.shallowCopy();
			node.setSort("KItem");
			return node;
		}
		
		
	}
}

/*
 * f(5)
 * 
 * 'f(# 5(.List{K}))
 * 
 * env(X |-> 5) 'env(Map2KLabel(C |-> 5)(.List{K}))
 */
