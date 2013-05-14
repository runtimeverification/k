package org.kframework.compile.transformers;

import org.kframework.compile.utils.MaudeHelper;
import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attributes;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.Cell;
import org.kframework.kil.Collection;
import org.kframework.kil.CollectionItem;
import org.kframework.kil.Constant;
import org.kframework.kil.Empty;
import org.kframework.kil.FloatBuiltin;
import org.kframework.kil.Freezer;
import org.kframework.kil.FreezerLabel;
import org.kframework.kil.IntBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KInjectedLabel;
import org.kframework.kil.KLabel;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.KSequence;
import org.kframework.kil.KSorts;
import org.kframework.kil.MapItem;
import org.kframework.kil.Module;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Sort;
import org.kframework.kil.StringBuiltin;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Terminal;
import org.kframework.kil.UserList;
import org.kframework.kil.Variable;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.StringUtil;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
		if (listSeparators.isEmpty())
			return node;

		// List<PriorityBlock> pbs = new ArrayList<PriorityBlock>();
		// PriorityBlock pb = new PriorityBlock();
		// pbs.add(pb);
		// Syntax syn = new Syntax(new Sort(KSorts.KLABEL), pbs);
		// node.getItems().add(syn);
		// for (String separator : listSeparators) {
		// List<ProductionItem> pis = new ArrayList<ProductionItem>();
		// pis.add(new Terminal(MetaK.getListUnitLabel(separator)));
		// pb.getProductions().add(new Production(new Sort(KSorts.KLABEL), pis));
		// }
		for (String sep : listSeparators) {
			node.addConstant(KSorts.KLABEL, MetaK.getListUnitLabel(sep));
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
		node = (Syntax) super.transform(node);
		node.setSort(new Sort(KSorts.KLABEL));
		return node;
	}

	@Override
	public ASTNode transform(Production node) throws TransformerException {
		if (node.containsAttribute("KLabelWrapper"))
			return node;
		if (!isComputation)
			return super.transform(node);
		if (node.isSubsort() && !node.containsAttribute("klabel"))
			return null;
		String arity = String.valueOf(node.getArity());
		Attributes attrs = node.getAttributes().shallowCopy();
		if (node.isListDecl()) {
			listSeparators.add(((UserList) node.getItems().get(0)).getSeparator());
			attrs.set("hybrid", "");
		}
		node = node.shallowCopy();
		List<ProductionItem> pis = new ArrayList<ProductionItem>();
		pis.add(new Terminal(node.getKLabel()));
		node.setItems(pis);
		attrs.set("arity", arity);
		node.setAttributes(attrs);
		node.setSort(KSorts.KLABEL);
		return node;
	}

	@Override
	public ASTNode transform(Sort node) throws TransformerException {
		if (!MetaK.isComputationSort(node.getName()))
			return node;
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
		if (MetaK.isComputationSort(node.getSort()))
			return node.accept(kTrans);
		return node;
	}

	@Override
	public ASTNode transform(Empty node) throws TransformerException {
		if (MetaK.isComputationSort(node.getSort()))
			return node.accept(kTrans);
		return node;
	}

	@Override
	public ASTNode transform(Constant node) throws TransformerException {
        assert false : "dead code";
		if (MetaK.isComputationSort(node.getSort()))
			return node.accept(kTrans);
		return node;
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		if (MetaK.isComputationSort(tc.getSort()))
			return tc.accept(kTrans);
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
			Term label = (Term) node.getLabel().accept(trans);
			Term child = (Term) node.getChild().accept(trans);
			if (child != node.getChild() || label != node.getLabel()) {
				node = node.shallowCopy();
				node.setChild(child);
				node.setLabel(label);
			}
			return node;
		}

		@Override
		public ASTNode transform(Freezer node) throws TransformerException {
			return KApp.of(new FreezerLabel((Term) node.getTerm().accept(this)));
		}

		@Override
		public ASTNode transform(TermCons tc) throws TransformerException {
			if (!MetaK.isComputationSort(tc.getSort())) {
				return KApp.of(new KInjectedLabel((Term) tc.accept(trans)));
			}

			String l = tc.getLocation();
			String f = tc.getFilename();
			Production ppp = DefinitionHelper.conses.get(tc.getCons());
			KList lok = new KList(l, f);
			for (Term t : tc.getContents()) {
				lok.getContents().add((Term) t.accept(this));
			}
			return new KApp(l, f, KLabelConstant.of(ppp.getKLabel()), lok);
		}

		@Override
		public ASTNode transform(KLabel kLabel) throws TransformerException {
			return new KApp(
                    kLabel.getLocation(),
                    kLabel.getFilename(),
                    new KInjectedLabel(kLabel),
                    KList.EMPTY);
		}

		@Override
		public ASTNode transform(Constant cst) throws TransformerException {
            assert false : "deprecated class";
            return null;
		}

		@Override
		public ASTNode transform(Empty emp) {
			String l = emp.getLocation();
			String f = emp.getFilename();
			if (!MetaK.isComputationSort(emp.getSort())) {
				return KApp.of(new KInjectedLabel(emp));
			}
			// if this is a list sort
			if (!MaudeHelper.basicSorts.contains(emp.getSort())) {
				Production listProd = DefinitionHelper.listConses.get(emp.getSort());
				String separator = ((UserList) listProd.getItems().get(0)).getSeparator();
				return new KApp(l, f, KLabelConstant.of(MetaK.getListUnitLabel(separator)), KList.EMPTY);
				// Constant cst = new Constant(l, f, KSorts.KLABEL, "'." + emp.getSort() + "");
				// return new KApp(l, f, cst, new Empty(l, f, MetaK.Constants.KList));
			}
			return emp;
		}

		@Override
		public ASTNode transform(Collection node) throws TransformerException {
			if (node instanceof KSequence)
				return super.transform(node);
			return KApp.of(new KInjectedLabel((Term) node.accept(trans)));
		}

		@Override
		public ASTNode transform(CollectionItem node) throws TransformerException {
			return KApp.of(new KInjectedLabel((Term) node.accept(trans)));
		}

		@Override
		public ASTNode transform(MapItem node) throws TransformerException {
			return KApp.of(new KInjectedLabel((Term) node.accept(trans)));
		}

		@Override
		public ASTNode transform(Cell node) throws TransformerException {
			return KApp.of(new KInjectedLabel((Term) node.accept(trans)));
		}

		@Override
		public ASTNode transform(Variable node) throws TransformerException {
			if (node.getSort().equals(KSorts.KITEM) || node.getSort().equals(KSorts.K)) {
				return node;
            }
            if (MetaK.isKSort(node.getSort())) {
				return KApp.of(new KInjectedLabel(node));
            }

            if (node.getSort().equals(BoolBuiltin.SORT_NAME)
                    || node.getSort().equals(IntBuiltin.SORT_NAME)
                    || node.getSort().equals(FloatBuiltin.SORT_NAME)
                    || node.getSort().equals(StringBuiltin.SORT_NAME)) {
                return node;
            }
			node = node.shallowCopy();
			node.setSort(KSorts.KITEM);
			return node;
		}
	}
}
