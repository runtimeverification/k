package org.kframework.compile.transformers;


import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Attribute;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.Module;
import org.kframework.kil.ModuleItem;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class GenerateSyntaxPredicates extends CopyOnWriteTransformer {
	
	public class SyntaxPredicatesVisitor extends BasicVisitor {
		List<ModuleItem> result = new ArrayList<ModuleItem>();
		Set<String> declarations = new HashSet<String>();
		Set<String> lists = new HashSet<String>();
				
		@Override
		public void visit(Module node) {
			lists.clear();
			super.visit(node);
			if (!lists.isEmpty()) {
				for (String lsort : lists) {
					Rule rule = new Rule();
					rule.setBody(new Rewrite(
							new KApp(new Constant("KLabel", "is" + lsort), 
									new Empty(lsort)), 
							new Constant("#Bool", "true")));
					rule.getAttributes().getContents().add(new Attribute("predicate", ""));
					result.add(rule);
					rule = new Rule();
					rule.setBody(new Rewrite(
							new KApp(new Constant("KLabel", "isKResult"), 
									new Empty(lsort)), 
							new Constant("#Bool", "true")));
					rule.getAttributes().getContents().add(new Attribute("predicate", ""));
					result.add(rule);
				}
			}
		}
		
		@Override
		public void visit(Syntax node) {
			String sort = node.getSort().getName();
			if (DefinitionHelper.isListSort(sort)) 
				lists.add(sort);
			if (MetaK.isKSort(sort)) return;
			super.visit(node);
		}
		
		@Override
		public void visit(Production node) {
			if (node.getAttributes().containsKey("bracket")) return;
			if (node.getAttributes().containsKey("function")) return;
			if (node.getAttributes().containsKey("predicate")) return;
			if (!declarations.contains("is" + node.getSort()))
				declarePredicate(node.getSort());
			Rule rule = new Rule();
			rule.setBody(new Rewrite(
					new KApp(new Constant("KLabel", "is" + node.getSort()), 
							MetaK.getTerm(node)), 
					new Constant("#Bool", "true")));
			rule.getAttributes().getContents().add(new Attribute("predicate", ""));
			result.add(rule);
		}


		private void declarePredicate(String sort) {
			{				
				Sort KLabel = new Sort("KLabel");
				List<PriorityBlock> priorities = new LinkedList<PriorityBlock>();
				PriorityBlock pb = new PriorityBlock();
				List<Production> kLabelProductions = new LinkedList<Production>();
//				for(String s : sdc.kLabels)
				{
					LinkedList<ProductionItem> prod = new LinkedList<ProductionItem>();
					prod.add(new Terminal("is" + sort));
					kLabelProductions.add(new Production(KLabel, prod));
				}
				pb.setProductions(kLabelProductions);
				priorities.add(pb);
				result.add(new Syntax(KLabel, priorities));
				declarations.add("is" + sort);
			}
		}
		
		@Override
		public void visit(Rule node) {
		}

		@Override
		public void visit(Context node) {
		}
		
		@Override
		public void visit(Configuration node) {
		}

		public List<ModuleItem> getResult() {
			return result;
		}
	}

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		SyntaxPredicatesVisitor moduleVisitor = new SyntaxPredicatesVisitor(); 
		node.accept(moduleVisitor);
		List<ModuleItem> predicates = moduleVisitor.getResult();
		if (predicates.isEmpty()) return node;
		node = node.shallowCopy();
		List<ModuleItem> items = new ArrayList<ModuleItem>(node.getItems());
		items.addAll(predicates);
		node.setItems(items);
		return node;
	}
	
	public GenerateSyntaxPredicates() {
		super("Generate syntax predicates");
	}

}
