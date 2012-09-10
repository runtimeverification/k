package ro.uaic.info.fmse.sharing;

import java.util.LinkedList;
import java.util.List;

import ro.uaic.info.fmse.exceptions.TransformerException;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Import;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.PriorityBlock;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Terminal;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class AutomaticModuleImportsTransformer extends BasicTransformer {

	@Override
	public ASTNode transform(Module node) throws TransformerException {
		if (!node.getName().equals("SHARED"))
			node.appendModuleItem(new Import("SHARED"));
		else node.appendModuleItem(new Import("K"));
		if (!node.isPredefined() && !node.getName().equals("SHARED"))
			node.appendModuleItem(new Import("URIS"));
		return super.transform(node);
	}
	
	@Override
	public ASTNode transform(Definition node) throws TransformerException {
		
		SharedDataCollector sdc = new SharedDataCollector();
		node.accept(sdc);
		
		/**
		 *  create a new module called SHARED which
		 *  declares klabels, sorts, subsorts to K
		 *  and cell labels. 
		 */

		// K labels
		Sort KLabel = new Sort("KLabel");
		List<PriorityBlock> priorities = new LinkedList<PriorityBlock>();
		PriorityBlock pb = new PriorityBlock();
		List<Production> kLabelProductions = new LinkedList<Production>();
		for(String s : sdc.kLabels)
		{
			LinkedList<ProductionItem> prod = new LinkedList<ProductionItem>();
			prod.add(new Terminal(s));
			kLabelProductions.add(new Production(KLabel, prod));
		}
		pb.setProductions(kLabelProductions);
		priorities.add(pb);
		Syntax kLabelsDeclaration = new Syntax(KLabel, priorities);

		// cell labels
		Sort CellLabel = new Sort("CellLabel");
		List<PriorityBlock> lpriorities = new LinkedList<PriorityBlock>();
		PriorityBlock lpb = new PriorityBlock();
		List<Production> cellLabelProductions = new LinkedList<Production>();
		for(String s : sdc.cellLabels)
		{
			LinkedList<ProductionItem> prod = new LinkedList<ProductionItem>();
			prod.add(new Terminal(s));
			cellLabelProductions.add(new Production(CellLabel, prod));
		}
		lpb.setProductions(cellLabelProductions);
		lpriorities.add(lpb);
		Syntax cellLabelsDeclaration = new Syntax(CellLabel, lpriorities);

		// cell labels
		Sort K = new Sort("K");
		List<PriorityBlock> kpriorities = new LinkedList<PriorityBlock>();
		PriorityBlock kpb = new PriorityBlock();
		List<Production> kProductions = new LinkedList<Production>();
		for(String s : sdc.sorts)
		{
			LinkedList<ProductionItem> prod = new LinkedList<ProductionItem>();
			prod.add(new Sort(s));
			kProductions.add(new Production(K, prod));
		}
		kpb.setProductions(kProductions);
		kpriorities.add(kpb);
		Syntax kDeclaration = new Syntax(K, kpriorities);
		
		
		Module shared = new Module("SHARED", "module", false);
		shared.appendModuleItem(kLabelsDeclaration);
		shared.appendModuleItem(cellLabelsDeclaration);
		shared.appendModuleItem(kDeclaration);

		node.appendBeforeDefinitionItem(shared);
		
		return super.transform(node);
	}
}
