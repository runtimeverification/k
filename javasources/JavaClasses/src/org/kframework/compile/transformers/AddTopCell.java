package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Configuration;
import org.kframework.kil.Context;
import org.kframework.kil.Module;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.Rule;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.Terminal;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;

public class AddTopCell extends CopyOnWriteTransformer {

	public AddTopCell() {
		super("Add top cell");
		// TODO Auto-generated constructor stub
	}
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		ASTNode result = super.transform(node);
		if (result == node) return node;
		if (result == null) { 
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.COMPILER, 
					"Expecting Module, but got null while transforming. Returning the untransformed ", 
					node.getFilename(), node.getLocation(), 0));					
			return node;
		}
		if (!(result instanceof Module)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Module, but got " + result.getClass() + " while transforming.", 
					node.getFilename(), node.getLocation(), 0));	
			return node;
		}
		node = (Module) result;
		List<PriorityBlock> topCellBlocks = new ArrayList<PriorityBlock>();
		PriorityBlock topPriorityBlock = new PriorityBlock();
		List<ProductionItem> topTerminals = new ArrayList<ProductionItem>();
		topTerminals.add(new Terminal("generatedTop"));
		Production topProduction = new Production(new Sort("CellLabel"), topTerminals );
		topPriorityBlock.getProductions().add(topProduction);
		topCellBlocks.add(topPriorityBlock);
		Syntax topCellDecl = new Syntax(new Sort("CellLabel"), topCellBlocks );
		node.getItems().add(topCellDecl);
		return node;
	}
	
	@Override
	public ASTNode transform(Rule node) {
		if (MetaK.isAnywhere(node)) return node;
		if (!MetaK.hasCell(node.getBody())) return node; 
		node = node.shallowCopy();
		node.setBody(MetaK.wrap(node.getBody(),"generatedTop","both"));
		return node;
	}
	
	@Override
	public ASTNode transform(Configuration node) {
		node = node.shallowCopy();
		node.setBody(MetaK.wrap(node.getBody(),"generatedTop","none"));
		return node;
	}
	
	@Override
	public ASTNode transform(Context node) {
		return node;
	}

	@Override
	public ASTNode transform(Syntax node) {
		return node;
	}

}
