package ro.uaic.info.fmse.compile;

import java.util.ArrayList;
import java.util.List;

import ro.uaic.info.fmse.compile.utils.MetaK;
import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Configuration;
import ro.uaic.info.fmse.k.Context;
import ro.uaic.info.fmse.k.Definition;
import ro.uaic.info.fmse.k.Module;
import ro.uaic.info.fmse.k.PriorityBlock;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.ProductionItem;
import ro.uaic.info.fmse.k.Rule;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.Syntax;
import ro.uaic.info.fmse.k.Terminal;
import ro.uaic.info.fmse.visitors.CopyOnWriteTransformer;

public class AddTopCell extends CopyOnWriteTransformer implements CompilerStep {

	@Override
	public Definition compile(Definition def) {
		ASTNode result =  def.accept(this);
		if (result == null) { 
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.COMPILER, 
					"Expecting definition, but got null while transforming. Returning the untransformed ", 
					def.getFilename(), def.getLocation(), 0));					
			return def;
		}
		if (!(result instanceof Definition)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Term, but got " + result.getClass() + " while transforming.", 
					def.getFilename(), def.getLocation(), 0));					
		}
		return (Definition) result;
	}

	@Override
	public String getName() {
		return "Add Top cell";
	}
	
	
	@Override
	public ASTNode transform(Module node) {
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
