package org.kframework.compile.transformers;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Stack;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Bag;
import org.kframework.kil.Cell;
import org.kframework.kil.Cell.Ellipses;
import org.kframework.kil.Cell.Multiplicity;
import org.kframework.kil.Configuration;
import org.kframework.kil.Constant;
import org.kframework.kil.Context;
import org.kframework.kil.Module;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Rule;
import org.kframework.kil.Syntax;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Variable;
import org.kframework.kil.visitors.BasicVisitor;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.Visitor;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class ResolveContextAbstraction extends CopyOnWriteTransformer {

	Map<String, ConfigurationStructure> config = new HashMap<String, ConfigurationStructure>();
	int maxLevel = 0;

	public ResolveContextAbstraction() {
		super("Resolve Context Abstraction");
	}
	
	
	@Override
	public ASTNode transform(Module node) throws TransformerException {
		Visitor visitor = new ConfigurationStructureVisitor();
		node.accept(visitor);
		if (config.isEmpty()) return node;
		return super.transform(node);
	}
	
	@Override
	public ASTNode transform(Configuration node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Syntax node) throws TransformerException {
		return node;
	}
	
	@Override
	public ASTNode transform(Context node) throws TransformerException {
		return node;
	}
	
	
	@Override
	public ASTNode transform(Rule node) throws TransformerException {
		boolean change = false;		
		if (MetaK.getTopCells(node.getBody()).isEmpty()) return node;
		Rule rule = (Rule) super.transform(node);
		
		SplitByLevelVisitor visitor = new SplitByLevelVisitor(-1);
		rule.getBody().accept(visitor);
		
		int min = visitor.max;
		for (int i=visitor.max-1; i>0; i--) {
			if (!visitor.levels.get(i).isEmpty()) min = i;  
		}
		 
		if (min < visitor.max) change = true;
		Cell parentCell = null;
		do {
			if (min < visitor.max) {
				bringToLevel(visitor, min);
				visitor.max = min;
			}
			LinkedList<Term> cells = visitor.levels.get(min);
			ConfigurationStructure parent = findParent(cells.peek());
			parentCell = createParentCell(parent, cells);
			if (!cells.isEmpty()) {
				assert(min>1);
				change = true;
				min--;
				visitor.levels.get(min).add(parentCell);
			}
		} while (min < visitor.max);
		if (change) {
			rule = rule.shallowCopy();
			rule.setBody(parentCell.getContents());
		}
		return rule;
	}
	
	@Override
	public ASTNode transform(Cell node) throws TransformerException {
		boolean change = false;
		Cell cell = (Cell)super.transform(node);
		if (cell.getEllipses() == Ellipses.NONE) return cell;
		ConfigurationStructure confCell = config.get(cell.getId());
		if (confCell == null)
		{
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.CRITICAL, 
					"Cell " + cell.getLabel() + " is not part of the configuration ", 
					node.getFilename(), node.getLocation()));
		}
		
		if (confCell.sons.isEmpty()) return cell;
		SplitByLevelVisitor visitor = new SplitByLevelVisitor(confCell.level);
		cell.getContents().accept(visitor);
		int min = 0;
		if (visitor.max>min) change = true;
		bringToLevel(visitor, min);
		LinkedList<Term> cells = visitor.levels.get(min);
		Cell parentCell = createParentCell(confCell, cells);
		assert(cells.isEmpty());
		if (change) cell = parentCell;
		return cell;
	}


	private void bringToLevel(SplitByLevelVisitor visitor, int level) {
		while (visitor.max > level) {
			LinkedList<Term> cells = visitor.levels.get(visitor.max);
			if (cells.isEmpty()) { visitor.max--; continue;}
			ConfigurationStructure parent = findParent(cells.peek());
			Cell parentCell = createParentCell(parent, cells);
			visitor.levels.get(visitor.max-1).add(parentCell);
		}
	}
	
	private Cell createParentCell(ConfigurationStructure parent,
			LinkedList<Term> cells) {
		Cell p = new Cell();
		p.setLabel(parent.cell.getLabel());
		p.setId(parent.id);
		Bag contents = new Bag();
		List<Term> items = new ArrayList<Term>();
		contents.setContents(items);
		p.setContents(contents);
		Ellipses e = fillParentItems(parent, cells, items);
		p.setEllipses(e);
		return p;
	}


	private Ellipses fillParentItems(ConfigurationStructure parent, LinkedList<Term> cells, List<Term> items) {
		Map<String, ConfigurationStructure> potentialSons = new HashMap<String, ConfigurationStructure>(parent.sons);
		ListIterator<Term> i = cells.listIterator();
		while (i.hasNext()) {
			Term t = i.next();
			List<Cell> inCells = MetaK.getTopCells(t);
			boolean allAvailable = true;
			for (Cell cell : inCells) {
				if (!potentialSons.containsKey(cell.getId())) {
					allAvailable = false;
					break;
				}
			}
			if (allAvailable) {
				for (Cell cell : inCells) {
					ConfigurationStructure cellCfg = potentialSons.get(cell.getId());
					if (cellCfg == null) {
						GlobalSettings.kem.register(new KException(ExceptionType.WARNING, 
								KExceptionGroup.INTERNAL, 
								"Cell " + cell + " appears more than its multiplicity in " + t + " while " + getName(), 
								t.getFilename(), t.getLocation()));								
						continue;
					}
					if (cellCfg.multiplicity == Multiplicity.MAYBE || cellCfg.multiplicity == Multiplicity.ONE) 
						potentialSons.remove(cell.getId());
				}				
				items.add(t);
				i.remove();
			}
		}
		if (potentialSons.isEmpty()) return Ellipses.NONE;
		return Ellipses.BOTH;
	}


	private ConfigurationStructure findParent(Term t) {
		if (t instanceof Cell) {
			 return config.get(((Cell)t).getId()).parent; 
		}
		if (!(t instanceof Rewrite)) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting Rewrite, but got " + t.getClass() + " while " + getName(), 
					t.getFilename(), t.getLocation()));					
			
		}
		List<Cell> cells = MetaK.getTopCells(t);
		if (cells.isEmpty()) {
			GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
					KExceptionGroup.INTERNAL, 
					"Expecting some cells in here, but got none while " + getName(), 
					t.getFilename(), t.getLocation()));								
		}
		Iterator<Cell> i = cells.iterator();
		ConfigurationStructure parent = config.get(i.next().getId()).parent;
		while (i.hasNext()) {
			if (parent != config.get(i.next().getId()).parent) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.INTERNAL, 
						"Not all cells " + cells + "have parent " + parent + " while " + getName(), 
						t.getFilename(), t.getLocation()));								
				
			}
		}
		return parent;
	}

	public class ConfigurationStructure {
		Cell cell;
		String id;
		ConfigurationStructure parent = null;
		Map<String,ConfigurationStructure> sons = new HashMap<String, ConfigurationStructure>();
		Multiplicity multiplicity;
		int level = 0;
	}
	
	
	private class SplitByLevelVisitor extends BasicVisitor {
		ArrayList<LinkedList<Term>> levels;
		private int level;
		private int max;
		
		public SplitByLevelVisitor(int level) {
			levels = new ArrayList<LinkedList<Term>>(maxLevel-level + 1);
			for (int i=0; i<=maxLevel-level; i++) levels.add(new LinkedList<Term>());
			this.level = level + 1;
			max = 0;
		}
		
		@Override
		public void visit(Cell node) {
			int level = config.get(node.getId()).level - this.level;
			if (level < 0) {
				GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
						KExceptionGroup.INTERNAL, 
						"Cell " + node + " Has a higher level than its parent while " + getName(), 
						node.getFilename(), node.getLocation()));								
				
			}
			if (max<level) max = level;
			levels.get(level).add(node);
		}
		
		@Override
		public void visit(Constant node) {
			levels.get(0).add(node);
		}
		
		@Override
		public void visit(TermCons node) {
			levels.get(0).add(node);
		}
		
		@Override
		public void visit(Variable node) {
			levels.get(0).add(node);
		}
		
		@Override
		public void visit(Rewrite node) {
			List<Cell> cells = MetaK.getTopCells(node);
			int level = 0;
			if (!cells.isEmpty()) {
				Iterator<Cell> i = cells.iterator();
				level = config.get(i.next().getId()).level - this.level;
				assert(level >= 0);
				if (max < level) max = level;
				while(i.hasNext()) //Sanity check -- see that all cells in a rewrite are at the same level
					if (level != config.get(i.next().getId()).level - this.level) {
						GlobalSettings.kem.register(new KException(ExceptionType.ERROR, 
								KExceptionGroup.INTERNAL, 
								"Expecting all cells in " + node + " to be at the same level when " + getName(), 
								node.getFilename(), node.getLocation()));														
					}
			}
			levels.get(level).add(node);
		}
	}

	private class ConfigurationStructureVisitor extends BasicVisitor {
		
		Stack<ConfigurationStructure> ancestors = new Stack<ResolveContextAbstraction.ConfigurationStructure>();
		
		
		@Override
		public void visit(Configuration node) {
			Term t = node.getBody();
			Cell top = new Cell();
			top.setLabel("___CONTEXT_ABSTRACTION_TOP_CELL___");
			top.setContents(t);
			top.accept(this);
		}
		
		@Override
		public void visit(Cell node) {
			ConfigurationStructure cfg = new ConfigurationStructure();
			cfg.multiplicity = node.getMultiplicity();
			cfg.id = node.getId();
			cfg.cell = node;
			if (!ancestors.empty()) {
				ConfigurationStructure parent = ancestors.peek();
				cfg.level = parent.level+1;
				cfg.parent = parent;
				if (cfg.level > maxLevel) maxLevel = cfg.level;
				parent.sons.put(cfg.id, cfg);
			}
			ancestors.push(cfg);
			super.visit(node);
			ancestors.pop();
			config.put(cfg.id, cfg);
		}
		
		@Override
		public void visit(Context node) {
		}

		@Override
		public void visit(Syntax node) {
		}

		@Override
		public void visit(Rule node) {
		}
	}


}
