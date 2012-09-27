package org.kframework.parser.generator.loader;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;

/**
 * Collect all the syntax declarations into containers according to their function.
 * 
 * @author Radu
 * 
 */
public class ProgramSDFVisitor extends BasicVisitor {

	public List<Production> outsides = new ArrayList<Production>();
	public List<Production> constants = new ArrayList<Production>();
	public Set<String> sorts = new HashSet<String>(); // list of inserted sorts that need to avoid the priority filter
	public Set<String> startSorts = new HashSet<String>(); // list of sorts that are start symbols
	public Set<String> listSorts = new HashSet<String>(); // list of sorts declared as being list
	public Set<String> userSort = new HashSet<String>(); // list of sorts declared by the user (to be declared later as Start symbols if no declaration for Start was found)

	public ProgramSDFVisitor() {
	}

	public void visit(Syntax syn) {

		userSort.add(syn.getSort().getName());
		List<PriorityBlock> prilist = new ArrayList<PriorityBlock>();
		for (PriorityBlock prt : syn.getPriorityBlocks()) {
			PriorityBlock p = new PriorityBlock();
			p.setAssoc(prt.getAssoc());

			// filter the productions according to their form
			for (Production prd : prt.getProductions()) {
				if (prd.isSubsort()) {
					outsides.add(prd);
					if (prd.getSort().equals("Start"))
						startSorts.add(((Sort) prd.getItems().get(0)).getName());
				} else if (prd.isConstant()) {
					constants.add(prd);
				} else if (prd.getItems().get(0).getType() == ProductionType.TERMINAL && prd.getItems().get(prd.getItems().size() - 1).getType() == ProductionType.TERMINAL) {
					outsides.add(prd);
				} else if (prd.getItems().get(0).getType() == ProductionType.USERLIST) {
					outsides.add(prd);
					listSorts.add(prd.getSort());
				} else {
					p.getProductions().add(prd);
				}
			}
			if (p.getProductions().size() > 0)
				prilist.add(p);
		}
	}
}
