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
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Subsort;
import org.kframework.kil.visitors.BasicVisitor;

public class DefinitionSDFVisitor extends BasicVisitor {

	private List<Production> outsides = new ArrayList<Production>();
	private List<Production> constants = new ArrayList<Production>();
	private Set<Sort> startSorts = new HashSet<Sort>(); // list of sorts that are start symbols
	private Set<Subsort> subsorts = new HashSet<Subsort>();
	private Set<Production> listProds = new HashSet<Production>(); // list of sorts declared as being list
	private Set<Sort> userSorts = new HashSet<Sort>(); // list of sorts declared by the user (to be declared later as Start symbols if no declaration for Start was found)

	public DefinitionSDFVisitor() {
	}

	public void visit(Syntax syn) {

		userSorts.add(syn.getSort());
		List<PriorityBlock> prilist = new ArrayList<PriorityBlock>();
		for (PriorityBlock prt : syn.getPriorityBlocks()) {
			PriorityBlock p = new PriorityBlock();
			p.setAssoc(prt.getAssoc());

			// filter the productions according to their form
			for (Production prd : prt.getProductions()) {
				if (prd.getAttributes().containsKey("onlyLabel")) {
					// if a production has this attribute, don't add it to the list
				} else if (prd.isSubsort()) {
					outsides.add(prd);
					subsorts.add(new Subsort(prd.getSort(), ((Sort) prd.getItems().get(0)).getName()));
					if (prd.getSort().equals(new Sort("Start")))
						startSorts.add((Sort) prd.getItems().get(0));
					// add the small sort to the user sorts to add it to the variable declarations
					userSorts.add((Sort) prd.getItems().get(0));
				} else if (prd.getItems().get(0).getType() == ProductionType.TERMINAL && prd.getItems().size() == 1 && prd.isConstant()) {
					constants.add(prd);
				} else if (prd.getItems().get(0).getType() == ProductionType.TERMINAL && prd.getItems().get(prd.getItems().size() - 1).getType() == ProductionType.TERMINAL) {
					outsides.add(prd);
				} else if (prd.isListDecl()) {
					outsides.add(prd);
					listProds.add(prd);
					subsorts.add(new Subsort(prd.getSort(), ((UserList) prd.getItems().get(0)).getSort()));
				} else {
					p.getProductions().add(prd);
				}
			}
			if (p.getProductions().size() > 0)
				prilist.add(p);
		}
	}
}
