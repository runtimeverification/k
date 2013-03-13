package org.kframework.backend.symbolic;

import java.util.Iterator;
import java.util.Set;

import org.kframework.kil.Constant;
import org.kframework.kil.KApp;
import org.kframework.kil.Production;
import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicVisitor;

public class CheckSmtlibVisitor extends BasicVisitor {

	private boolean smtValid = false;

	public CheckSmtlibVisitor() {
		super("Check SMTLIB translation.");
	}
	
	public boolean smtValid() {
		return smtValid;
	}

	@Override
	public void visit(KApp node) {
		Term label = node.getLabel();
//		System.out.println("INSPECT: " + label);
		if (label instanceof Constant) {
			Set<Production> prods = DefinitionHelper.productions
					.get(((Constant) label).getValue().trim());
			if (prods == null) {
				smtValid = false;
			} else {
				Iterator<Production> it = prods.iterator();
				while (it.hasNext()) {
					Production p = it.next();
					if (p.containsAttribute("smtlib"))
						smtValid = true;
					else smtValid = false;
//					System.out.println("\t P:" + p + ", CHECK:" + p.containsAttribute("smtlib") + ", ATTR: " + smtValid);
					// stop after one step
					break;
				}
			}
		}
		
		super.visit(node);
	}
}
