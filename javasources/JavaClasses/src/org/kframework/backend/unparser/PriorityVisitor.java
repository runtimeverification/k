package org.kframework.backend.unparser;

import java.util.Map.Entry;

import org.kframework.kil.Definition;
import org.kframework.kil.PriorityBlock;
import org.kframework.kil.Production;
import org.kframework.kil.Syntax;
import org.kframework.kil.visitors.BasicVisitor;


public class PriorityVisitor extends BasicVisitor {
    public java.util.List<java.util.Map<Production, Integer>> priorities =
	new java.util.LinkedList<java.util.Map<Production, Integer>>();
    public java.util.Map<Production, Integer> currentPriority = 
	new java.util.HashMap<Production, Integer>();
    public int currentNumber = 0;

    public boolean before(Production p1, Production p2) {
	for (java.util.Map<Production, Integer> priority : priorities) {
	    Integer n1 = null;
	    Integer n2 = null;
	    for (Entry<Production, Integer> entry : priority.entrySet()) {
		if (p1.getCons().equals(entry.getKey().getCons())) {
		    n1 = entry.getValue();
		}
		if (p2.getCons().equals(entry.getKey().getCons())) {
		    n2 = entry.getValue();
		}
	    }
	    if (n1 != null && n2 != null) {
		return n1 < n2;
	    }
	}
	return false;
    }

    private void pushCurrentPriority() {
	priorities.add(currentPriority);
	currentPriority = new java.util.HashMap<Production, Integer>();
    }

    @Override
    public void visit(Definition definition) {
	super.visit(definition);
    }

    @Override
    public void visit(Syntax syntax) {
	super.visit(syntax);
	pushCurrentPriority();
    }

    @Override
    public void visit(PriorityBlock priorityBlock) {
	currentNumber++;
	super.visit(priorityBlock);
    }
    
    @Override
    public void visit(Production production) {
	currentPriority.put(production, currentNumber);
	super.visit(production);
    }
}
