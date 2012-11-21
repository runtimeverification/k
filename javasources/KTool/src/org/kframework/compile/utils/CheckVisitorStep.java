package org.kframework.compile.utils;

import org.kframework.kil.Definition;
import org.kframework.kil.visitors.Visitor;


public class CheckVisitorStep implements CheckStep {

	Visitor t;

	public CheckVisitorStep(Visitor t) {
		this.t = t;
	}

	@Override
	public boolean check(Definition def) {
		try {
			def.accept(t);
		} catch (Exception e) {
			e.printStackTrace();
			return false;
		}
		return true;
	}

	@Override
	public String getName() {
		return t.getName();
	}

}
