package org.kframework.backend.symbolic;

import org.kframework.kil.ASTNode;
import org.kframework.kil.BoolBuiltin;
import org.kframework.kil.KApp;
import org.kframework.kil.KList;
import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class EliminateRRWrapper extends CopyOnWriteTransformer {

	Term lphi, rphi;
	
	public EliminateRRWrapper(Context context) {
		super("Filter condition: eliminate RRCondition wrapper", context);
	}

	@Override
	public ASTNode transform(KApp node) throws TransformerException {
		if (node.getLabel().toString().equals(ReachabilityRuleToKRule.RR_COND)) {
				KList contents = (KList) node.getChild();
				lphi = contents.getContents().get(0);
				rphi = contents.getContents().get(1);
				return BoolBuiltin.TRUE;
		}
		
		return super.transform(node);
	}

	public Term getLphi() {
		return lphi;
	}

	public Term getRphi() {
		return rphi;
	}
}
