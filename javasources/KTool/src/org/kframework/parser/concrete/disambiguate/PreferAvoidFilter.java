package org.kframework.parser.concrete.disambiguate;

import java.util.ArrayList;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class PreferAvoidFilter extends BasicTransformer {
	public PreferAvoidFilter(Context context) {
		super("Ambiguity filter", context);
	}

	public ASTNode transform(Ambiguity amb) throws TransformerException {
		java.util.List<Term> prefer = new ArrayList<Term>();
		java.util.List<Term> avoid = new ArrayList<Term>();

		for (ASTNode variant : amb.getContents()) {
			if (variant instanceof TermCons) {
				TermCons tc = (TermCons) variant;
				if (tc.getProduction().getAttributes().containsKey("prefer"))
					prefer.add(tc);
				if (tc.getProduction().getAttributes().containsKey("avoid"))
					avoid.add(tc);
			}
		}

		ASTNode result = amb;

		if (!prefer.isEmpty()) {
			if (prefer.size() == 1)
				result = prefer.get(0);
			else {
				amb.setContents(prefer);
			}
		} else if (!avoid.isEmpty()) {
			if (avoid.size() < amb.getContents().size()) {
				amb.getContents().removeAll(avoid);
				if (amb.getContents().size() == 1)
					result = amb.getContents().get(0);
			}
		}

		if (result == amb)
			return super.transform(result);
		else
			return result.accept(this);
	}
}
