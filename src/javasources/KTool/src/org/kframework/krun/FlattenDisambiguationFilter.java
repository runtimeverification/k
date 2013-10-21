package org.kframework.krun;

import java.util.ArrayList;
import java.util.List;

import org.kframework.compile.utils.MetaK;
import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KLabelConstant;
import org.kframework.kil.KList;
import org.kframework.kil.ListTerminator;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Context;
import org.kframework.kil.visitors.CopyOnWriteTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;

public class FlattenDisambiguationFilter extends CopyOnWriteTransformer {
	public FlattenDisambiguationFilter(Context context) {
		super("Reflatten ambiguous syntax", context);
	}

	@Override
	public ASTNode transform(Ambiguity amb) throws TransformerException {
		
		if (amb.getContents().get(0) instanceof TermCons) {
			TermCons t1 = (TermCons)amb.getContents().get(0);
			if (MetaK.isComputationSort(t1.getSort())) {
				if (t1.getProduction().isListDecl()) {
					Term t2 = t1.getContents().get(1);
					UserList ul = (UserList)t1.getProduction().getItems().get(0);
					if (context.isSubsortedEq(ul.getSort(), t2.getSort())) {
						t1.getContents().set(1, addEmpty(t2, t1.getSort()));
					}
					if (t2 instanceof Empty) {
						t1.getContents().set(1, new ListTerminator(ul.getSeparator()));
					}
				}
				return new KApp(
                        KLabelConstant.of(t1.getProduction().getKLabel(), context),
                        (Term) new KList(t1.getContents()).accept(this));
			}
		} else if (amb.getContents().get(0) instanceof Empty) {
			Empty t1 = (Empty)amb.getContents().get(0);
			if (MetaK.isComputationSort(t1.getSort())) {
				return new ListTerminator(((UserList) context.listConses.get(t1.getSort()).getItems().get(0)).getSeparator());
			}
		}
		return amb;
	}

	private Term addEmpty(Term node, String sort) {
		TermCons tc = new TermCons(sort, context.listConses.get(sort).getCons(), context);
		List<Term> contents = new ArrayList<Term>();
		contents.add(node);
		contents.add(new Empty(sort));
		tc.setContents(contents);
		return tc;
	}
}
