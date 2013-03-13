package org.kframework.parser.concrete.disambiguate;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Ambiguity;
import org.kframework.kil.Bracket;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Rewrite;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicHookWorker;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;

public class TypeSystemFilter2 extends BasicHookWorker {

	private String maxSort;

	public TypeSystemFilter2(String maxSort) {
		super("Type system");
		this.maxSort = maxSort;
	}

	public TypeSystemFilter2(TypeSystemFilter2 tsf) {
		super("Type system");
		this.maxSort = tsf.maxSort;
	}

	public ASTNode transform(TermCons tc) throws TransformerException {
		// choose only the allowed subsorts for a TermCons
		if (tc.getProduction().getItems().get(0).getType() == ProductionType.USERLIST) {
			UserList ulist = (UserList) tc.getProduction().getItems().get(0);
			tc.getContents().set(0, (Term) tc.getContents().get(0).accept(new TypeSystemFilter2(ulist.getSort())));
			tc.getContents().set(1, (Term) tc.getContents().get(1).accept(new TypeSystemFilter2(tc.getProduction().getSort())));

		} else {
			int j = 0;
			Production prd = tc.getProduction();
			for (int i = 0; i < prd.getItems().size(); i++) {
				if (prd.getItems().get(i).getType() == ProductionType.SORT) {
					Sort sort = (Sort) prd.getItems().get(i);
					Term child = (Term) tc.getContents().get(j);
					tc.getContents().set(j, (Term) child.accept(new TypeSystemFilter2(sort.getName())));
					j++;
				}
			}
		}

		return tc;
	}

	public ASTNode transform(Term trm) throws TransformerException {
		if (maxSort != null) {
			if (!(maxSort.equals(trm.getSort()) || DefinitionHelper.isSubsorted(maxSort, trm.getSort()))) {
				String msg = "Type error detected. Expected sort " + maxSort + ", but found " + trm.getSort();
				KException kex = new KException(ExceptionType.ERROR, KExceptionGroup.CRITICAL, msg, trm.getFilename(), trm.getLocation());
				throw new TransformerException(kex);
			}
		}
		return trm;
	}

	@Override
	public ASTNode transform(Ambiguity node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Bracket node) throws TransformerException {
		return node;
	}

	@Override
	public ASTNode transform(Rewrite node) throws TransformerException {
		return node;
	}
}
