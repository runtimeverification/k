package org.kframework.compile.transformers;

import org.kframework.kil.*;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

import java.util.ArrayList;
import java.util.List;

public class AddEmptyLists extends BasicTransformer {

	public AddEmptyLists(DefinitionHelper definitionHelper) {
		super("Add empty lists", definitionHelper);
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		// traverse
		Production p = tc.getProduction(definitionHelper);

		if (p.isListDecl()) {
			Term t = tc.getContents().get(0);
			UserList ul = (UserList) p.getItems().get(0);
			if (isAddEmptyList(ul.getSort(), t.getSort(definitionHelper))) {
				if (t.getSort(definitionHelper).equals("K") || !definitionHelper.isSubsortedEq(ul.getSort(), t.getSort(definitionHelper))) {
					String msg = "Found sort '" + t.getSort(definitionHelper) + "' where list sort '" + ul.getSort() + "' was expected. Moving on.";
					GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, msg, t.getFilename(), t.getLocation()));
				} else
					tc.getContents().set(0, addEmpty(t, ul.getSort()));
			}

			// if the term should be a list, append the empty element
			t = tc.getContents().get(1);
			if (isAddEmptyList(p.getSort(), t.getSort(definitionHelper))) {
				if (t.getSort(definitionHelper).equals("K") || !definitionHelper.isSubsortedEq(p.getSort(), t.getSort(definitionHelper))) {
					String msg = "Found sort '" + t.getSort(definitionHelper) + "' where list sort '" + p.getSort() + "' was expected. Moving on.";
					GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, msg, t.getFilename(), t.getLocation()));
				} else
					tc.getContents().set(1, addEmpty(t, tc.getProduction(definitionHelper).getSort()));
			}
		} else {
			for (int i = 0, j = 0; j < p.getItems().size(); j++) {
				ProductionItem pi = p.getItems().get(j);
				if (!(pi.getType() == ProductionType.SORT))
					continue;

				String srt = ((Sort) pi).getName();
				if (definitionHelper.isListSort(srt)) {
					Term t = (Term) tc.getContents().get(i);
					// if the term should be a list, append the empty element
					if (isAddEmptyList(srt, t.getSort(definitionHelper))) {
						if (t.getSort(definitionHelper).equals("K") || !definitionHelper.isSubsortedEq(srt, t.getSort(definitionHelper))) {
							String msg = "Found sort '" + t.getSort(definitionHelper) + "' where list sort '" + srt + "' was expected. Moving on.";
							GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, msg, t.getFilename(), t.getLocation()));
						} else
							tc.getContents().set(i, addEmpty(t, srt));
					}
				}
				i++;
			}
		}

		return super.transform(tc);
	}

	public boolean isAddEmptyList(String expectedSort, String termSort) {
		// if (termSort.equals("K"))
		// return false;
		if (!definitionHelper.isListSort(expectedSort))
			return false;
		if (definitionHelper.isSubsortedEq(expectedSort, termSort) && definitionHelper.isListSort(termSort))
			return false;
		return true;
	}

	private Term addEmpty(Term node, String sort) {
		TermCons tc = new TermCons(sort, getListCons(sort));
		List<Term> genContents = new ArrayList<Term>();
		genContents.add(node);
		genContents.add(new Empty(sort));

		tc.setContents(genContents);
		return tc;
	}

	private String getListCons(String psort) {
		Production p = definitionHelper.listConses.get(psort);
		return p.getAttribute(Constants.CONS_cons_ATTR);
	}
}
