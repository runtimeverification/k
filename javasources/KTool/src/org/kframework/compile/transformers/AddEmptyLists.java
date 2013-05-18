package org.kframework.compile.transformers;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Empty;
import org.kframework.kil.KApp;
import org.kframework.kil.KSorts;
import org.kframework.kil.Production;
import org.kframework.kil.ProductionItem;
import org.kframework.kil.ProductionItem.ProductionType;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.Token;
import org.kframework.kil.UserList;
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

/**
 * Transformer class adding the implicit terminator (.List{"SEP"}) to user defined lists.
 */
public class AddEmptyLists extends BasicTransformer {

	public AddEmptyLists(DefinitionHelper definitionHelper) {
		super("Add empty lists", definitionHelper);
	}

	@Override
	public ASTNode transform(TermCons tc) throws TransformerException {
		// traverse
		Production p = tc.getProduction();

		if (p.isListDecl()) {
			Term t = tc.getContents().get(0);
			UserList ul = (UserList) p.getItems().get(0);
			if (isAddEmptyList(ul.getSort(), t.getSort())) {
				if (!isUserListElement(ul.getSort(), t, definitionHelper)) {
					String msg = "Found sort '" + t.getSort() + "' where list sort '" + ul.getSort() + "' was expected. Moving on.";
					GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, msg, t.getFilename(), t.getLocation()));
				} else
					tc.getContents().set(0, addEmpty(t, ul.getSort()));
			}

			// if the term should be a list, append the empty element
			t = tc.getContents().get(1);
			if (isAddEmptyList(p.getSort(), t.getSort())) {
				if (!isUserListElement(p.getSort(), t, definitionHelper)) {
					String msg = "Found sort '" + t.getSort() + "' where list sort '" + p.getSort() + "' was expected. Moving on.";
					GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, msg, t.getFilename(), t.getLocation()));
				} else
					tc.getContents().set(1, addEmpty(t, tc.getProduction().getSort()));
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
					if (isAddEmptyList(srt, t.getSort())) {
						if (!isUserListElement(srt, t, definitionHelper)) {
							String msg = "Found sort '" + t.getSort() + "' where list sort '" + srt + "' was expected. Moving on.";
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

    private boolean isUserListElement(String listSort, Term element, DefinitionHelper definitionHelper) {
        String elementSort = element.getSort();

        /* TODO: properly infer sort of KApp */
        if (elementSort.equals(KSorts.K) && element instanceof KApp) {
            /* infer sort for builtins and tokens */
            if (((KApp) element).getLabel() instanceof Token) {
                elementSort = ((Token) ((KApp) element).getLabel()).tokenSort();
            }
        }

        return !elementSort.equals(KSorts.K)
               && definitionHelper.isSubsortedEq(listSort, elementSort);
    }

	public boolean isAddEmptyList(String expectedSort, String termSort) {
		if (!definitionHelper.isListSort(expectedSort))
			return false;
		if (definitionHelper.isSubsortedEq(expectedSort, termSort) && definitionHelper.isListSort(termSort))
			return false;
		return true;
	}

	private Term addEmpty(Term node, String sort) {
		TermCons tc = new TermCons(sort, getListCons(sort), definitionHelper);
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
