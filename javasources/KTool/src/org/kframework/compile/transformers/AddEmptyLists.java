package org.kframework.compile.transformers;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.kframework.kil.ASTNode;
import org.kframework.kil.Empty;
import org.kframework.kil.Production;
import org.kframework.kil.Sort;
import org.kframework.kil.Term;
import org.kframework.kil.TermCons;
import org.kframework.kil.UserList;
import org.kframework.kil.loader.Constants;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.kil.visitors.BasicTransformer;
import org.kframework.kil.visitors.exceptions.TransformerException;
import org.kframework.utils.errorsystem.KException;
import org.kframework.utils.errorsystem.KMessages;
import org.kframework.utils.errorsystem.KException.ExceptionType;
import org.kframework.utils.errorsystem.KException.KExceptionGroup;
import org.kframework.utils.general.GlobalSettings;

public class AddEmptyLists extends BasicTransformer {

	public AddEmptyLists() {
		super("Add empty lists");
	}

	@Override
	public ASTNode transform(TermCons node) throws TransformerException {

		// traverse
		TermCons tc = (TermCons) super.transform(node);

		Production production = tc.getProduction();
		// System.out.println("TermCons: " + tc);
		// System.out.println("Production: " + production);

		int i = 0, j = 0;
		while (!(i >= production.getItems().size() || j >= tc.getContents().size())) {
			// System.out.println("Compare: ");
			// System.out.println("\tPItem: " +
			// production.getItems().get(i));
			// System.out.println("\tTItem: " + tc.getContents().get(j));
			if (production.getItems().get(i) instanceof Sort) {
				// if the sort of the j-th term is a list sort
				String psort = production.getItems().get(i).toString();
				String tsort = tc.getContents().get(j).getSort();

				if (!psort.equals(tsort)) {
					if (isListSort(psort) && subsort(tsort, psort)) {
						List<Term> genContents = new LinkedList<Term>();
						genContents.add(tc.getContents().get(j));
						genContents.add(new Empty(psort));

						tc.getContents().set(j, new TermCons(psort, getListCons(psort), genContents));
						// System.out.println("Adding cons at "
						// + tc.getLocation());
					}

					if (!subsort(tsort, psort) && isListSort(psort)) {
						boolean avoid = false;

						if (isListSort(psort) && isListSort(tsort)) {
							UserList ps = (UserList) (DefinitionHelper.listConses.get(psort).getItems().get(0));
							UserList ts = (UserList) (DefinitionHelper.listConses.get(tsort).getItems().get(0));

							if (ps.getSeparator().equals(ts.getSeparator()))
								avoid = true;
						}

						if (!avoid) {
							GlobalSettings.kem.register(new KException(ExceptionType.HIDDENWARNING, KExceptionGroup.LISTS, KMessages.WARNING1000, new File(tc.getFilename()).getName(), tc.getLocation()));
						}
					}
				}
				j++;
			}
			i++;
		}

		// System.out.println("\n\n");
		return tc;
	}

	private String getListCons(String psort) {
		Production p = DefinitionHelper.listConses.get(psort);
		return p.getAttributes().get(Constants.CONS_cons_ATTR);
	}

	private boolean subsort(String tsort, String psort) {
		return DefinitionHelper.isSubsorted(psort, tsort);
	}

	public boolean isListSort(String sort) {
		return DefinitionHelper.listConses.containsKey(sort);
	}
}
