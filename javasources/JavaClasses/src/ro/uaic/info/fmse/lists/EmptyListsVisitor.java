package ro.uaic.info.fmse.lists;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import ro.uaic.info.fmse.errorsystem.KException;
import ro.uaic.info.fmse.errorsystem.KException.ExceptionType;
import ro.uaic.info.fmse.errorsystem.KException.KExceptionGroup;
import ro.uaic.info.fmse.errorsystem.KMessages;
import ro.uaic.info.fmse.general.GlobalSettings;
import ro.uaic.info.fmse.k.ASTNode;
import ro.uaic.info.fmse.k.Empty;
import ro.uaic.info.fmse.k.Production;
import ro.uaic.info.fmse.k.Sort;
import ro.uaic.info.fmse.k.Term;
import ro.uaic.info.fmse.k.TermCons;
import ro.uaic.info.fmse.k.UserList;
import ro.uaic.info.fmse.loader.Constants;
import ro.uaic.info.fmse.loader.DefinitionHelper;
import ro.uaic.info.fmse.visitors.BasicTransformer;

public class EmptyListsVisitor extends BasicTransformer {

	@Override
	public ASTNode transform(TermCons node) {

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
						genContents.add(new Empty("generated", "generated", psort));

						tc.getContents().set(j, new TermCons("generated", "generated", psort, getListCons(psort), genContents));
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
							GlobalSettings.kem.register(new KException(ExceptionType.WARNING, KExceptionGroup.LISTS, KMessages.WARNING1000, new File(tc.getFilename()).getName(), tc.getLocation(), 0));
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
		String cons = p.getAttributes().get(Constants.CONS_cons_ATTR);
		return cons.substring(1, cons.length() - 1);
	}

	private boolean subsort(String tsort, String psort) {
		return DefinitionHelper.isSubsorted(psort, tsort);
	}

	public boolean isListSort(String sort) {
		return DefinitionHelper.listConses.containsKey(sort);
	}
}
