package org.kframework.main;

import org.kframework.kil.Term;
import org.kframework.kil.loader.DefinitionHelper;
import org.kframework.backend.unparser.AddBracketsFilter;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.utils.kastparser.KastParser;

public class KPretty {

	public static void main(String[] args) {
		try {
			String kast = args[0];
			DefinitionHelper definitionHelper = new DefinitionHelper();
			Term t = KastParser.parse(kast);
			UnparserFilter unparser = new UnparserFilter(false, false, false, definitionHelper);
			t.accept(unparser);
			System.out.println(unparser.getResult());
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
