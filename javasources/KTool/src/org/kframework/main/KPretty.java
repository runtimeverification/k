package org.kframework.main;

import org.kframework.kil.Term;
import org.kframework.backend.unparser.AddBracketsFilter;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.utils.kastparser.KastParser;

public class KPretty {

	public static void main(String[] args) {
		try {
			String kast = args[0];
			Term t = KastParser.parse(kast);
			UnparserFilter unparser = new UnparserFilter(false, false, false);
			t.accept(unparser);
			System.out.println(unparser.getResult());
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
