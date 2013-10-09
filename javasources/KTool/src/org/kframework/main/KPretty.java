package org.kframework.main;

import org.kframework.kil.Term;
import org.kframework.kil.loader.Context;
import org.kframework.backend.unparser.UnparserFilter;
import org.kframework.krun.ColorSetting;
import org.kframework.utils.kastparser.KastParser;

public class KPretty {

	public static void main(String[] args) {
		try {
			String kast = args[0];
			Context context = new Context();
			Term t = KastParser.parse(kast, context);
			UnparserFilter unparser = new UnparserFilter(false, ColorSetting.OFF, false, context);
			t.accept(unparser);
			System.out.println(unparser.getResult());
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
}
