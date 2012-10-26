package org.kframework.parser.generator.loader;

import java.util.HashSet;
import java.util.Set;

public class FollowRestrictionsForTerminals {

	public static String getFollowRestrictionsForTerminals(Set<String> terminals) {
		Set<Ttuple> mytuples = new HashSet<Ttuple>();
		String varid = "[A-Z][^:\\;\\(\\)\\<\\>\\~\\n\\r\\t\\,\\ \\[\\]\\=\\+\\-\\*\\/\\|\\{\\}\\.]*";

		for (String t1 : terminals) {
			for (String t2 : terminals) {
				if (!t1.equals(t2)) {
					if (t1.startsWith(t2)) {
						Ttuple tt = new Ttuple();
						tt.key = t1;
						tt.value = t2;
						String ending = tt.key.substring(tt.value.length());
						if (ending.matches(varid))
							mytuples.add(tt);
					}
				}
			}
		}

		String sdf = "lexical restrictions\n";
		sdf += "	%% follow restrictions\n";
		for (Ttuple tt : mytuples) {
			sdf += "	\"" + tt.value + "\" -/- ";
			String ending = tt.key.substring(tt.value.length());
			for (int i = 0; i < ending.length(); i++) {
				String ch = "" + ending.charAt(i);
				if (ch.matches("[a-zA-Z]"))
					sdf += "[" + ch + "].";
				else
					sdf += "[\\" + ch + "].";
			}
			sdf = sdf.substring(0, sdf.length() - 1) + "\n";
		}

		return sdf;
	}

	/**
	 * Using this class to collect the prefixes amongst terminals
	 * 
	 * @author RaduFmse
	 * 
	 */
	private static class Ttuple {
		public String key;
		public String value;

		public boolean equals(Object o) {
			if (o.getClass() == Ttuple.class)
				return false;
			Ttuple tt = (Ttuple) o;
			if (key.equals(tt.key) && value.equals(tt.value))
				return true;
			return false;
		}

		public int hashCode() {
			return key.hashCode() + value.hashCode();
		}
	}
}