package ro.uaic.fmse.k2m.main;

public class StringUtil {

	public static String escape(String tag) {
		return tag.replaceAll("([\\(\\)\\[\\]\\{\\},\\s`])", "`$1");
	}

}
