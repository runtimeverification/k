package ro.uaic.info.fmse.k2m.main;

public class StringUtil {

	public static String escape(String tag) {
		return tag.replaceAll("([\\(\\)\\[\\]\\{\\},\\s`])", "`$1");
	}

}
