package ro.uaic.info.fmse.utils.strings;

public class StringUtil {

	public static String escape(String tag) {
		return tag.replaceAll("([\\(\\)\\[\\]\\{\\},\\s`])", "`$1");
	}

}
