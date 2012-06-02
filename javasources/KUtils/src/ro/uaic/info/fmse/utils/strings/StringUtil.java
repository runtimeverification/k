package ro.uaic.info.fmse.utils.strings;

public class StringUtil {

	public static String escape(String tag) {
		return tag.replaceAll("([\\(\\)\\[\\]\\{\\},\\s`])", "`$1");
	}

	public static String latexify(String name) {
		return name.replace("_","\\_").replace("{","\\{").replace("}", "\\}").replace("#", "\\#").replace("%", "\\%").replace(
				"$", "\\$").replace("&", "\\&").replace("~", "\\mbox{\\~{}}").replace("^", "\\mbox{\\^{}}");
	}

}
