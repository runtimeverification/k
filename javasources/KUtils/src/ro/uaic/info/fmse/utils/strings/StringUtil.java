package ro.uaic.info.fmse.utils.strings;

public class StringUtil {
	public static String unescape(String str) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < str.length(); i++) {
			if (str.charAt(i) == '\\') {
				if (str.charAt(i + 1) == '\\')
					sb.append('\\');
				else if (str.charAt(i + 1) == 'n')
					sb.append('\n');
				else if (str.charAt(i + 1) == 'r')
					sb.append('\r');
				else if (str.charAt(i + 1) == 't')
					sb.append('\t');
				i++;
			} else
				sb.append(str.charAt(i));
		}

		return sb.toString();
	}

	public static String escape(String tag) {
		return tag.replaceAll("([\\(\\)\\[\\]\\{\\},\\s`])", "`$1");
	}

	public static String latexify(String name) {
		return name.replace("\\", "\\textbackslash ")
		.replace("_", "\\_").replace("{", "\\{").replace("}", "\\}")
		.replace("#", "\\#").replace("%", "\\%").replace("$", "\\$")
		.replace("&", "\\&").replace("~", "\\mbox{\\~{}}").replace("^", "\\mbox{\\^{}}")
		.replace("`", "\\`{}");
	}

	public static String emptyIfNull(String string) {
		if (string == null) return "";
		return string;
	}
}
