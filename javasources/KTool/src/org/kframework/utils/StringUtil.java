package org.kframework.utils;

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

	public static String escape(String str) {
		str = str.replaceAll("\n", "\\n");
		str = str.replaceAll("\r", "\\r");
		str = str.replaceAll("\t", "\\t");
		str = str.replaceAll("\"", "\\\"");

		return str;
	}

	/**
	 * Use this function to print XML directly as string, and not when using DOM.
	 * @param str
	 * @return
	 */
	public static String escapeToXmlAttribute(String str) {
		str = str.replaceAll("\\", "\\\\");
		str = str.replaceAll("\n", "\\n");
		str = str.replaceAll("\r", "\\r");
		str = str.replaceAll("\t", "\\t");
		str = str.replaceAll("&", "&amp;");
		str = str.replaceAll("<", "&lt;");
		str = str.replaceAll(">", "&gt;");
		str = str.replaceAll("\"", "&quot;");
		return str;
	}

	public static String escapeSortName(String str) {
		str = str.replace("D", "Dd");
		str = str.replace("#", "Dz");
		str = str.replace("{", "Dl");
		str = str.replace("}", "Dr");
		return str;
	}

	public static String unEscapeSortName(String str) {
		str = str.replace("Dl", "{");
		str = str.replace("Dr", "}");
		str = str.replace("Dz", "#");
		str = str.replace("Dd", "D");
		return str;
	}

	private static int number = 0;

	/**
	 * Generate incremental numbers that dosn't contain the number 1
	 * 
	 * @return an integer that doesn't contain the number 1
	 */
	public static int getUniqueId() {
		boolean valid = false;
		while (!valid) {
			int nr = number;
			while (nr > 0) {
				if (nr % 10 == 1) {
					number++;
					break;
				} else {
					nr /= 10;
				}
			}
			if (nr == 0) {
				valid = true;
			}
		}
		return number++;
	}
}
