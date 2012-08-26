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
		return tag.replaceAll("([\\(\\)\\[\\]\\{\\},])", "`$1");
	}

	/**
	 * This function removes space when declaring equations in lists:
	 * -$ cat m.maude
		mod M is
		  sort S .
		  ops a b c : -> S .
		  op _  _ : S S -> S .
		  eq __(a, b) = c .
		endm
		red a b .
		q
		-$ maude m.maude 
				     \||||||||||||||||||/
				   --- Welcome to Maude ---
				     /||||||||||||||||||\
			    Maude 2.6 built: Dec 10 2010 11:12:39
			    Copyright 1997-2010 SRI International
				   Sun Aug 26 11:01:21 2012
		==========================================
		reduce in M : a b .
		rewrites: 1 in 0ms cpu (0ms real) (1000000 rewrites/second)
		result S: c
		Bye.
		-$
	 * @param tag
	 * @return
	 */
	public static String equationSpaceElimination(String tag)
	{
		return tag.replaceAll("\\s", "");
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
