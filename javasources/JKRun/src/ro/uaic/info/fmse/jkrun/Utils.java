package ro.uaic.info.fmse.jkrun;

import java.util.List;

public class Utils {
   
	/*
	 * count the number of underscores from the String op
	 */
	public static int countUnderscores(String op) {
		int count = 0;
	    int index = 0;
	    StringBuilder sb = new StringBuilder(op);
	    
		while (index != -1) {
			index = sb.indexOf("_", index);
			if (index != -1) {
				count++;
				index++;
			}
		}
		return count;
	}
	
	//replace all "_" from String op with its children representation from elements list
	public static StringBuilder replaceAllUnderscores(String op, List<String> elements) {
		int index = 0;
		int count = 0;
	    StringBuilder sb = new StringBuilder(op);
	    
		while (index != -1) {
			index = sb.indexOf("_", index);
			if (index != -1) {
				//when the number of underscores is greater than the number of children (such in the case of family.logik)
				if (count >= elements.size()) {		
					sb.insert(index, "");
					sb = sb.deleteCharAt(index);
					break;		
				}
				String s = (String)elements.get(count);
				sb.insert(index, s);
				index += s.length();
				sb = sb.deleteCharAt(index);
				count++;
			}
		}
		return sb;
	}
	
	//replace all "_" from String op with its children representation from elements list when the operator is associative
	public static StringBuilder replaceAllUnderscoresAssoc(String op, List<String> elements) {
		StringBuilder aux = new StringBuilder();
		
		op = op.replaceAll("_", " ");
		for (int i = 0; i < elements.size(); i++) {
			String s = elements.get(i);
			s = s.trim();
			if (i == elements.size() - 1) {
				aux.append(s);
			} else {
				aux.append(s);
				aux.append(op);
			}
		}
		return aux;
	}
	
	//insert around each "_" additional space depending on "_" position  
	public static StringBuilder insertSpaceNearUnderscores(String op) {
		StringBuilder sb = new StringBuilder(op);
		int index = 0;
		
		while (index != -1) {
			index = sb.indexOf("_", index);
			if (index != -1) {
				if (index == 0) {
					sb.insert(index + 1, " ");
					index += "-".length();
				} else if (index == sb.length() - 1) {
					sb.insert(index, " ");
					index += 2;
				} else {
					sb = sb.insert(index + 1, " ");
					sb = sb.insert(index, " ");
					index += 2;
				}
			}
		}
		return sb;
	}
	
	public static String getKastOnOs() {
		if (System.getProperty("os.name").toLowerCase().contains("win"))
			return "kast.bat";
		return "kast";
	}
	
}
