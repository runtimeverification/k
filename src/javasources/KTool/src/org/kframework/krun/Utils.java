package org.kframework.krun;

import org.kframework.kil.KSorts;
import org.w3c.dom.Element;

import java.util.List;

public class Utils {
   
	// count the number of underscores from the String op
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
	
	//replace all "_" from op attribute of the current node with its children representation from elements list
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
	
	//replace all "_" from op attribute of the current node with its children representation from elements list when the operator is associative
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
	
	//insert parenthesis before and after each "_" when we have the option --parens
	public static StringBuilder insertParenthesisNearUnderscores(List<Element> list, String op) {
		StringBuilder sb = new StringBuilder(op);
		int index = 0;
		int count = 0;
		while (index != -1) {
			index = sb.indexOf("_", index);
			if (index != -1) {
				//when the number of underscores is greater than the number of children (such in the case of family.logik)
				if (count >= list.size()) {		
					sb.insert(index, "");
					break;		
				}
				Element child = list.get(count);
				//do not insert any parenthesis in this case
				if (child.getAttribute("op").equals("#_")
                        && child.getAttribute("sort").equals(KSorts.KLABEL)) {
					sb = sb.insert(index + 1, " ");
					sb = sb.insert(index, " ");
					index += 2;
				} else {
					sb = sb.insert(index + 1, ") ");
					sb = sb.insert(index, " (");
					index += 3;
				}
				count++;
			}
		}
		return sb;
	}
	
	//color the symbol found in text with the specified color
	public static StringBuilder colorSymbol(String text, String symbol, String color, String oldColor) {
		StringBuilder aux = new StringBuilder();
		String[] tokens;
		tokens = text.split("\\" + symbol);
		for (int i = 0; i < tokens.length - 1; i++) {
			aux.append(tokens[i]);
			aux.append(color);
			aux.append(symbol);
			aux.append(oldColor);
		}
		aux.append(tokens[tokens.length - 1]);
		return aux;
	}

	//returns a string composed of numChars whitespace characters
	public static String buildWhitespace(int numChars) {
		StringBuilder sb = new StringBuilder();
		for (int i = 0; i < numChars; i++)
			sb.append(" ");
		return sb.toString();
	}
	
	//determines if a String is a number or not
	public static boolean isNumber(String s) {
	    if (s == null || s.isEmpty()) {
	        return false;
	    }
	    for (int i = 0; i < s.length(); i++) {
	        if (!Character.isDigit(s.charAt(i))) {
	            return false;
	        }
	    }
	    return true;
	}
	
	
}
