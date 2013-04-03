package org.kframework.krun.gui.diff;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;

import org.apache.commons.lang3.StringEscapeUtils;

import difflib.Delta;
import difflib.DiffUtils;
import difflib.Patch;

public class Diff {
	private StringBuilder sb = new StringBuilder();
	StringBuilder l2b(List<?> l){
		sb.delete(0, sb.length());
		for (Object object : l) {
			sb.append(object+"\n");
		}
		if(sb.length()>=1)sb.deleteCharAt(sb.length()-1); // last "\n"
		return sb;
	}
	
	public static String comparableTest(String str1, String str2) throws IOException{     
		String[] x = str1.split("\\n");
		String[] y = str2.split("\\n");
		
		List<String> original = new LinkedList<String>();
		for (String s  : x )
			original.add(StringEscapeUtils.escapeHtml4(s));
		List<String> revised = new LinkedList<String>();
		for (String s  : y )
			revised.add(StringEscapeUtils.escapeHtml4(s));
		String[] cors = new String[]{"palegreen","khaki","pink","moccasin","lightskyblue","lightyellow","coral","aliceblue","yellowgreen","beige","lightpink"};
		StringBuilder tl = new StringBuilder();
		StringBuilder tr = new StringBuilder();
		Patch patch = DiffUtils.diff(original, revised);
		List<Delta> deltas = patch.getDeltas();
		Diff l2B = new Diff();
		int cori = 0;
		int last = 0;
		for (Delta delta : deltas) {
			if(last + 1 < delta.getOriginal().getPosition()){ // not continuous
				tl.append("<pre style='font-size:smaller;'>\n");
				tr.append("<pre style='font-size:smaller;'>\n");
				for(int i = last + 1; i < delta.getOriginal().getPosition(); i++){
					tl.append(original.get(i)+"\n");
					tr.append(original.get(i)+"\n");
				}
				tl.append("</pre>\n");
				tr.append("</pre>\n");
			}
			List<?> or = delta.getOriginal().getLines();
//			/System.out.println("<pre style='background-color:"+cors[cori]+";'><font color='"+cors[cori]+"'>\n"+l2B.l2b(or)+"</font>\n</pre>");
			tl.append("<pre style='background-color:"+cors[cori]+";'><font color='"+cors[cori]+"'>\n"+l2B.l2b(or)+"</font>\n</pre>");
			List<?> re = delta.getRevised().getLines();
			//System.out.println("<pre style='background-color:"+cors[cori]+";'>\n"+l2B.l2b(re)+"\n</pre>");
			tr.append("<pre style='background-color:"+cors[cori]+";'><font color='"+cors[cori]+"'>\n"+l2B.l2b(re)+"\n</font></pre>");
			cori = (cori<cors.length)?cori+1:0;
			last = delta.getOriginal().last();
		}
		if(last + 1 < original.size()){ //last is not delta
			tl.append("<pre style='font-size:smaller;'>\n");
			tr.append("<pre style='font-size:smaller;'>\n");
			for(int i = last + 1; i < original.size(); i++){
				tl.append(original.get(i)+"\n");
				tr.append(original.get(i)+"\n");
			}
			tl.append("</pre>\n");
			tr.append("</pre>\n");
		}

		return("<html><table><tr><td style='vertical-align:top;'>"+tl.toString()+"</td><td style='vertical-align:top;'>"+tr.toString()+"</td></tr></table></html>");
	}
}
