// Copyright (c) 2013-2014 K Team. All Rights Reserved.
package org.kframework.krun.gui.diff;

import java.util.LinkedList;
import java.util.List;

import org.apache.commons.lang3.StringEscapeUtils;

import difflib.Delta;
import difflib.DiffUtils;
import difflib.Patch;

/**
 * Class used to perform diff between two strings
 */
public class Diff {

    private static final String STYLESAME = "";// "font-size:smaller;";
    private static final String YELLLOW = "#FFFF00";
    private static final String ORANGE = "#FFCC00";
    private static final String GREEN = "#00FF00";
    private static final String GRAY = "#E0E0E0";
    private StringBuilder sb = new StringBuilder();

    StringBuilder l2b(List<?> l) {
        sb.delete(0, sb.length());
        for (Object object : l) {
            sb.append(object + "\n");
        }
        if (sb.length() >= 1)
            sb.deleteCharAt(sb.length() - 1); // last "\n"
        return sb;
    }

    public static String comparableTest(String str1, String str2) {
        String[] x = str1.split("\\n");
        String[] y = str2.split("\\n");

        List<String> original = new LinkedList<String>();
        for (String s : x)
            original.add(StringEscapeUtils.escapeHtml4(s));
        List<String> revised = new LinkedList<String>();
        for (String s : y)
            revised.add(StringEscapeUtils.escapeHtml4(s));
        StringBuilder tl = new StringBuilder();
        StringBuilder tr = new StringBuilder();
        StringBuilder fin = new StringBuilder();
        Patch patch = DiffUtils.diff(original, revised);
        List<Delta> deltas = patch.getDeltas();
        Diff l2B = new Diff();
        int last = 0;
        String colorOrg;
        String colorRev;
        for (Delta delta : deltas) {
            tl.delete(0, tl.length());
            tr.delete(0, tr.length());
            if (last + 1 < delta.getOriginal().getPosition()) { // not
                                                                // continuous
                tl.append("<td style='" + STYLESAME + "'>\n");
                tr.append("<td style='" + STYLESAME + "'>\n");
                for (int i = last + 1; i < delta.getOriginal().getPosition(); i++) {
                    tl.append(original.get(i) + "\n");
                    tr.append(original.get(i) + "\n");
                }
                tl.append("</td>\n");
                tr.append("</td>\n");
                fin.append("<tr>" + tl + tr + "</tr>");
            }
            List<?> or = delta.getOriginal().getLines();
            List<?> re = delta.getRevised().getLines();
            String org = l2B.l2b(or).toString();
            String rev = l2B.l2b(re).toString();
            boolean deleted = false;
            if (org.trim().isEmpty()) {
                colorOrg = GRAY;
                int lines = rev.split("\n").length;
                for (int i = 0; i < lines; i++) {
                    org += "\n";
                }
                // text was added
                colorRev = GREEN;
            } else if (rev.trim().isEmpty()) {
                colorRev = GRAY;
                int lines = org.split("\n").length;
                for (int i = 1; i < lines; i++) {
                    rev += "\n";
                }
                deleted = true;
                // text was removed
                colorOrg = ORANGE;
            } else {
                colorOrg = colorRev = YELLLOW;
            }
            tl.delete(0, tl.length());
            tr.delete(0, tr.length());
            tl.append("<td style='background-color:" + colorOrg + ";'>" + (deleted ? "<del>" : "")
                    + org.replaceAll("\\n", "<br>") + "<br>" + (deleted ? "</del>" : "") + "</td>");
            tr.append("<td style='background-color:" + colorRev + ";'>"
                    + rev.replaceAll("\\n", "<br>") + "<br></td>");
            fin.append("<tr>" + tl + tr + "</tr>");
            last = delta.getOriginal().last();
        }
        if (last + 1 < original.size()) { // last is not delta
            tl.delete(0, tl.length());
            tr.delete(0, tr.length());
            tl.append("<td style='" + STYLESAME + "'>\n");
            tr.append("<td style='" + STYLESAME + "'>\n");
            for (int i = last + 1; i < original.size(); i++) {
                tl.append(original.get(i) + "\n");
                tr.append(original.get(i) + "\n");
            }
            tl.append("</td>\n");
            tr.append("</td>\n");
            fin.append("<tr>" + tl + tr + "</tr>");
        }
        return ("<html><table>" + fin + "</table></html>");
    }
}
