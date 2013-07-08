package org.kframework.krun.gui.diff;

import java.awt.Color;
import java.io.IOException;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import javax.swing.JTextPane;
import javax.swing.text.BadLocationException;
import javax.swing.text.SimpleAttributeSet;
import javax.swing.text.StyleConstants;
import javax.swing.text.StyledDocument;
import difflib.Delta;
import difflib.DiffUtils;
import difflib.Patch;

/**
 * Class used to perform diff between two strings
 * 
 * @author danielV
 * 
 */
public class Diff {

  private static final int MaxPerRow = 100;
  private static final String SEP = "";
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

  // performs diffs and stored formated result in testPane
  public static void comparableTest(String str1, String str2, JTextPane textPane)
          throws IOException {
    synchronized (Diff.class) {
      textPane.setText("");
      StyledDocument doc = textPane.getStyledDocument();
      SimpleAttributeSet diffP = new SimpleAttributeSet();
      StyleConstants.setBackground(diffP, Color.YELLOW);
      StyleConstants.setBold(diffP, true);

      List<String> original = getAllTrimLines(str1);
      List<String> revised = getAllTrimLines(str2);
      Patch patch = DiffUtils.diff(original, revised);
      List<Delta> deltas = patch.getDeltas();
      Diff l2B = new Diff();
      int last = 0;
      for (Delta delta : deltas) {
        if (last + 1 < delta.getOriginal().getPosition()) { // not continuous
          for (int i = last + 1; i < delta.getOriginal().getPosition(); i++) {
            try {
              doc.insertString(doc.getLength(), original.get(i)
                      + createSpaces(original.get(i).length()) + SEP + original.get(i) + "\n",
                      null);
            } catch (BadLocationException e) {
              e.printStackTrace();
            }
          }
        }
        List<?> or = delta.getOriginal().getLines();
        List<?> re = delta.getRevised().getLines();
        try {
          String strOr = l2B.l2b(or).toString().replaceAll("\\r", "");
          String strRe = l2B.l2b(re).toString().replaceAll("\\r", "");
          String[] splitOr = strOr.split("\n");
          String[] splitRe = strRe.split("\n");
          int i = 0;
          for (; i < splitOr.length; i++) {
            doc.insertString(doc.getLength(),
                    splitOr[i] + createSpaces(splitOr[i].length()) + SEP, diffP);
            if (i < splitRe.length) {
              doc.insertString(doc.getLength(), splitRe[i] + "\n", diffP);
            }
            else {
              doc.insertString(doc.getLength(), createSpaces(0) + "\n", diffP);
            }
          }
          for (; i < splitRe.length; i++) {
            doc.insertString(doc.getLength(), createSpaces(0) + splitRe[i] + "\n", diffP);
          }
        } catch (BadLocationException e) {
          e.printStackTrace();
        }
        last = delta.getOriginal().last();
      }
      if (last + 1 < original.size()) { // last is not delta
        for (int i = last + 1; i < original.size(); i++) {
          try {
            doc.insertString(doc.getLength(), original.get(i)
                    + createSpaces(original.get(i).length()) + SEP + original.get(i) + "\n", null);
          } catch (BadLocationException e) {
            e.printStackTrace();
          }
        }
      }
    }
  }

  // splits given string by new line and trim each line to maxRow chars
  private static List<String> getAllTrimLines(String strToTrim) {
    List<String> rez = new LinkedList<String>();
    rez.addAll(Arrays.asList(strToTrim.replaceAll("\t", "     ").split("\n")));
    for (int i = 0; i < rez.size(); i++) {
      String currentStr = rez.get(i);
      if (currentStr.length() > MaxPerRow) {
        rez.remove(i);
        List<String> trim = limitRowToMax(currentStr);
        rez.addAll(i, trim);
        // increase index so that we do not check again what we just added
        i += trim.size() - 1;
      }
    }
    return rez;
  }

  private static List<String> limitRowToMax(String row) {
    List<String> ret = new LinkedList<String>();
    while (row.length() > MaxPerRow) {
      ret.add(row.substring(0, MaxPerRow));
      row = row.substring(MaxPerRow);
    }
    return ret;
  }

  private static String createSpaces(int le) {
    String ret = "";
    for (int i = 0; i < MaxPerRow - le; i++) {
      ret += " ";
    }
    return ret;
  }

}
