import org.antlr.runtime.tree.*;

public class treeUtils {
  public static String toTreeString(CommonTree t, int indent) {
    String s = "";
    if (t != null) {
      StringBuffer sb = new StringBuffer(indent);
      for (int i = 0; i < indent; i++) {
        sb = sb.append("  "); 
      }
      s += sb.toString() + t.toString() + "\n";
      for (int i = 0; i < t.getChildCount(); i++) {
        s += toTreeString((CommonTree) t.getChild(i), indent + 1);
      }
    }
    return s;
  }

  public static String toMaudeString(CommonTree t) {
    String s = "";
    if (t != null) {
      s += t.toString();
      if (t.getChildCount() > 0) {
        s += "(";
        s += toMaudeString((CommonTree) t.getChild(0));
        for (int i = 1; i < t.getChildCount(); i++) {
          s += "," + toMaudeString((CommonTree) t.getChild(i));
        }
        s += ")";
      }
    }
    return s;
  }
}
