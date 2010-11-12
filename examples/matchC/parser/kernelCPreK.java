import java.io.IOException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.*;
import org.antlr.runtime.Token;

public class kernelCPreK {
  public static void main (String[] args) {
    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      kernelCLexer lexer = new kernelCLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      kernelCParser parser = new kernelCParser(tokens);
      CommonTree tree = (CommonTree) parser.translation_unit().getTree();
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(tree);
      kernelCToMaude maudifier = new kernelCToMaude(nodes);
      CommonTree maudifiedTree = (CommonTree) maudifier.root().getTree();

      //System.out.println(treeToString(tree, 0));
      for (String annot : lexer.annots) {
        annot = annot.trim();
        if (annot.startsWith("var")) {
          annot = annot.replace("var ", "  ops ").replace(":", ": ->") + " .";
          System.out.println(annot); 
        }
      }
      System.out.print("  ops ");
      for (String id : lexer.ids) {
        System.out.print(id + " "); 
      }
      System.out.println(": -> Id .");
      System.out.println("  op prog : -> TranslationUnit .");
      System.out.println("  eq prog = (" + toMaudeString(maudifiedTree) + ") .");
    }
    catch (IOException e) {}
    catch (RecognitionException e) {}
  }

  public static String treeToString(CommonTree t, int indent) {
    String s = "";
    if (t != null) {
      StringBuffer sb = new StringBuffer(indent);
      for (int i = 0; i < indent; i++) {
        sb = sb.append("  "); 
      }
      s += sb.toString() + t.toString() + "\n";
      for (int i = 0; i < t.getChildCount(); i++) {
        s += treeToString((CommonTree) t.getChild(i), indent + 1);
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
