import java.io.IOException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.*;
import org.antlr.runtime.Token;
public class antlrTest {
  public static void main (String[] args) {
    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      antlrLexer lexer = new antlrLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      antlrParser parser = new antlrParser(tokens);
      CommonTree t = (CommonTree) parser.config().getTree();
      CommonTreeNodeStream nodes1 = new CommonTreeNodeStream(t);
      antlrTreePass1 treePass1 = new antlrTreePass1(nodes1);
      CommonTree t1 = (CommonTree) treePass1.config().getTree();
      CommonTreeNodeStream nodes2 = new CommonTreeNodeStream(t1);
      antlrTreePass2 treePass2 = new antlrTreePass2(nodes2);
      CommonTree t2 = (CommonTree) treePass2.config().getTree();
      System.out.println(treeToString(t2, 0));
    }
    catch (IOException e) {}
    catch (RecognitionException e) {}
  }

  public static String treeToString(CommonTree t, int indent) {
    String s = "";
    if (t != null) {
      StringBuffer sb = new StringBuffer(indent);
      for (int i = 0; i < indent; i++)
        sb = sb.append("  ");
      s += sb.toString() + t.toString() + "\n";
      for ( int i = 0; i < t.getChildCount(); i++ ) {
        s += treeToString((CommonTree) t.getChild(i), indent + 1);
      }
    }
    return s;
  }
}