import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.UnsupportedEncodingException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.tree.*;

public class annotPreK {
  public static String annotToMaudeString(String annotString) {
    try {
      InputStream is = new ByteArrayInputStream(annotString.getBytes("UTF-8"));
      ANTLRInputStream input = new ANTLRInputStream(is);
      annotLexer lexer = new annotLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      annotParser parser = new annotParser(tokens);
      CommonTree tree = (CommonTree) parser.annot().getTree();
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(tree);
      annotToMaude maudifier = new annotToMaude(nodes);
      CommonTree maudifiedTree = (CommonTree) maudifier.root().getTree();

      //System.out.println(treeUtils.toTreeString(tree, 0));
      //System.out.println(treeUtils.toMaudeString(maudifiedTree));
      return treeUtils.toMaudeString(maudifiedTree);
    } catch (UnsupportedEncodingException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }

    return "";
  }

  public static void main (String[] args) {
    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      annotLexer lexer = new annotLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      annotParser parser = new annotParser(tokens);
      CommonTree tree = (CommonTree) parser.annot().getTree();
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(tree);
      annotToMaude maudifier = new annotToMaude(nodes);
      CommonTree maudifiedTree = (CommonTree) maudifier.root().getTree();

      System.out.println(treeUtils.toTreeString(tree, 0));
      System.out.println(treeUtils.toMaudeString(maudifiedTree));
    } catch (UnsupportedEncodingException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }
  }

}
