import java.io.IOException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.*;
import org.antlr.runtime.Token;


public class KernelCPreK {

  public static void main (String[] args) {
    Table.init();

    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      kernelCLexer lexer = new kernelCLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      kernelCParser parser = new kernelCParser(tokens);
      CommonTree tree = (CommonTree) parser.translation_unit().getTree();
      CommonTreeNodeStream nodes = new CommonTreeNodeStream(tree);
      kernelCToMaude maudifier = new kernelCToMaude(nodes);
      CommonTree maudifiedTree = (CommonTree) maudifier.root().getTree();

      for (String annot : lexer.annots) {
        annot = annot.trim();
        if (annot.startsWith("var")) {
          annot = annot.replace("var ", "  ops ").replace(":", ": ->") + " .";
          System.out.println(annot); 
        }
      }

      System.out.print("  ops ");
      for (String id : Table.identifiers) {
        System.out.print(id + " "); 
      }
      System.out.println(": -> Id .");

      System.out.println("  op prog : -> TranslationUnit .");
      String prog = TreeUtils.toMaudeString(maudifiedTree);
      System.out.println("  eq prog = (" + prog + ") .");
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }
  }
}
