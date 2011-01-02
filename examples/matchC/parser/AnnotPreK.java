import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.UnsupportedEncodingException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.Token;
import org.antlr.runtime.CommonToken;
import org.antlr.runtime.tree.*;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;


public class AnnotPreK {
  public static String annotToMaudeString(String annotString) {
    try {
      // Parsing
      InputStream is = new ByteArrayInputStream(annotString.getBytes("UTF-8"));
      ANTLRInputStream input = new ANTLRInputStream(is);
      annotLexer lexer = new annotLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      annotParser parser = new annotParser(tokens);
      CommonTree tree = (CommonTree) parser.annot().getTree();

      // Rewriting the AST
      CommonTreeNodeStream nodes;
      tree = completeConfig(tree);

      nodes = new CommonTreeNodeStream(tree);
      annotPass1 pass1 = new annotPass1(nodes);
      tree = (CommonTree) pass1.downup(tree);

      // Maudifing the AST
      nodes = new CommonTreeNodeStream(tree);
      annotToMaude maudifier = new annotToMaude(nodes);
      tree = (CommonTree) maudifier.root().getTree();

      //System.out.println(TreeUtils.toTreeString(tree, 0));
      //System.out.println(TreeUtils.toMaudeString(tree));
      return TreeUtils.toMaudeString(tree);
    } catch (UnsupportedEncodingException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }

    return "";
  }

  public static void addCell(CommonTree cellBag, Table.Cell cell, String var) {
    Token t;
    String label = cell.label;

    t = new CommonToken(annotParser.CELL, "CELL");
    CommonTree newCell = new CommonTree(t);
    cellBag.addChild(newCell);

    t = new CommonToken(annotParser.LABEL, label);
    newCell.addChild(new CommonTree(t));

    t = new CommonToken(annotParser.BAG, "BAG");
    CommonTree newBag = new CommonTree(t);
    newCell.addChild(newBag);

    if (!cell.defaultFlag) { 
      String prefix;
      if (var.startsWith("?") || var.startsWith("!")) {
        prefix = var.substring(0, 1);
        var = var.substring(1);
      } else {
        prefix = "Free";
      }

      String wrapper = prefix + cell.sort + "Item";
      t = new CommonToken(annotParser.IDENTIFIER, wrapper);
      CommonTree newVar = new CommonTree(t);
      newBag.addChild(newVar);

      String wrappee = "\"" + var + label + "\"";
      t = new CommonToken(annotParser.IDENTIFIER, wrappee);
      newVar.addChild(new CommonTree(t));
    } else {
      t = new CommonToken(annotParser.IDENTIFIER, "default");
      newBag.addChild(new CommonTree(t));
    }

    t = new CommonToken(annotParser.LABEL, label);
    newCell.addChild(new CommonTree(t));
  }

  public static CommonTree completeConfig(CommonTree tree) {
    if (tree.getType() == annotParser.CONFIG  ) {
      CommonTree topBag = (CommonTree) tree.getChild(0);
      CommonTree bagElement = (CommonTree) topBag.getChild(0);
      
      if (bagElement.getType() == annotParser.IDENTIFIER) {
        topBag.deleteChild(0);

        Table.Cell cell = Table.config.get("config");
        String frameVar = bagElement.getText();
        addCell(topBag, cell, frameVar); 
      }
    }

    if (tree.getType() == annotParser.CELL) {
      String cellLabel = ((CommonTree) tree.getChild(0)).getText();

      if (!Table.config.get(cellLabel).cells.isEmpty()) {
        HashSet labelSet = new HashSet<String>();
        String frameVar = "";
        int frameVarIndex = -1;
        
        CommonTree cellBag = (CommonTree) tree.getChild(1);

        for (int i = 0; i < cellBag.getChildCount(); i++) {
          CommonTree element = (CommonTree) cellBag.getChild(i);

          if (element.getType() == annotParser.CELL) {
            labelSet.add(((CommonTree) element.getChild(0)).getText());
          } else if (element.getType() == annotParser.IDENTIFIER) {
            frameVar = element.getText();
            frameVarIndex = i;
          }
        }

        if (frameVarIndex == -1 && !labelSet.isEmpty()) {
          System.err.println("error: cell " + cellLabel);
          System.exit(-1);
        }

        cellBag.deleteChild(frameVarIndex);

        Iterator<Table.Cell> labelIterator;
        labelIterator = Table.config.get(cellLabel).cells.iterator();

        while (labelIterator.hasNext()) {
          Table.Cell cell = labelIterator.next();
          String label = cell.label;

          if (!labelSet.contains(label))
            addCell(cellBag, cell, frameVar);
        }
      }
    }

    for (int i = 0; i < tree.getChildCount(); i++)
      completeConfig((CommonTree) tree.getChild(i));
    
    return tree;
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

      System.out.println(TreeUtils.toTreeString(tree, 0));
      System.out.println(TreeUtils.toMaudeString(maudifiedTree));
    } catch (UnsupportedEncodingException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }
  }

}
