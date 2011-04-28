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
import java.util.Set;
import java.util.Stack;
import java.util.Iterator;


public class AnnotPreK {
  public static final HashMap<Integer, String>
    tokenToK = new HashMap<Integer, String>();
  public static final HashMap<Integer, String>
    tokenToBuiltins = new HashMap<Integer, String>();
  public static final HashSet<String>
    coreK = new HashSet<String>();
  public static final HashMap<String, String>
    tokenToWrapper = new HashMap<String, String>();

  static {
    coreK.add("_~>_");
    coreK.add("(.).K");
    coreK.add(".");
    coreK.add("_=>_");

    tokenToK.put(annotParser.REW, "_=>_");

    tokenToK.put(annotParser.CONDITIONAL_RULE, "@`cfg_->_if_");
    tokenToK.put(annotParser.SPECIFICATION, "@`cfg_->_req_ens_");
    tokenToK.put(annotParser.ASSUME, "@`assume_");
    tokenToK.put(annotParser.ASSERT, "@`assert_");
    tokenToK.put(annotParser.INVARIANT, "@`inv_");
    tokenToK.put(annotParser.SKIP, "@`skip");
    tokenToK.put(annotParser.VERIFY, "@`verify");
    tokenToK.put(annotParser.BREAKPOINT, "@`breakpoint");
    tokenToK.put(annotParser.RETURN, "returnRule_");

    tokenToBuiltins.put(annotParser.DISJ, "_\\/_");
    tokenToBuiltins.put(annotParser.CONJ, "_/\\_");
    tokenToBuiltins.put(annotParser.NEG, "~_");
    tokenToBuiltins.put(annotParser.EQ, "_===_");
    tokenToBuiltins.put(annotParser.LT, "_<Int_");
    tokenToBuiltins.put(annotParser.LEQ, "_<=Int_");
    tokenToBuiltins.put(annotParser.GT, "_>Int_");
    tokenToBuiltins.put(annotParser.GEQ, "_>=Int_");
    tokenToBuiltins.put(annotParser.UNION, "_U_");
    tokenToBuiltins.put(annotParser.APPEND, "_@_");
    tokenToBuiltins.put(annotParser.ADD, "_+Int_");
    tokenToBuiltins.put(annotParser.SUB, "_-Int_");
    tokenToBuiltins.put(annotParser.MUL, "_*Int_");
    tokenToBuiltins.put(annotParser.DIV, "_/Int_");
    tokenToBuiltins.put(annotParser.REM, "_%Int_");
    tokenToBuiltins.put(annotParser.SIGN_POS, "+Int_");
    tokenToBuiltins.put(annotParser.SIGN_NEG, "-Int_");
    tokenToBuiltins.put(annotParser.EPSILON, "epsilon");
    tokenToBuiltins.put(annotParser.SEQ, "`[_`]");
    tokenToBuiltins.put(annotParser.MSET, "`{|_|`}");
    tokenToBuiltins.put(annotParser.MAPSTO, "_|->_");
    tokenToBuiltins.put(annotParser.POINTSTO, "_|->_:_");
    tokenToBuiltins.put(annotParser.HEAP_PATTERN, "_`(_`)`(_`)");
    tokenToBuiltins.put(annotParser.CELL, "<_>_</_>");
    tokenToBuiltins.put(annotParser.FORMULA_TRUE, "TrueFormula");
    tokenToBuiltins.put(annotParser.FORMULA_FALSE, "FalseFormula");
    tokenToBuiltins.put(annotParser.ID, "id`(_`)");
  }


  public static String annotToMaudeString(String annotString) {
    try {
      // Parsing
      Table.annotLocalVariables.clear();
      InputStream is = new ByteArrayInputStream(annotString.getBytes("UTF-8"));
      ANTLRInputStream input = new ANTLRInputStream(is);
      annotLexer lexer = new annotLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      annotParser parser = new annotParser(tokens);
      CommonTree tree = (CommonTree) parser.annot_text().getTree();
      int annotType = tree.getType();

      // Rewriting the AST
      CommonTreeNodeStream nodes;

      completeConfig(tree);
      splitConfig(tree);

      if (annotParser.annotType == annotParser.RULE) {
        Table.annotLogicalVariables.clear();
        getLogicalVariables((CommonTree) tree.getChild(0));
      }

      nodes = new CommonTreeNodeStream(tree);
      annotPass5 pass5 = new annotPass5(nodes);
      tree = (CommonTree) pass5.downup(tree);

      nodes = new CommonTreeNodeStream(tree);
      annotPass1 pass1 = new annotPass1(nodes);
      tree = (CommonTree) pass1.downup(tree);

      nodes = new CommonTreeNodeStream(tree);
      annotPass2 pass2 = new annotPass2(nodes);
      tree = (CommonTree) pass2.downup(tree);

      // Replace operators with K
      TreeUtils.makeOps(tree, tokenToK, tokenToBuiltins);

      nodes = new CommonTreeNodeStream(tree);
      annotPass3 pass3 = new annotPass3(nodes);
      tree = (CommonTree) pass3.downup(tree);

      // Make KLabels
      tree = (CommonTree) TreeUtils.makeLabels(tree, coreK, tokenToWrapper);

      // Unflat containers
      tree = (CommonTree) TreeUtils.unflat(tree, annotParser.LIST, annotParser.LIST, annotParser.LIST, "__", "(.).List");
      tree = (CommonTree) TreeUtils.unflat(tree, annotParser.MAP, annotParser.MAP, annotParser.MAP, "__", "(.).Map");
      tree = (CommonTree) TreeUtils.unflat(tree, annotParser.BAG, annotParser.BAG, annotParser.BAG, "__", "(.).Bag");
      tree = (CommonTree) TreeUtils.unflat(tree, k.K_LIST, k.K_LIST_COMMA, k.K_LIST_UNIT, "_`,`,_", ".List{K}");
      tree = (CommonTree) TreeUtils.unflat(tree, annotParser.MATH_OBJ_LIST, annotParser.MATH_OBJ_LIST, annotParser.MATH_OBJ_LIST, "_`,_", ".List{MathObj++}");

      CommonTree maudifiedTree = tree;

      //System.err.println(TreeUtils.toTreeString(maudifiedTree, 0));
      //System.err.println(TreeUtils.toMaudeString(tree));
      String annotMaudeString = TreeUtils.toMaudeString(maudifiedTree);
      if (annotType == annotParser.ASSERT && Table.varString.startsWith("!") ) {
        String varRoot = Table.varString.substring(1);
        String argString = "_`(_`)(";
        argString += "'cleanFrameSubst`(_`), ";
        argString += "_`(_`)(List`{MathObj++`}_(\"" + varRoot +"\"), .List{K})";
        argString += ")";
        annotMaudeString = "_~>_(" + annotMaudeString + ", " + argString + ")";
      }

      return annotMaudeString;
    } catch (UnsupportedEncodingException e) {
      e.printStackTrace();
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }

    return "";
  }


  private static CommonTree newVar(String name, String sort, boolean isDefault)
  {
    Token t;
    String wrapper;
    if (!isDefault) 
      wrapper = prefix + sort;
    else
      wrapper = "default" + sort;

    t = new CommonToken(annotParser.IDENTIFIER, wrapper);
    CommonTree var = new CommonTree(t);

    String wrappee;
    if (!isDefault)
      wrappee = "\"" + name + "_" + suffix + "\"";
    else 
      wrappee = "\"" + name + "\"";

    t = new CommonToken(annotParser.IDENTIFIER, wrappee);
    var.addChild(new CommonTree(t));

    return var;
  }

  private static CommonTree makeVarId(String varName) {
    Token t;

    t = new CommonToken(annotParser.ID);
    CommonTree idWrapperNode = new CommonTree(t);
    t = new CommonToken(annotParser.STRING_LITERAL, "\"" + varName + "\"");
    idWrapperNode.addChild(new CommonTree(t));

    return idWrapperNode;
  }

  private static CommonTree makeEnvVar(String varName, boolean isFree) {
    Token t;
    t = new CommonToken(annotParser.MAPSTO);
    CommonTree mapstoNode = new CommonTree(t);

    t = new CommonToken(annotParser.APP, "_`(_`)");
    CommonTree leftAppNode = new CommonTree(t);
    mapstoNode.addChild(leftAppNode);
    t = new CommonToken(annotParser.BUILTIN, "Id_");
    CommonTree idBuiltinNode = new CommonTree(t);
    leftAppNode.addChild(idBuiltinNode);
    idBuiltinNode.addChild(makeVarId(varName));
    t = new CommonToken(annotParser.K_LIST, ".List`{K`}");
    leftAppNode.addChild(new CommonTree(t));

    t = new CommonToken(annotParser.APP, "_`(_`)");
    CommonTree rightAppNode = new CommonTree(t);
    mapstoNode.addChild(rightAppNode);
    t = new CommonToken(annotParser.BUILTIN, "List`{MathObj++`}_");
    CommonTree objBuiltinNode = new CommonTree(t);
    rightAppNode.addChild(objBuiltinNode);
    if (!"__return__".equals(varName))
    {
      if (isFree)
        t = new CommonToken(annotParser.IDENTIFIER, "FreeVar");
      else
        t = new CommonToken(annotParser.IDENTIFIER, "?var");
      CommonTree valNode = new CommonTree(t);
      objBuiltinNode.addChild(valNode);
      valNode.addChild(makeVarId(varName));
    }
    else
    {
      if(annotParser.retTree == null)
      {
        t = new CommonToken(annotParser.VALUE, "unit");
        objBuiltinNode.addChild(new CommonTree(t));
      }
      else
        objBuiltinNode.addChild(annotParser.retTree);
    }
    t = new CommonToken(annotParser.K_LIST, ".List`{K`}");
    rightAppNode.addChild(new CommonTree(t));

    return mapstoNode;
  }

  private static void addEnvVars(CommonTree map, boolean isFree, boolean isRet)
  {
    Token t;

    for (String varName : Table.annotLocalVariables)
    {
      map.addChild(makeEnvVar(varName, isFree));
    }

    if (isRet)
      map.addChild(makeEnvVar("__return__", isFree));
  }

  private static void addCell(CommonTree cellBag, Table.Cell cell) {
    Token t;
    String cellLabel = cell.label;

    t = new CommonToken(annotParser.CELL, Integer.toString(Table.Cell.NONE));
    CommonTree newCell = new CommonTree(t);
    cellBag.addChild(newCell);

    t = new CommonToken(annotParser.IDENTIFIER, cellLabel);
    newCell.addChild(new CommonTree(t));

    t = new CommonToken(annotParser.BAG, "BAG");
    CommonTree container = new CommonTree(t);
    newCell.addChild(container);

    if ("env".equals(cellLabel)) {
      switch (annotParser.annotType) {
        case annotParser.RULE:
          t = new CommonToken(annotParser.REW);
          CommonTree rewNode = new CommonTree(t);
          container.addChild(rewNode);
          t = new CommonToken(annotParser.MAP);
          CommonTree leftMapNode = new CommonTree(t);
          rewNode.addChild(leftMapNode);
          t = new CommonToken(annotParser.MAP);
          CommonTree rightMapNode = new CommonTree(t);
          rewNode.addChild(rightMapNode);

          addEnvVars(leftMapNode, true, false);
          addEnvVars(rightMapNode, false, true);

          String oldPrefix = prefix;
          prefix = "?";
          rightMapNode.addChild(newVar("env", "MapItem", false));
          prefix = oldPrefix;
          break;
        case annotParser.INVARIANT:
        case annotParser.ASSERT:
          addEnvVars(container, false, false);
          container.addChild(newVar("env", "MapItem", false));
          break;
        default:
          container.addChild(newVar("env", "MapItem", true));
          break;
      }
    }
    else if (cell.cells.isEmpty())
      container.addChild(newVar(cellLabel, cell.sort + "Item", cell.isDefault));

    t = new CommonToken(annotParser.IDENTIFIER, cellLabel);
    newCell.addChild(new CommonTree(t));
  }

  private static void frameCell(CommonTree tree)
  {
    String cellLabel = ((CommonTree) tree.getChild(0)).getText();
    int cellOpen = Integer.parseInt(tree.getText());
    String cellSort = Table.labelToCell.get(cellLabel).sort;
    String cellItem = cellSort + "Item";

    if (cellOpen != Table.Cell.NONE)
    {
      Token t = null;
      if (cellSort.equals(Table.Sort.MAP) || cellSort.equals(Table.Sort.BAG)) {
        if (cellSort.equals(Table.Sort.MAP))
          t = new CommonToken(annotParser.MAP);
        if (cellSort.equals(Table.Sort.BAG))
          t = new CommonToken(annotParser.BAG);

        CommonTree newContainer = new CommonTree(t);
        if (cellOpen == Table.Cell.LEFT)
          newContainer.addChild(newVar("left_" + cellLabel, cellItem, false));
        newContainer.addChild(tree.getChild(1));
        if (cellOpen == Table.Cell.RIGHT)
          newContainer.addChild(newVar("right_" + cellLabel, cellItem, false));
        if (cellOpen == Table.Cell.BOTH)
          newContainer.addChild(newVar(cellLabel, cellItem, false));
        tree.setChild(1, newContainer);
      }
      else if (cellSort.equals(Table.Sort.LIST)) {
        if (((CommonTree) tree.getChild(1)).getType() == annotParser.STREAM) {
          t = new CommonToken(annotParser.APPEND);

          CommonTree newContainer = new CommonTree(t);
          if ((cellOpen & Table.Cell.LEFT) != Table.Cell.NONE)
            newContainer.addChild(newVar("left_" + cellLabel, "Seq", false));
          newContainer.addChild(((CommonTree) tree.getChild(1)).getChild(0));
          if ((cellOpen & Table.Cell.RIGHT) != Table.Cell.NONE)
            newContainer.addChild(newVar("right_" + cellLabel, "Seq", false));

          ((CommonTree) tree.getChild(1)).setChild(0, newContainer);
        }
      }
    }
  }


  private static String prefix = "";
  private static String suffix = "";
  private static final Stack<String> prefixStack = new Stack<String>();
  private static final Stack<String> suffixStack = new Stack<String>();
  private static final Set<Table.Cell> cells = new HashSet<Table.Cell>();


  private static void completeConfig(CommonTree tree) {
    CommonTree cellBag = null;
    if (tree.getType() == annotParser.CONFIG) {
      cells.clear();
      cells.add(Table.Cell.CONFIG);
      cellBag = (CommonTree) tree.getChild(0);

      if (Table.varString.startsWith("?") || Table.varString.startsWith("!")) {
        prefix = Table.varString.substring(0, 1);
        suffix = Table.varString.substring(1);
      }
      else {
        prefix = "Free";
        suffix = Table.varString;
      }
    }
    else if (tree.getType() == annotParser.CELL) {
      String cellLabel = ((CommonTree) tree.getChild(0)).getText();
      cells.clear();
      cells.addAll(Table.labelToCell.get(cellLabel).cells);
      if (!cells.isEmpty()) {
        cellBag = (CommonTree) tree.getChild(1);
      }
      else {
        frameCell(tree);
        return;
      }
    }

    boolean isVar = false;
    if (cellBag != null) {
      Set<CommonTree> nodes = new HashSet<CommonTree>();

      for (int index = 0; index < cellBag.getChildCount(); index++) {
        CommonTree item = (CommonTree) cellBag.getChild(index);

        if (item.getType() == annotParser.CELL) {
          String cellLabel = ((CommonTree) item.getChild(0)).getText();
          Table.Cell cell = Table.labelToCell.get(cellLabel);
          if (cells.contains(cell))
            cells.remove(cell);
          else {
            nodes.add(item);
            cellBag.deleteChild(index);
            index--;
          }
        }
        else if (item.getType() == annotParser.IDENTIFIER) {
          isVar = true;
          prefixStack.push(prefix);
          suffixStack.push(suffix);

          String var =  item.getText();
          if (var.startsWith("?") || var.startsWith("!")) {
            prefix = var.substring(0, 1);
            suffix = var.substring(1);
          }
          else {
            prefix = "Free";
            suffix = var;
          }

          cellBag.deleteChild(index);
          index--;
        }
      }

      for (Table.Cell cell : cells) {
        addCell(cellBag, cell);
      }

      Iterator<CommonTree> nodeIterator = nodes.iterator();
      while (nodeIterator.hasNext()) {
        CommonTree node = nodeIterator.next();
        String subcellLabel = ((CommonTree) node.getChild(0)).getText();
        Table.Cell subcell = Table.labelToCell.get(subcellLabel);

        for (int index = 0; index < cellBag.getChildCount(); index++) {
          CommonTree item = (CommonTree) cellBag.getChild(index);
          String cellLabel = ((CommonTree) item.getChild(0)).getText();
          Table.Cell cell = Table.labelToCell.get(cellLabel);
          if (cell.isAncestor(subcell)) {
            ((CommonTree) item.getChild(1)).addChild(node);
            break;
          }
        }
      }
    }

    for (int i = 0; i < tree.getChildCount(); i++)
      completeConfig((CommonTree) tree.getChild(i));

    if (isVar) {
      prefix = prefixStack.pop();
      suffix = suffixStack.pop();
    }
  }

  private static void splitConfig(CommonTree tree) {
    if (tree.getType() == annotParser.CONDITIONAL_RULE) {
      CommonTree rewNode = splitTerm((CommonTree) tree.getChild(0));
      tree.addChild(tree.getChild(1));
      tree.setChild(0, rewNode.getChild(0));
      tree.setChild(1, rewNode.getChild(1));
    }
    else if (tree.getType() == annotParser.SPECIFICATION) {
      CommonTree rewNode = splitTerm((CommonTree) tree.getChild(0));
      tree.addChild(tree.getChild(2));
      tree.setChild(2, tree.getChild(1));
      tree.setChild(0, rewNode.getChild(0));
      tree.setChild(1, rewNode.getChild(1));
    }
  }

  private static CommonTree splitTerm(CommonTree tree) {
    if (tree.getType() == annotParser.REW)
      return tree;

    CommonTree rewNode = new CommonTree(new CommonToken(annotParser.REW));
    CommonTree leftNode = new CommonTree(new CommonToken(tree.getToken()));
    CommonTree rightNode = new CommonTree(new CommonToken(tree.getToken()));
    rewNode.addChild(leftNode);
    rewNode.addChild(rightNode);

    for (int i = 0; i < tree.getChildCount(); i++) {
      CommonTree splitChild = splitTerm((CommonTree) tree.getChild(i));
      leftNode.addChild(splitChild.getChild(0));
      rightNode.addChild(splitChild.getChild(1));
    }

    return rewNode;
  }


  private static void getLogicalVariables(CommonTree tree) {
    if (tree.getType() == annotParser.LOGICAL_VARIABLE)
      Table.annotLogicalVariables.add(tree.getText());

    for (int i = 0; i < tree.getChildCount(); i++) {
      getLogicalVariables((CommonTree) tree.getChild(i));
    }
  }



  public static void main (String[] args) {
    annotToMaudeString("//@ assert <heap> . </heap>");
/*
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
*/
  }

}
