import java.io.IOException;
import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.tree.*;
import org.antlr.runtime.Token;
import java.util.Map;
import java.util.HashMap;
import java.util.HashSet;


public class KernelCPreK {
  public static final HashMap<Integer, String>
    tokenToK = new HashMap<Integer, String>();
  public static final HashMap<Integer, String>
    tokenToBuiltins = new HashMap<Integer, String>();
  public static final HashSet<String>
    coreK = new HashSet<String>();
  public static final HashMap<String, String>
    tokenToWrapper = new HashMap<String, String>();

  public static void init() {
    coreK.add("_~>_");
    coreK.add("(.).K");
    coreK.add(".");

    tokenToK.put(kernelCParser.TRANS_UNIT, "translationUnit_");
    tokenToBuiltins.put(kernelCParser.INT_TYPE, "int");
    tokenToBuiltins.put(kernelCParser.STRING_TYPE, "string");
    tokenToBuiltins.put(kernelCParser.VOID_TYPE, "void");
    tokenToK.put(kernelCParser.FUN_DECL, "__`(_`)");
    tokenToK.put(kernelCParser.ANNOT_FUN_DECL, "__`(_`)`[`[_`]`]");
    tokenToK.put(kernelCParser.FUN_DEF, "__`(_`)_");
    tokenToK.put(kernelCParser.ANNOT_FUN_DEF, "__`(_`)`[`[_`]`]_");
    tokenToK.put(kernelCParser.STRUCT_DECL, "struct_`{_`};");
    tokenToK.put(kernelCParser.VAR_DECL, "__;");
    tokenToK.put(kernelCParser.PARAM, "__;");
    tokenToBuiltins.put(kernelCParser.STRUCT, "struct_");
    tokenToBuiltins.put(kernelCParser.PTR, "_*");
    tokenToK.put(kernelCParser.NOP, "nop");
    tokenToK.put(kernelCParser.BLOCK, "block`(_`)");
    tokenToK.put(kernelCParser.SEP, "_;");
    tokenToK.put(kernelCParser.IF, "if`(_`)_else_");
    tokenToK.put(kernelCParser.WHILE, "while`(_`)_");
    tokenToK.put(kernelCParser.RETURN, "return_");
    tokenToK.put(kernelCParser.ASSIGN, "_=_");
    tokenToK.put(kernelCParser.OR_ASSIGN, "_|=_");
    tokenToK.put(kernelCParser.XOR_ASSIGN, "_^=_");
    tokenToK.put(kernelCParser.AND_ASSIGN, "_&=_");
    tokenToK.put(kernelCParser.SHL_ASSIGN, "_<<=_");
    tokenToK.put(kernelCParser.SHR_ASSIGN, "_>>=_");
    tokenToK.put(kernelCParser.ADD_ASSIGN, "_+=_");
    tokenToK.put(kernelCParser.SUB_ASSIGN, "_-=_");
    tokenToK.put(kernelCParser.MUL_ASSIGN, "_*=_");
    tokenToK.put(kernelCParser.DIV_ASSIGN, "_/=_");
    tokenToK.put(kernelCParser.REM_ASSIGN, "_%=_");
    tokenToK.put(kernelCParser.COND, "_?_:_");
    tokenToK.put(kernelCParser.LOR, "_||_");
    tokenToK.put(kernelCParser.LAND, "_&&_");
    tokenToK.put(kernelCParser.OR, "_|_");
    tokenToK.put(kernelCParser.XOR, "_^_");
    tokenToK.put(kernelCParser.AND, "_&_");
    tokenToK.put(kernelCParser.EQ, "_==_");
    tokenToK.put(kernelCParser.NEQ, "_!=_");
    tokenToK.put(kernelCParser.LT, "_<_");
    tokenToK.put(kernelCParser.GT, "_>_");
    tokenToK.put(kernelCParser.LEQ, "_<=_");
    tokenToK.put(kernelCParser.GEQ, "_=>_");
    tokenToK.put(kernelCParser.SHL, "_<<_");
    tokenToK.put(kernelCParser.SHR, "_>>_");
    tokenToK.put(kernelCParser.ADD, "_+_");
    tokenToK.put(kernelCParser.SUB, "_-_");
    tokenToK.put(kernelCParser.MUL, "_*_");
    tokenToK.put(kernelCParser.DIV, "_/_");
    tokenToK.put(kernelCParser.REM, "_%_");
    tokenToK.put(kernelCParser.PRE_INC, "++_");
    tokenToK.put(kernelCParser.PRE_DEC, "--_");
    tokenToK.put(kernelCParser.SIZEOF, "sizeof_");
    tokenToK.put(kernelCParser.CAST, "`(_`)_");
    tokenToK.put(kernelCParser.REF, "&_");
    tokenToK.put(kernelCParser.DEREF, "*_");
    tokenToK.put(kernelCParser.SIGN_POS, "+_");
    tokenToK.put(kernelCParser.SIGN_NEG, "-_");
    tokenToK.put(kernelCParser.NOT, "~_");
    tokenToK.put(kernelCParser.NEG, "-_");
    tokenToK.put(kernelCParser.DOT, "_._");
    tokenToK.put(kernelCParser.ARROW, "_->_");
    tokenToK.put(kernelCParser.INDEX, "");
    tokenToK.put(kernelCParser.CALL, "_`(_`)");
    tokenToK.put(kernelCParser.POST_INC, "_++");
    tokenToK.put(kernelCParser.POST_DEC, "_--");
    tokenToK.put(k.K_ARROW, "_~>_"); 
    tokenToK.put(k.K_UNIT, "(.).K"); 
    tokenToK.put(kernelCParser.LIST, "_`,`,`,_"); 
    tokenToBuiltins.put(kernelCParser.ID, "id`(_`)");
    tokenToBuiltins.put(kernelCParser.TV, "tv`(_`,_`)");

    tokenToWrapper.put("id`(_`)", "Id_");
    tokenToWrapper.put("tv`(_`,_`)", "TypedValue_");
    tokenToWrapper.put("struct_", "ExpressionType_");
    tokenToWrapper.put("_*", "ExpressionType_");
    tokenToWrapper.put("void", "ExpressionType_");
    tokenToWrapper.put("int", "ExpressionType_");
  }

  public static void main (String[] args) {
    Table.init();
    init();

    try {
      ANTLRInputStream input = new ANTLRInputStream(System.in);
      kernelCLexer lexer = new kernelCLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      kernelCParser parser = new kernelCParser(tokens);
      CommonTree tree = (CommonTree) parser.translation_unit().getTree();

      // Rewriting the AST
      CommonTreeNodeStream nodes;

      // Wrap identifiers
      nodes = new CommonTreeNodeStream(tree);
      kernelCPass1 pass1 = new kernelCPass1(nodes);
      tree = (CommonTree) pass1.downup(tree);

      // Wrap Values with types
      nodes = new CommonTreeNodeStream(tree);
      kernelCPass2 pass2 = new kernelCPass2(nodes);
      tree = (CommonTree) pass2.downup(tree);

      // Unflat k arrow
      tree = (CommonTree) TreeUtils.unflat(tree, kernelCParser.SEQ, k.K_ARROW, k.K_UNIT, "_~>_", ".K");

      // Replace operators with K
      TreeUtils.makeOps(tree, tokenToK, tokenToBuiltins);

      // Make KLabels
      tree = (CommonTree) TreeUtils.makeLabels(tree, coreK, tokenToWrapper);

      // Unflat list
      tree = (CommonTree) TreeUtils.unflat(tree, k.K_LIST, k.K_LIST_COMMA, k.K_LIST_UNIT, "_`,`,_", ".List{K}");

      nodes = new CommonTreeNodeStream(tree);
      kernelCPass3 pass3 = new kernelCPass3(nodes);
      tree = (CommonTree) pass3.downup(tree);

      CommonTree maudifiedTree = tree;

      Table.makeVars();

      System.out.println("  op prog : -> K .");
      String prog = TreeUtils.toMaudeString(maudifiedTree);
      System.out.println("  eq prog = (" + prog + ") .");

      for (Map.Entry<String, String> varEntry : Table.varToSort.entrySet()) {
        String id = varEntry.getKey();
        String sort = varEntry.getValue();
        System.out.println("  op " + id + " : -> " + sort + " .");
      }
    } catch (IOException e) {
      e.printStackTrace();
    } catch (RecognitionException e) {
      e.printStackTrace();
    }
  }
}
