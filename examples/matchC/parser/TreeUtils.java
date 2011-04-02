import org.antlr.runtime.Token;
import org.antlr.runtime.CommonToken;
import org.antlr.runtime.tree.*;
import java.util.HashMap;
import java.util.HashSet;


public class TreeUtils {
  public static void makeOps(
    CommonTree tree,
    HashMap<Integer, String> tokenToK,
    HashMap<Integer, String> tokenToBuiltins
  ) {
    // tansform the children
    for (int index = 0; index < tree.getChildCount(); index++) {
      makeOps((CommonTree) tree.getChild(index), tokenToK, tokenToBuiltins);
    }

    int tokenType = tree.getType();
    if (tokenToK.containsKey(tokenType)) {
      tree.token = new CommonToken(k.K, tokenToK.get(tokenType));
    }
    else if (tokenToBuiltins.containsKey(tokenType)) {
      tree.token = new CommonToken(k.BUILTIN, tokenToBuiltins.get(tokenType));
    }
  }

  public static Tree unflat(
    Tree tree,
    int tokenType,
    int opTokenType,
    int idTokenType,
    String opString,
    String idString
  ) {
    // tansform the children
    for (int index = 0; index < tree.getChildCount(); index++) {
      tree.setChild(index,
                    unflat(tree.getChild(index), tokenType, opTokenType,
                           idTokenType, opString, idString));
    }

    if (tree.getType() == tokenType) {
      int childCount = tree.getChildCount();
      Tree rootNode;
      if (childCount > 1) {
        int index = 0;
        CommonToken opToken = new CommonToken(opTokenType, opString);
        CommonTree opNode = new CommonTree(opToken);
        opNode.addChild(tree.getChild(index));
        rootNode = opNode; 
        for (index++; index < childCount -1; index++) {
          opToken = new CommonToken(opTokenType, opString); 
          CommonTree newOpNode = new CommonTree(opToken);
          opNode.addChild(newOpNode);
          opNode = newOpNode;
          opNode.addChild(tree.getChild(index));
        }
        opNode.addChild(tree.getChild(index));
      }
      else if (childCount == 1) {
        rootNode = tree.getChild(0);
      }
      else {
        CommonToken idToken = new CommonToken(idTokenType, idString);
        rootNode = new CommonTree(idToken);
      }
      tree = rootNode;
    }

    return tree;
  }


  public static Tree
  makeLabels(
    Tree tree,
    HashSet<String> coreK,
    HashMap<String, String> tokenToWrapper
  ) {
    // tansform the children
    for (int index = 0; index < tree.getChildCount(); index++) {
      tree.setChild(index, makeLabels(tree.getChild(index), coreK, tokenToWrapper));
    }

    int kTokenType = tree.getType();
    String kString = tree.getText();
    // 
    if (kTokenType == k.K && !coreK.contains(kString)) {
      String kLabelString = "'" + kString;
      CommonToken kLabelToken = new CommonToken(k.KLABEL, kLabelString);
      CommonTree kLabelNode = new CommonTree(kLabelToken);

      CommonToken kListToken = new CommonToken(k.K_LIST, "_`,`,_");
      CommonTree kListNode = new CommonTree(kListToken);
      for (int index = 0; index < tree.getChildCount(); index++) {
        kListNode.addChild(tree.getChild(index));
      }    

      CommonToken appToken = new CommonToken(k.APP, "_`(_`)");
      CommonTree appNode = new CommonTree(appToken);
      appNode.addChild(kLabelNode);
      appNode.addChild(kListNode);
      tree = appNode;
    }
    // wrappers
    else if (kTokenType == k.BUILTIN && tree.getParent() != null) {
      int parentTokenType = ((CommonTree) tree.getParent()).getType();
      String parentString = ((CommonTree) tree.getParent()).getText();
      if (parentTokenType == k.K || coreK.contains(parentString)) {
        if (tokenToWrapper.containsKey(kString)) {
          String wrapperString = tokenToWrapper.get(kString);
          CommonToken wrapperToken;
          wrapperToken = new CommonToken(k.WRAPPER, wrapperString);
          CommonTree wrapperNode = new CommonTree(wrapperToken);
          wrapperNode.addChild(tree);

          CommonToken kListToken = new CommonToken(k.K_LIST, "_`,`,_");
          CommonTree kListNode = new CommonTree(kListToken);
          CommonToken appToken = new CommonToken(k.APP, "_`(_`)");
          CommonTree appNode = new CommonTree(appToken);
          appNode.addChild(wrapperNode);
          appNode.addChild(kListNode);
          tree = appNode;
        } 
        else {
        }
      }
    }
    else if (kTokenType == k.WRAPPER) {
      CommonToken kListToken = new CommonToken(k.K_LIST, "_`,`,_");
      CommonTree kListNode = new CommonTree(kListToken);
      CommonToken appToken = new CommonToken(k.APP, "_`(_`)");
      CommonTree appNode = new CommonTree(appToken);
      appNode.addChild(tree);
      appNode.addChild(kListNode);
      tree = appNode;
    }

    return tree;
  }

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
          s += ", " + toMaudeString((CommonTree) t.getChild(i));
        }
        s += ")";
      }
    }
    return s;
  }
}

