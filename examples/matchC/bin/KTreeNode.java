import javax.swing.tree.TreeNode;

import java.util.Enumeration;
import java.util.List;
import java.util.ArrayList;
import java.util.Arrays;


public class KTreeNode implements TreeNode
{

  final static int DEFAULT_COUNT = 5;

  String content;
  boolean isCell;

  int visibleCount;
  final int visibleInc = 1;

  final KTreeNode parent;
  final ArrayList<KTreeNode> children;
  final KTreeNode ldotsNode;

  static StringBuilder buffer = new StringBuilder(1048576);


  public KTreeNode(KTreeNode parent)
  {
    this(parent, "", 0);
  }

  public KTreeNode(KTreeNode parent, String content)
  {
    this(parent, content, 0);
  }

  public KTreeNode(KTreeNode parent, String content, int visibleCount)
  {
    this.parent = parent;
    children = new ArrayList<KTreeNode>(); 
    this.content = content;
    this.visibleCount = visibleCount;

    if (visibleCount != 0)
    {
      ldotsNode = new KTreeNode(this, "...", 0);
      ldotsNode.add(new KTreeNode(ldotsNode));
    }
    else
      ldotsNode = null;
  }


  public void add(KTreeNode node)
  {
    children.add(node);
  }

  public String getContent()
  {
    return content;
  }

  public void setContent(String content)
  {
    this.content = content;
  }

  public String toString()
  {
    return content;
  }


  /*
   * TreeNode Methods
   */
  public Enumeration children()
  {
    return null;
  }

  public boolean getAllowsChildren()
  {
    return true;
  }

  public TreeNode getChildAt(int childIndex)
  {
    if (visibleCount == 0 || childIndex < visibleCount - 1)
      return children.get(childIndex);
    else if (childIndex == visibleCount - 1)
      return ldotsNode;
    else
      return null;
  }
  
  public int getChildCount()
  {
    if (visibleCount == 0 || children.size() <= visibleCount) 
      return children.size();
    else
      return visibleCount;
  }

  public int getIndex(TreeNode node)
  {
    if (visibleCount == 0 || children.size() <= visibleCount) 
      return children.indexOf(node);
    else if (ldotsNode.equals(node))
      return visibleCount - 1;
   else
      return -1;
  }

  public TreeNode getParent()
  {
    return parent;
  }

  public boolean isLeaf()
  {
    return children.size() == 0;
  }


  public static boolean isAssocOp(String op)
  {
    return "__".equals(op)
        || "_~>_".equals(op)
        || "_\\/_".equals(op)
        || "_/\\_".equals(op)
        || "_;;_".equals(op);
  }


/*
  public static KTreeNode format(KTreeNode parent, MaudeTerm term)
  {
    if ("<_>_</_>".equals(term.getOp()))
      return formatCell(parent, term);
    else
      return formatContent(parent, term);
  }

  public static KTreeNode formatCell(KTreeNode parent, MaudeTerm term)
  {
    KTreeNode node = null;
    String cellLabel = term.subterms().get(0).getOp();      
    MaudeTerm cellContent = term.subterms().get(1);

    if (isAssocOp(cellContent.getOp()))
    {
      //node = new KTreeNode(parent, "<" + cellLabel + "/>", DEFAULT_COUNT);
      node = new KTreeNode(parent, "<" + cellLabel + "/>");
      String assocOp = cellContent.getOp();
      String prefix = assocOp.substring(1, assocOp.length() - 1);
      buffer.setLength(0);
      for (int i = 0; i < prefix.length(); ++i)
        buffer.append(" ");
      for (MaudeTerm cellItem : cellContent.subterms())
      {
        node.add(format(node, cellItem));
        buffer.setLength(0);
        buffer.append(prefix);
      }
      buffer.setLength(0);
    }
    else
    {
      node = new KTreeNode(parent, "<" + cellLabel + "/>");
      node.add(format(node, cellContent));
    }

    return node;
  }

  public static KTreeNode formatContent(KTreeNode parent, MaudeTerm term)
  {
    KTreeNode node = new KTreeNode(parent);
    buffer.setLength(0);
    node.setContent(bufferContent(node, term).toString());

    return node;
  }

  public static StringBuilder bufferContent(KTreeNode node, MaudeTerm term)
  {
    StringBuilder buffer = new StringBuilder();

    if (!"<_>_</_>".equals(term.getOp()))
    {
      List<MaudeTerm> subterms = term.subterms();
      int size = subterms.size();

      if (size > 0 && term.getOp().indexOf('_') != -1)
      {
        String[] fragments = term.getOp().replace("`", "").split("_", -1);

        int length = fragments[0].length();
        if (!"".equals(fragments[0]) &&
            Character.isLetterOrDigit(fragments[0].charAt(length - 1)))
          fragments[0] = fragments[0] + " ";
        if (!"".equals(fragments[fragments.length -1]) &&
            Character.isLetterOrDigit(fragments[fragments.length -1].charAt(0)))
          fragments[fragments.length -1] = " " + fragments[fragments.length -1];

        for (int index = 1; index < fragments.length -1; ++index)
        {
          length = fragments[index].length();
          if (length > 0)
          {
            if (Character.isLetterOrDigit(fragments[index].charAt(0)))
              fragments[index] = " " + fragments[index];
            if (Character.isLetterOrDigit(fragments[index].charAt(length - 1)))
              fragments[index] = fragments[index] + " ";
          }
          else
            fragments[index] = " ";
        }

        if (fragments.length != size + 1 && fragments.length == 3)
        {
          String[] tmp = new String[size + 1];
          tmp[0] = fragments[0];
          tmp[size] = fragments[2];
          Arrays.fill(tmp, 1, size, fragments[1]);
          fragments = tmp;
        }

        for (int index = 0; index < size; ++index)
        {
          buffer.append(fragments[index]);
          buffer.append(bufferContent(node, subterms.get(index)));
        }

        buffer.append(fragments[size]);
      }
      else
      {
        buffer.append(term.getOp());
  
        if (size > 0)
        {
          buffer.append("(");
          buffer.append(bufferContent(node, subterms.get(0)));
             
          for (int index = 1; index < size; ++index)
          {
            buffer.append(", ");
            buffer.append(bufferContent(node, subterms.get(index)));
          }
  
          buffer.append(")");
        }
      }
    }
    else
    {
      node.add(formatCell(node, term));
      buffer.append("<>");
    }

    return buffer;
  }
*/

  public static KTreeNode format2(KTreeNode parent, String prefix,
                                  MaudeTerm term)
  {
    if ("<_>_</_>".equals(term.getOp()))
      return formatCell2(parent, term);
    else
      return formatContent2(parent, prefix, term);
  }

  public static KTreeNode formatCell2(KTreeNode parent, MaudeTerm term)
  {
    String cellLabel = term.subterms().get(0).getOp();      
    MaudeTerm cellContent = term.subterms().get(1);
    KTreeNode node = new KTreeNode(parent, cellLabel);

    if (isAssocOp(cellContent.getOp()))
    {
      String assocOp = cellContent.getOp();
      String prefixOp = assocOp.substring(1, assocOp.length() - 1);
      char[] spaces = new char[prefixOp.length()];
      Arrays.fill(spaces , ' ');
      String prefix = new String(spaces);
      for (MaudeTerm cellItem : cellContent.subterms())
      {
        node.add(format2(node, prefix, cellItem));
        prefix = prefixOp;
      }
    }
    else
    {
      node.add(format2(node, "", cellContent));
    }

    return node;
  }

  public static KTreeNode formatContent2(KTreeNode parent, String prefix,
                                         MaudeTerm term)
  {
    buffer.setLength(0);
    buffer.append(prefix);
    String content = term.toMaudeString(buffer, 0).toString();
    KTreeNode node = new KTreeNode(parent, content);

    return node;
  }

  public String toKString()
  {
    buffer.setLength(0);
    return toKString(0).toString();
  }

  private StringBuilder toKString(int indent)
  {
    if (children.size() > 0)
    {
      buffer.append("<" + content + ">");
      if (children.size() > 1 || children.get(0).children.size() > 0)
      {
        for (int index = 0; index < children.size(); ++index)
        {
          buffer.append("\n");
          for (int i = 0; i <= indent; ++i)
          {
            buffer.append("  "); 
          }
          children.get(index).toKString(indent + 1);
        }
        buffer.append("\n");
        for (int i = 0; i < indent; ++i)
        {
          buffer.append("  "); 
        }
      }
      else
        children.get(0).toKString(indent + 1);
      buffer.append("<" + content + "/>");
    }
    else
      buffer.append(content);
    return buffer;
  }

}

